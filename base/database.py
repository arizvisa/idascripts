"""
Database module

This module exposes a number of tools that can be used on a database
and on addresses within the database. There are a number of namespaces
that allow one to query information about the database as a whole, or to
read/write to an address within the database.

The base argument type for many of the utilites within this module is
the address. This can allow one to modify the colors or comments for an
address, or to read/write from the different types of data that might
exist at an address.

Some namespaces are also provided for querying the available symbolic
information that IDA has discovered about a binary. This can be used
to search and navigate the database. Some of the available namespaces
that can be used for querying are ``functions``, ``segments``,
``names``, ``imports``, ``entries``, and ``marks``.
"""

import six, builtins

import functools, operator, itertools, types
import sys, os, logging, string
import math, array as _array, fnmatch, re, ctypes

import function, segment
import structure as _structure, instruction as _instruction
import ui, internal
from internal import utils, interface, exceptions as E

import idaapi

## properties
def here():
    '''Return the current address.'''
    return ui.current.address()
h = utils.alias(here)

@utils.multicase()
def within():
    '''Should always return true.'''
    return within(ui.current.address())
@utils.multicase(ea=six.integer_types)
def within(ea):
    '''Returns true if address `ea` is within the bounds of the database.'''
    left, right = config.bounds()
    return left <= ea < right
contains = utils.alias(within)

def top():
    '''Return the very lowest address within the database.'''
    ea, _ = config.bounds()
    return ea
def bottom():
    '''Return the very highest address within the database.'''
    _, ea = config.bounds()
    return ea

class config(object):
    """
    This namespace contains various read-only properties about the
    database. This includes things such as the database boundaries,
    its filename, the path to the generated database, etc. Some tools
    for determining the type of the binary are also included.
    """

    # cache the default value for the structure
    info = idaapi.get_inf_structure()

    @classmethod
    def __init_info_structure__(cls, idp_modname):
        information = idaapi.get_inf_structure()
        if information:
            logging.debug(u"{:s}.__init_info_structure__({!s}) : Successfully fetched and cached information structure for database.".format('.'.join([__name__, cls.__name__]), utils.string.escape(idp_modname, '"')))

            # Display summary of the database and what it's used for.
            bits = "{:d}-bit".format(64 if information.is_64bit() else 32 if information.is_32bit() else 16)
            format = 'library' if information.lflags & idaapi.LFLG_IS_DLL else 'binary'

            if idaapi.__version__ < 7.0:
                byteorder = "{:s}-endian".format('big' if idaapi.cvar.inf.mf else 'little')
            else:
                byteorder = "{:s}-endian".format('big' if information.lflags & idaapi.LFLG_MSF else 'little')

            if idaapi.__version__ >= 7.0:
                mode = ' kernelspace' if information.lflags & idaapi.LFLG_KERNMODE else ' userspace'
            else:
                mode = ''
            logging.warning("Initialized {tag!s} database v{version:d} for {bits:s} {byteorder:s}{mode:s} {format:s}.".format('.'.join([information.__class__.__module__, information.__class__.__name__]), tag=information.tag, bits=bits, byteorder=byteorder, mode=mode, format=format, version=information.version))

        else:
            logging.fatal(u"{:s}.__init_info_structure__({!s}) : Unknown error while trying to get information structure for database.".format('.'.join([__name__, cls.__name__]), utils.string.escape(idp_modname, '"')))
        cls.info = information

    @classmethod
    def __nw_init_info_structure__(cls, nw_code, is_old_database):
        logging.debug(u"{:s}.__nw_init_info_structure__({!s}) : Received notification to initialize information structure for database.".format('.'.join([__name__, cls.__name__]), ', '.join(map("{!r}".format, [nw_code, is_old_database]))))
        idp_modname = idaapi.get_idp_name()
        return cls.__init_info_structure__(idp_modname)

    @classmethod
    def filename(cls):
        '''Returns the filename that the database was built from.'''
        res = idaapi.get_root_filename()
        return utils.string.of(res)

    @classmethod
    def idb(cls):
        '''Return the full path to the database.'''
        res = idaapi.cvar.database_idb if idaapi.__version__ < 7.0 else idaapi.get_path(idaapi.PATH_TYPE_IDB)
        res = utils.string.of(res)
        return res.replace(os.sep, '/')

    @classmethod
    def module(cls):
        '''Return the module name as per the windows loader.'''
        res = cls.filename()
        res = os.path.split(res)
        return os.path.splitext(res[1])[0]

    @utils.multicase()
    @classmethod
    def path(cls):
        '''Return the absolute path to the directory containing the database.'''
        res = cls.idb()
        path, _ = os.path.split(res)
        return path
    @utils.multicase(pathname=six.string_types)
    @classmethod
    def path(cls, pathname, *components):
        '''Return an absolute path composed of the provided `pathname` and any additional `components` relative to the directory containing the database.'''
        res = cls.idb()
        path, _ = os.path.split(res)
        return os.path.join(path, pathname, *components)

    @classmethod
    def baseaddress(cls):
        '''Returns the baseaddress of the database.'''
        return idaapi.get_imagebase()

    @classmethod
    def readonly(cls):
        '''Returns whether the database is read-only or not.'''
        if idaapi.__version__ >= 7.0:
            return cls.info.readonly_idb()
        raise E.UnsupportedVersion(u"{:s}.readonly() : This function is only supported on versions of IDA 7.0 and newer.".format('.'.join([__name__, cls.__name__])))

    @classmethod
    def is_sharedobject(cls):
        '''Returns whether the database is a shared-object or not.'''
        if idaapi.__version__ >= 7.0:
            return True if cls.info.lflags & idaapi.LFLG_IS_DLL else False
        raise E.UnsupportedVersion(u"{:s}.is_sharedobject() : This function is only supported on versions of IDA 7.0 and newer.".format('.'.join([__name__, cls.__name__])))
    sharedobject = is_shared = sharedQ = utils.alias(is_sharedobject, 'config')

    @classmethod
    def is_kernelspace(cls):
        '''Returns whether the database is using a kernelmode address space or not.'''
        if idaapi.__version__ >= 7.0:
            return True if cls.info.lflags & idaapi.LFLG_KERNMODE else False
        raise E.UnsupportedVersion(u"{:s}.is_kernelspace() : This function is only supported on versions of IDA 7.0 and newer.".format('.'.join([__name__, cls.__name__])))
    kernelspaceQ = utils.alias(is_kernelspace, 'config')

    @classmethod
    def changes(cls):
        '''Returns the number of changes within the database.'''
        if idaapi.__version__ >= 7.0:
            return cls.info.database_change_count
        raise E.UnsupportedVersion(u"{:s}.changes() : This function is only supported on versions of IDA 7.0 and newer.".format('.'.join([__name__, cls.__name__])))

    @classmethod
    def processor(cls):
        '''Returns the name of the processor configured by the database.'''
        if idaapi.__version__ >= 7.0:
            result = cls.info.get_procName()
        elif hasattr(cls.info, 'procName'):
            result = cls.info.procName
        else:
            raise E.UnsupportedVersion(u"{:s}.processor() : This function is only supported on versions of IDA 7.0 and newer.".format('.'.join([__name__, cls.__name__])))
        return utils.string.of(result)

    @classmethod
    def compiler(cls):
        '''Returns the configured compiler for the database.'''
        return cls.info.cc
    @classmethod
    def version(cls):
        '''Returns the database version.'''
        return cls.info.version

    @classmethod
    def type(cls, typestr):
        '''Evaluates a type string and returns its size according to the compiler used by the database.'''
        lookup = {
            'bool': 'size_b',
            'short': 'size_s',
            'int': 'size_i', 'float': 'size_l', 'single': 'size_l',
            'long': 'size_l',
            'longlong': 'size_ll', 'double': 'size_ll',
            'enum': 'size_e',
            'longdouble': 'size_ldbl',
            'align': 'defalign', 'alignment': 'defalign',
        }
        string = typestr.replace(' ', '')
        return getattr(cls.compiler(), lookup.get(string.lower(), typestr.lower()))

    @classmethod
    def bits(cls):
        '''Return number of bits of the processor used by the database.'''
        if cls.info.is_64bit():
            return 64
        elif cls.info.is_32bit():
            return 32
        # Anything else seems to be 16-bit
        return 16

    @classmethod
    def byteorder(cls):
        '''Returns a string representing the byte-order used by integers in the database.'''
        if idaapi.__version__ < 7.0:
            res = idaapi.cvar.inf.mf
            return 'big' if res else 'little'
        return 'big' if cls.info.lflags & idaapi.LFLG_MSF else 'little'

    @classmethod
    def main(cls):
        return cls.info.main

    @classmethod
    def entry(cls):
        '''Return the first entry point for the database.'''
        if idaapi.__version__ < 7.0:
            return cls.info.beginEA
        return cls.info.start_ip

    @classmethod
    def margin(cls):
        '''Return the current margin position for the current database.'''
        return cls.info.margin

    @classmethod
    def bounds(cls):
        '''Return the bounds of the current database in a tuple formatted as `(left, right)`.'''
        return interface.bounds_t(cls.info.minEA, cls.info.maxEA)

    class register(object):
        """
        This namespace returns the available register names and their
        sizes for the database.
        """
        @classmethod
        def names(cls):
            '''Return all of the register names in the database.'''
            names = idaapi.ph_get_regnames()
            return [utils.string.of(item) for item in names]
        @classmethod
        def segments(cls):
            '''Return all of the segment registers in the database.'''
            sreg_first, sreg_last = (idaapi.ph_get_regFirstSreg, idaapi.ph_get_regLastSreg) if idaapi.__version__ < 7.0 else (idaapi.ph_get_reg_first_sreg, idaapi.ph_get_reg_last_sreg)

            names = cls.names()
            return [names[ri] for ri in builtins.range(sreg_first(), 1 + sreg_last())]
        @classmethod
        def codesegment(cls):
            '''Return all of the code segment registers in the database.'''
            res = idaapi.ph_get_regCodeSreg() if idaapi.__version__ < 7.0 else idaapi.ph_get_reg_code_sreg()
            return cls.names()[res]
        @classmethod
        def datasegment(cls):
            '''Return all of the data segment registers in the database.'''
            res = idaapi.ph_get_regDataSreg() if idaapi.__version__ < 7.0 else idaapi.ph_get_reg_data_sreg()
            return cls.names()[res]
        @classmethod
        def segmentbits(cls):
            '''Return the segment register size for the database.'''
            return 8 * idaapi.ph_get_segreg_size()

range = utils.alias(config.bounds, 'config')
filename, idb, module, path = utils.alias(config.filename, 'config'), utils.alias(config.idb, 'config'), utils.alias(config.module, 'config'), utils.alias(config.path, 'config')
path = utils.alias(config.path, 'config')
baseaddress = base = utils.alias(config.baseaddress, 'config')

class functions(object):
    r"""
    This namespace is used for listing all the functions inside the
    database. By default a list is returned containing the address of
    each function.

    The different types that one can match functions with are the following:

        `address` or `ea` - Match according to the function's address
        `name` - Match according to the exact name
        `like` - Filter the function names according to a glob
        `regex` - Filter the function names according to a regular-expression
        `predicate` - Filter the functions by passing their ``idaapi.func_t`` to a callable

    Some examples of how to use these keywords are as follows::

        > for ea in database.functions(): ...
        > database.functions.list('*sub*')
        > iterable = database.functions.iterate(regex='.*alloc')
        > result = database.functions.search(like='*alloc*')

    """
    __matcher__ = utils.matcher()
    __matcher__.boolean('name', lambda name, item: name.lower() == item.lower(), function.by, function.name)
    __matcher__.combinator('like', utils.fcompose(fnmatch.translate, utils.fpartial(re.compile, flags=re.IGNORECASE), operator.attrgetter('match')), function.by, function.name)
    __matcher__.combinator('regex', utils.fcompose(utils.fpartial(re.compile, flags=re.IGNORECASE), operator.attrgetter('match')), function.by, function.name)
    __matcher__.predicate('predicate', function.by)
    __matcher__.predicate('pred', function.by)
    __matcher__.boolean('address', function.contains), __matcher__.boolean('ea', function.contains)

    # chunk matching
    #__matcher__.boolean('greater', operator.le, utils.fcompose(function.chunks, functools.partial(map, builtins.list, operator.itemgetter(-1)), max)), __matcher__.boolean('gt', operator.lt, utils.fcompose(function.chunks, functools.partial(map, builtins.list, operator.itemgetter(-1)), max))
    #__matcher__.boolean('less', operator.ge, utils.fcompose(function.chunks, functools.partial(map, builtins.list, operator.itemgetter(0)), min)), __matcher__.boolean('lt', operator.gt, utils.fcompose(function.chunks, functools.partial(map, builtins.list, operator.itemgetter(0)), min))

    # entry point matching
    __matcher__.boolean('greater', operator.le, function.top), __matcher__.boolean('gt', operator.lt, function.top)
    __matcher__.boolean('less', operator.ge, function.top), __matcher__.boolean('lt', operator.gt, function.top)

    def __new__(cls):
        '''Returns a list of all of the functions in the current database.'''
        return [item for item in cls.__iterate__()]

    @utils.multicase()
    @classmethod
    def __iterate__(cls):
        '''Iterates through all of the functions in the current database (ripped from idautils).'''
        left, right = config.bounds()

        # find first function chunk
        ch = idaapi.get_fchunk(left) or idaapi.get_next_fchunk(left)
        while ch and interface.range.start(ch) < right and (ch.flags & idaapi.FUNC_TAIL) != 0:
            ui.navigation.procedure(interface.range.start(ch))
            ch = idaapi.get_next_fchunk(interface.range.start(ch))

        # iterate through the rest of the functions in the database
        while ch and interface.range.start(ch) < right:
            ui.navigation.procedure(interface.range.start(ch))
            if function.within(interface.range.start(ch)):
                yield interface.range.start(ch)
            ch = idaapi.get_next_func(interface.range.start(ch))
        return

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def iterate(cls, string):
        '''Iterate through all of the functions in the database with a glob that matches `string`.'''
        return cls.iterate(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def iterate(cls, **type):
        '''Iterate through all of the functions in the database that match the keyword specified by `type`.'''
        iterable = cls.__iterate__()
        for key, value in (type or {'predicate': utils.fconstant(True)}).items():
            iterable = cls.__matcher__.match(key, value, iterable)
        for item in iterable: yield item

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def list(cls, string):
        '''List all of the functions in the database with a glob that matches `string`.'''
        return cls.list(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def list(cls, **type):
        '''List all of the functions in the database that match the keyword specified by `type`.'''
        listable = []

        # Some utility functions for grabbing frame information
        flvars = lambda f: _structure.fragment(f.frame, 0, f.frsize) if f.frsize else []
        favars = lambda f: function.frame.args(f) if f.frsize else []

        # Set some reasonable defaults here
        maxentry = config.bounds()[0]
        maxaddr = minaddr = 0
        maxname = chunks = marks = blocks = exits = 0
        lvars = avars = 0

        # First pass through the list to grab the maximum lengths of the different fields
        for ea in cls.iterate(**type):
            func, _ = function.by(ea), ui.navigation.procedure(ea)
            maxentry = max(ea, maxentry)
            maxname = max(len(function.name(func)), maxname)

            res = [item for item in function.chunks(func)]
            maxaddr, minaddr = max(max(map(operator.itemgetter(-1), res)), maxaddr), max(max(map(operator.itemgetter(0), res)), minaddr)
            chunks = max(len(res), chunks)

            # Prior to IDA 7.0, interacting with marks forces the mark window to appear...so we'll ignore them
            marks = max(len([] if idaapi.__version__ < 7.0 else builtins.list(function.marks(func))), marks)
            blocks = max(len(builtins.list(function.blocks(func))), blocks)
            exits = max(len(builtins.list(function.bottom(func))), exits)
            lvars = max(len(builtins.list(flvars(func))) if func.frsize else lvars, lvars)
            avars = max(len(builtins.list(favars(func))) if func.frsize else avars, avars)

            listable.append(ea)

        # Collect the maximum sizes for everything from the first pass
        cindex = math.ceil(math.log(len(listable) or 1)/math.log(10)) if listable else 1
        try: cmaxoffset = math.floor(math.log(offset(maxentry)) or 1)/math.log(16)
        except: cmaxoffset = 0
        cmaxentry = math.floor(math.log(maxentry or 1)/math.log(16))
        cmaxaddr = math.floor(math.log(maxaddr or 1)/math.log(16))
        cminaddr = math.floor(math.log(minaddr or 1)/math.log(16))
        cchunks = math.floor(math.log(chunks or 1)/math.log(10)) if chunks else 1
        cblocks = math.floor(math.log(blocks or 1)/math.log(10)) if blocks else 1
        cexits = math.floor(math.log(exits or 1)/math.log(10)) if exits else 1
        cavars = math.floor(math.log(avars or 1)/math.log(10)) if avars else 1
        clvars = math.floor(math.log(lvars or 1)/math.log(10)) if lvars else 1
        cmarks = math.floor(math.log(marks or 1)/math.log(10)) if marks else 1

        # List all the fields of every single function that was matched
        for index, ea in enumerate(listable):
            func, _ = function.by(ea), ui.navigation.procedure(ea)
            res = [item for item in function.chunks(func)]
            six.print_(u"[{:>{:d}d}] {:+#0{:d}x} : {:#0{:d}x}<>{:#0{:d}x} {:s}({:d}) : {:<{:d}s} : args:{:<{:d}d} lvars:{:<{:d}d} blocks:{:<{:d}d} exits:{:<{:d}d}{:s}".format(
                index, int(cindex),
                offset(ea), int(cmaxoffset),
                min(map(operator.itemgetter(0), res)), int(cminaddr), max(map(operator.itemgetter(-1), res)), int(cmaxaddr),
                int(cchunks) * ' ', len(res),
                function.name(func), int(maxname),
                len(builtins.list(favars(func))) if func.frsize else 0, 1 + int(cavars),
                len(builtins.list(flvars(func))), 1 + int(clvars),
                len(builtins.list(function.blocks(func))), 1 + int(cblocks),
                len(builtins.list(function.bottom(func))), 1 + int(cexits),
                '' if idaapi.__version__ < 7.0 else " marks:{:<{:d}d}".format(len(builtins.list(function.marks(func))), 1 + int(cmarks))
            ))
        return

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def search(cls, string):
        '''Search through all of the functions matching the glob `string` and return the first result.'''
        return cls.search(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def search(cls, **type):
        '''Search through all of the functions within the database and return the first result matching the keyword specified by `type`.'''
        query_s = utils.string.kwargs(type)

        listable = [item for item in cls.iterate(**type)]
        if len(listable) > 1:
            messages = ((u"[{:d}] {:s}".format(i, function.name(ea))) for i, ea in enumerate(listable))
            [ logging.info(msg) for msg in messages ]
            f = utils.fcompose(function.by, function.name)
            logging.warning(u"{:s}.search({:s}) : Found {:d} matching results. Returning the first function \"{:s}\".".format('.'.join([__name__, cls.__name__]), query_s, len(listable), utils.string.escape(f(listable[0]), '"')))

        iterable = (item for item in listable)
        res = builtins.next(iterable, None)
        if res is None:
            raise E.SearchResultsError(u"{:s}.search({:s}) : Found 0 matching results.".format('.'.join([__name__, cls.__name__]), query_s))
        return res

class segments(object):
    r"""
    This namespace is used for listing all the segments inside the
    database. By default each segment's boundaries are yielded.

    The different types that one can match segments with are the following:

        `name` - Match according to the true segment name
        `like` - Filter the segment names according to a glob
        `regex` - Filter the segment names according to a regular-expression
        `index` - Match the segment by its index
        `identifier` - Match the segment by its identifier (``idaapi.segment_t.name``)
        `selector` - Match the segment by its selector (``idaapi.segment_t.sel``)
        `greater` or `gt` - Filter the segments for any after the specified address
        `less` or `lt` - Filter the segments for any before the specified address
        `predicate` - Filter the segments by passing its ``idaapi.segment_t`` to a callable

    Some examples of using these keywords are as follows::

        > for l, r in database.segments(): ...
        > database.segments.list(regex=r'\.r?data')
        > iterable = database.segments.iterate(like='*text*')
        > result = database.segments.search(greater=0x401000)

    """

    def __new__(cls):
        '''Yield the bounds of each segment within the current database.'''
        for seg in segment.__iterate__():
            yield interface.range.bounds(seg)
        return

    @utils.multicase(name=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('name')
    def list(cls, name):
        '''List all of the segments defined in the database that match the glob `name`.'''
        return cls.list(like=name)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def list(cls, **type):
        '''List all of the segments in the database that match the keyword specified by `type`.'''
        return segment.list(**type)

    @utils.multicase(name=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('name')
    def iterate(cls, name):
        '''Iterate through all of the segments in the database with a glob that matches `name`.'''
        return cls.iterate(like=name)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def iterate(cls, **type):
        '''Iterate through all the segments defined in the database matching the keyword specified by `type`.'''
        return segment.__iterate__(**type)

    @utils.multicase(name=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('name')
    def search(cls, name):
        '''Search through all of the segments matching the glob `name` and return the first result.'''
        return cls.search(like=name)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def search(cls, **type):
        '''Search through all of the segments within the database and return the first result matching the keyword specified by `type`.'''
        return segment.search(**type)

@utils.multicase()
def instruction():
    '''Return the instruction at the current address as a string.'''
    return instruction(ui.current.address())
@utils.multicase(ea=six.integer_types)
def instruction(ea):
    '''Return the instruction at the address `ea` as a string.'''
    ash = idaapi.cvar.ash if idaapi.__version__ < 7.5 else idaapi.get_ash()
    cmnt1, cmnt2 = ash.cmnt, ash.cmnt2

    # first grab the disassembly and then remove all of IDA's tag information from it
    insn = idaapi.generate_disasm_line(interface.address.inside(ea))
    unformatted = idaapi.tag_remove(insn)

    # if there's a terminating comment character, locate it, and then slice out just the comment
    if cmnt2:
        lindex = unformatted.rfind(cmnt1)
        rindex = lindex + unformatted[lindex:].find(cmnt2) + len(cmnt2)
        nocomment = unformatted if lindex < 0 else unformatted[:lindex] if rindex < 0 else (nocomment[:lindex] + nocomment[rindex:])

    # there's no terminating comment character, so we just need to cull out everything after cmnt1
    elif cmnt1:
        index = unformatted.rfind(cmnt1)
        nocomment = unformatted if index < 0 else unformatted[:index]

    # if the starting cmnt1 character isn't defined, then we don't do anything.
    else:
        nocomment = unformatted

    # combine any multiple spaces into just a single space and return it
    res = utils.string.of(nocomment.strip())
    return functools.reduce(lambda agg, char: agg + (('' if agg.endswith(' ') else ' ') if char == ' ' else char), res, '')

@utils.multicase()
def disassemble(**options):
    '''Disassemble the instructions at the current address.'''
    return disassemble(ui.current.address(), **options)
@utils.multicase(ea=six.integer_types)
def disassemble(ea, **options):
    """Disassemble the instructions at the address specified by `ea`.

    If the integer `count` is specified, then return `count` number of instructions.
    If the bool `comments` is true, then return the comments for each instruction as well.
    """
    ea = interface.address.inside(ea)
    commentQ = builtins.next((options[k] for k in ['comment', 'comments'] if k in options), False)

    # grab the values we need in order to distinguish a comment
    ash = idaapi.cvar.ash if idaapi.__version__ < 7.5 else idaapi.get_ash()
    cmnt1, cmnt2 = ash.cmnt, ash.cmnt2

    # enter a loop that goes through the number of line items requested by the user
    res, count = [], options.get('count', 1)
    while count > 0:
        # grab the instruction and remove all of IDA's tag information from it
        insn = idaapi.generate_disasm_line(ea) or ''
        unformatted = idaapi.tag_remove(insn)

        # check if the terminating char (cmnt2) is defined
        if cmnt2:
            lindex = unformatted.rfind(cmnt1)
            rindex = lindex + unformatted[lindex:].find(cmnt2) + len(cmnt2)

            # so that we can separate the comment out of it
            nocomment = unformatted if lindex < 0 else unformatted[:lindex] if rindex < 0 else (nocomment[:lindex] + nocomment[rindex:])
            comment = unformatted[lindex : lindex] if lindex < 0 else unformatted[lindex:] if rindex < 0 else comment[lindex : rindex]

        # if it's not, then just use the starting char (cmnt1) to find the comment
        elif cmnt1:
            index = unformatted.rfind(cmnt1)
            nocomment, comment = (unformatted, unformatted[index : index]) if index < 0 else (unformatted[:index], unformatted[index:])

        # if this comment is undefined, then there ain't shit we can do with it,
        # and we need to just append it as-is
        else:
            res.append(u"{:x}: {:s}".format(ea, unformatted.strip()))

        # remove any surrounding spaces from the instruction
        stripped = nocomment.strip()

        # combine all multiple spaces together so it's single-spaced
        noextraspaces = functools.reduce(lambda agg, char: agg + (('' if agg.endswith(' ') else ' ') if char == ' ' else char), utils.string.of(stripped), '')

        # if we've been asked to include the comment, then first we need to clean
        # it up a bit.
        if commentQ:
            cleaned = comment[len(cmnt1) : -len(cmnt2)] if cmnt2 else comment[len(cmnt1):]
            stripped = cleaned.strip()

            # then we can concatenate it with our instruction and its comment characters
            withcharacters = u''.join([u"{:s} ".format(cmnt1) if cmnt1 else u'', stripped, u" {:s}".format(cmnt2) if cmnt2 else u''])

            # and then we can append it to our result
            res.append(u"{:x}: {:s}{:s}".format(ea, noextraspaces, u" {:s}".format(withcharacters) if stripped else ''))

        # otherwise we cna simply append it to our result with the address in front
        else:
            res.append(u"{:x}: {:s}".format(ea, noextraspaces))

        # move on to the next iteration
        ea = address.next(ea)
        count -= 1
    return '\n'.join(res)
disasm = utils.alias(disassemble)

@utils.multicase()
def read():
    '''Return the bytes defined at the current address.'''
    res = ui.current.address()
    return read(res, type.size(res))
@utils.multicase(ea=six.integer_types)
def read(ea):
    '''Return the number of bytes associated with the address `ea`.'''
    return read(ea, type.size(ea))
@utils.multicase(ea=six.integer_types, size=six.integer_types)
def read(ea, size):
    '''Return `size` number of bytes from address `ea`.'''
    get_bytes = idaapi.get_many_bytes if idaapi.__version__ < 7.0 else idaapi.get_bytes
    start, end = interface.address.within(ea, ea + size)
    return get_bytes(ea, end - start) or b''
@utils.multicase(bounds=tuple)
def read(bounds):
    '''Return the bytes within the specified `bounds`.'''
    get_bytes = idaapi.get_many_bytes if idaapi.__version__ < 7.0 else idaapi.get_bytes
    start, end = bounds
    return get_bytes(start, end - start) or b''

@utils.multicase(data=bytes)
def write(data, **persist):
    '''Modify the database at the current address with the bytes specified in `data`.'''
    return write(ui.current.address(), data, **persist)
@utils.multicase(ea=six.integer_types, data=bytes)
def write(ea, data, **persist):
    """Modify the database at address `ea` with the bytes specified in `data`

    If the bool `persist` is specified, then modify what IDA considers the original bytes.
    """
    patch_bytes, put_bytes = (idaapi.patch_many_bytes, idaapi.put_many_bytes) if idaapi.__version__ < 7.0 else (idaapi.patch_bytes, idaapi.put_bytes)

    ea, _ = interface.address.within(ea, ea + len(data))
    originalQ = builtins.next((persist[k] for k in ['original', 'persist', 'store', 'save'] if k in persist), False)
    return patch_bytes(ea, data) if originalQ else put_bytes(ea, data)

class names(object):
    """
    This namespace is used for listing all the names (or symbols)
    within the database. By default the `(address, name)` is yielded.

    The different types that one can filter the symbols with are the following:

        `address` - Match according to the address of the symbol
        `name` - Match according to the name of the symbol
        `like` - Filter the symbol names according to a glob
        `regex` - Filter the symbol names according to a regular-expression
        `index` - Match the symbol according to its index
        `predicate` - Filter the symbols by passing their address to a callable

    Some examples of using these keywords are as follows::

        > list(database.names())
        > database.names.list(index=31)
        > iterable = database.names.iterate(like='str.*')
        > result = database.names.search(name='some_really_sick_symbol_name')

    """
    __matcher__ = utils.matcher()
    __matcher__.mapping('address', idaapi.get_nlist_ea), __matcher__.mapping('ea', idaapi.get_nlist_ea)
    __matcher__.boolean('name', lambda name, item: name.lower() == item.lower(), idaapi.get_nlist_name, utils.string.of)
    __matcher__.combinator('like', utils.fcompose(fnmatch.translate, utils.fpartial(re.compile, flags=re.IGNORECASE), operator.attrgetter('match')), idaapi.get_nlist_name, utils.string.of)
    __matcher__.combinator('regex', utils.fcompose(utils.fpartial(re.compile, flags=re.IGNORECASE), operator.attrgetter('match')), idaapi.get_nlist_name, utils.string.of)
    __matcher__.predicate('predicate', idaapi.get_nlist_ea)
    __matcher__.predicate('pred', idaapi.get_nlist_ea)
    __matcher__.attribute('index')

    def __new__(cls):
        '''Iterate through all of the names in the database yielding a tuple of the address and its name.'''
        for index in builtins.range(idaapi.get_nlist_size()):
            res = zip([idaapi.get_nlist_ea, utils.fcompose(idaapi.get_nlist_name, utils.string.of)], 2 * [index])
            yield tuple(f(x) for f, x in res)
        return

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def __iterate__(cls, string):
        return cls.__iterate__(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def __iterate__(cls, **type):
        iterable = (idx for idx in builtins.range(idaapi.get_nlist_size()))
        for key, value in (type or {'predicate': utils.fconstant(True)}).items():
            iterable = cls.__matcher__.match(key, value, iterable)
        for item in iterable: yield item

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def iterate(cls, string):
        '''Iterate through all of the names in the database with a glob that matches `string`.'''
        return cls.iterate(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def iterate(cls, **type):
        '''Iterate through all of the names in the database that match the keyword specified by `type`.'''
        for idx in cls.__iterate__(**type):
            ea, name = idaapi.get_nlist_ea(idx), idaapi.get_nlist_name(idx)
            yield ea, utils.string.of(name)
        return

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def list(cls, string):
        '''List all of the names in the database with a glob that matches `string`.'''
        return cls.list(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def list(cls, **type):
        '''List all of the names in the database that match the keyword specified by `type`.'''
        listable = []

        # Set some reasonable defaults
        maxindex = 1
        maxaddr = 0

        # Perform the first pass through our listable grabbing our field lengths
        for index in cls.__iterate__(**type):
            maxindex = max(index, maxindex)
            maxaddr = max(idaapi.get_nlist_ea(index), maxaddr)

            listable.append(index)

        # Collect the sizes from our first pass
        cindex = math.ceil(math.log(maxindex or 1)/math.log(10))
        caddr = math.floor(math.log(maxaddr or 1)/math.log(16))

        # List all the fields of each name that was found
        for index in listable:
            ea, name = idaapi.get_nlist_ea(index), idaapi.get_nlist_name(index)
            ui.navigation.set(ea)
            six.print_(u"[{:>{:d}d}] {:#0{:d}x} {:s}".format(index, int(cindex), ea, int(caddr), utils.string.of(name)))
        return

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def search(cls, string):
        '''Search through all of the names matching the glob `string` and return the first result.'''
        return cls.search(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def search(cls, **type):
        '''Search through all of the names within the database and return the first result matching the keyword specified by `type`.'''
        query_s = utils.string.kwargs(type)

        listable = [item for item in cls.__iterate__(**type)]
        if len(listable) > 1:
            f1, f2 = idaapi.get_nlist_ea, utils.fcompose(idaapi.get_nlist_name, utils.string.of)
            messages = ((u"[{:d}] {:x} {:s}".format(idx, f1(idx), f2(idx))) for idx in listable)
            [ logging.info(msg) for msg in messages ]
            logging.warning(u"{:s}.search({:s}) : Found {:d} matching results, Returning the first item at {:#x} with the name \"{:s}\".".format('.'.join([__name__, cls.__name__]), query_s, len(listable), f1(listable[0]), utils.string.escape(f2(listable[0]), '"')))

        iterable = (item for item in listable)
        res = builtins.next(iterable, None)
        if res is None:
            raise E.SearchResultsError(u"{:s}.search({:s}) : Found 0 matching results.".format('.'.join([__name__, cls.__name__]), query_s))
        return idaapi.get_nlist_ea(res)

    @utils.multicase()
    @classmethod
    def symbol(cls):
        '''Return the symbol name of the current address.'''
        return cls.symbol(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def symbol(cls, ea):
        '''Return the symbol name of the address `ea`.'''
        res = idaapi.get_nlist_idx(ea)
        return utils.string.of(idaapi.get_nlist_name(res))
    name = utils.alias(symbol, 'names')

    @classmethod
    def address(cls, index):
        '''Return the address of the symbol at `index`.'''
        return idaapi.get_nlist_ea(index)

    @utils.multicase()
    @classmethod
    def at(cls):
        '''Return the index, symbol address, and name at the current address.'''
        return cls.at(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def at(cls, ea):
        '''Return the index, symbol address, and name at the address `ea`.'''
        idx = idaapi.get_nlist_idx(ea)
        ea, name = idaapi.get_nlist_ea(idx), idaapi.get_nlist_name(idx)
        return idx, ea, utils.string.of(name)

class search(object):
    """
    This namespace used for searching the database using IDA's find
    functionality.

    By default the name is used, however there are 4 search methods
    that are available. The methods that are provided are:

        ``search.by_bytes`` - Search by the specified hex bytes
        ``search.by_regex`` - Search by the specified regex
        ``search.by_text``  - Search by the specified text
        ``search.by_name``  - Search by the specified name

    Each search method has its own options, but all of them take an extra
    boolean option, `reverse`, which specifies whether to search backwards
    from the starting position or forwards.

    The ``search.iterate`` function allows one to iterate through all the results
    discovered in the database. One variation of ``search.iterate`` takes a 3rd
    parameter `predicate`. One can provide one of the search methods provided
    or include their own. This function will then yield each matched search
    result.
    """

    @utils.multicase()
    @staticmethod
    def by_bytes(data, **direction):
        '''Search through the database at the current address for the bytes specified by `data`.'''
        return search.by_bytes(ui.current.address(), data, **direction)
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def by_bytes(ea, data, **direction):
        """Search through the database at address `ea` for the bytes specified by `data`.

        If `reverse` is specified as a bool, then search backwards from the given address.
        If `radix` is specified, then use it as the numerical radix for describing the bytes.
        If `radix` is not specified, then assume that `data` represents the exact bytes to search.
        """
        radix = direction.get('radix', 0)

        # convert the bytes directly into a string of base-10 integers
        if isinstance(data, bytes) and radix == 0:
            radix, queryF = 10, lambda string: ' '.join("{:d}".format(by) for by in bytearray(string))

        # convert the string directly into a string of base-10 integers
        elif isinstance(data, six.string_types) and radix == 0:
            radix, queryF = 10, lambda string: ' '.join(map("{:d}".format, itertools.chain(*(((ord(ch) & 0xff00) // 0x100, (ord(ch) & 0x00ff) // 0x1) for ch in string))))

        # otherwise, leave it alone because the user specified the radix already
        else:
            radix, queryF = radix or 16, utils.string.to

        reverseQ = builtins.next((direction[k] for k in ['reverse', 'reversed', 'up', 'backwards'] if k in direction), False)
        flags = idaapi.SEARCH_UP if reverseQ else idaapi.SEARCH_DOWN
        res = idaapi.find_binary(ea, idaapi.BADADDR, queryF(data), radix, idaapi.SEARCH_CASE | flags)
        if res == idaapi.BADADDR:
            raise E.SearchResultsError(u"{:s}.by_bytes({:#x}, \"{:s}\"{:s}) : The specified bytes were not found.".format('.'.join([__name__, search.__name__]), ea, utils.string.escape(data, '"'), u", {:s}".format(utils.string.kwargs(direction)) if direction else '', res))
        return res
    bybytes = utils.alias(by_bytes, 'search')

    @utils.multicase(string=six.string_types)
    @staticmethod
    @utils.string.decorate_arguments('string')
    def by_regex(string, **options):
        '''Search through the database at the current address for the regex matched by `string`.'''
        return search.by_regex(ui.current.address(), string, **options)
    @utils.multicase(ea=six.integer_types, string=six.string_types)
    @staticmethod
    @utils.string.decorate_arguments('string')
    def by_regex(ea, string, **options):
        """Search the database at address `ea` for the regex matched by `string`.

        If `reverse` is specified as a bool, then search backwards from the given address.
        If `sensitive` is specified as bool, then perform a case-sensitive search.
        """
        queryF = utils.string.to

        reverseQ = builtins.next((options[k] for k in ['reverse', 'reversed', 'up', 'backwards'] if k in options), False)
        flags = idaapi.SEARCH_REGEX
        flags |= idaapi.SEARCH_UP if reverseQ else idaapi.SEARCH_DOWN
        flags |= idaapi.SEARCH_CASE if options.get('sensitive', False) else 0
        res = idaapi.find_text(ea, 0, 0, queryF(string), flags)
        if res == idaapi.BADADDR:
            raise E.SearchResultsError(u"{:s}.by_regex({:#x}, \"{:s}\"{:s}) : The specified regex was not found.".format('.'.join([__name__, search.__name__]), ea, utils.string.escape(string, '"'), u", {:s}".format(utils.string.kwargs(options)) if options else '', res))
        return res
    byregex = utils.alias(by_regex, 'search')

    @utils.multicase(string=six.string_types)
    @staticmethod
    @utils.string.decorate_arguments('string')
    def by_text(string, **options):
        '''Search through the database at the current address for the text matched by `string`.'''
        return search.by_text(ui.current.address(), string, **options)
    @utils.multicase(ea=six.integer_types, string=six.string_types)
    @staticmethod
    @utils.string.decorate_arguments('string')
    def by_text(ea, string, **options):
        """Search the database at address `ea` for the text matched by `string`.

        If `reverse` is specified as a bool, then search backwards from the given address.
        If `sensitive` is specified as bool, then perform a case-sensitive search.
        """
        queryF = utils.string.to

        reverseQ = builtins.next((options[k] for k in ['reverse', 'reversed', 'up', 'backwards'] if k in options), False)
        flags = 0
        flags |= idaapi.SEARCH_UP if reverseQ else idaapi.SEARCH_DOWN
        flags |= idaapi.SEARCH_CASE if options.get('sensitive', False) else 0
        res = idaapi.find_text(ea, 0, 0, queryF(string), flags)
        if res == idaapi.BADADDR:
            raise E.SearchResultsError(u"{:s}.by_text({:#x}, \"{:s}\"{:s}) : The specified text was not found.".format('.'.join([__name__, search.__name__]), ea, utils.string.escape(string, '"'), u", {:s}".format(utils.string.kwargs(options)) if options else '', res))
        return res
    bytext = by_string = bystring = utils.alias(by_text, 'search')

    @utils.multicase(name=six.string_types)
    @staticmethod
    @utils.string.decorate_arguments('name')
    def by_name(name, **options):
        '''Search through the database at the current address for the symbol `name`.'''
        return search.by_name(ui.current.address(), name, **options)
    @utils.multicase(ea=six.integer_types, name=six.string_types)
    @staticmethod
    @utils.string.decorate_arguments('name')
    def by_name(ea, name, **options):
        """Search through the database at address `ea` for the symbol `name`.

        If `reverse` is specified as a bool, then search backwards from the given address.
        If `sensitive` is specified as bool, then perform a case-sensitive search.
        """
        queryF = utils.string.to

        reverseQ = builtins.next((options[k] for k in ['reverse', 'reversed', 'up', 'backwards'] if k in options), False)
        flags = idaapi.SEARCH_IDENT
        flags |= idaapi.SEARCH_UP if reverseQ else idaapi.SEARCH_DOWN
        flags |= idaapi.SEARCH_CASE if options.get('sensitive', False) else 0
        res = idaapi.find_text(ea, 0, 0, queryF(name), flags)
        if res == idaapi.BADADDR:
            raise E.SearchResultsError(u"{:s}.by_name({:#x}, \"{:s}\"{:s}) : The specified name was not found.".format('.'.join([__name__, search.__name__]), ea, utils.string.escape(name, '"'), u", {:s}".format(utils.string.kwargs(options)) if options else '', res))
        return res
    byname = utils.alias(by_name, 'search')

    @utils.multicase()
    @classmethod
    def iterate(cls, data, **options):
        '''Iterate through all search results that match the bytes `data` starting at the current address.'''
        predicate = options.pop('predicate', cls.by_bytes)
        return cls.iterate(ui.current.address(), data, predicate, **options)
    @utils.multicase(predicate=callable)
    @classmethod
    def iterate(cls, data, predicate, **options):
        '''Iterate through all search results matched by the function `predicate` with the specified `data` starting at the current address.'''
        return cls.iterate(ui.current.address(), data, predicate, **options)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def iterate(cls, ea, data, **options):
        '''Iterate through all search results that match the bytes `data` starting at address `ea`.'''
        predicate = options.pop('predicate', cls.by_bytes)
        return cls.iterate(ea, data, predicate, **options)
    @utils.multicase(ea=six.integer_types, predicate=callable)
    @classmethod
    def iterate(cls, ea, data, predicate, **options):
        '''Iterate through all search results matched by the function `predicate` with the specified `data` starting at address `ea`.'''
        ea = predicate(ea, data, **options)
        try:
            while ea != idaapi.BADADDR:
                yield ea
                ea = predicate(address.next(ea), data)
        except E.SearchResultsError:
            return
        return

    @utils.multicase()
    def __new__(cls, data, **direction):
        '''Search through the database at the current address for the bytes specified by `data`.'''
        return cls.by_bytes(ui.current.address(), data, **direction)
    @utils.multicase(ea=six.integer_types)
    def __new__(cls, ea, data, **direction):
        """Search through the database at address `ea` for the bytes specified by `data`.

        If `reverse` is specified as a bool, then search backwards from the given address.
        If `radix` is specified, then use it as the numerical radix for describing the bytes.
        If `radix` is not specified, then assume that `data` represents the exact bytes to search.
        """
        return cls.by_bytes(ea, data, **direction)

byname = by_name = utils.alias(search.by_name, 'search')

def go(ea):
    '''Jump to the specified address at `ea`.'''
    if isinstance(ea, six.string_types):
        ea = search.by_name(None, ea)
    idaapi.jumpto(interface.address.inside(ea))
    return ea

def go_offset(offset):
    '''Jump to the specified `offset` within the database.'''
    res, ea = address.offset(ui.current.address()), address.by_offset(offset)
    idaapi.jumpto(interface.address.inside(ea))
    return res
goof = gooffset = gotooffset = goto_offset = utils.alias(go_offset)

@utils.multicase()
def name(**flags):
    '''Returns the name at the current address.'''
    return name(ui.current.address(), **flags)
@utils.multicase(ea=six.integer_types)
def name(ea, **flags):
    """Return the name defined at the address specified by `ea`.

    If `flags` is specified, then use the specified value as the flags.
    """
    ea = interface.address.inside(ea)

    # figure out what default flags to use
    fn = idaapi.get_func(ea)

    # figure out which name function to call
    if idaapi.__version__ < 6.8:
        # if get_true_name is going to return the function's name instead of a real one, then leave it as unnamed.
        if fn and interface.range.start(fn) == ea and not flags:
            return None

        aname = idaapi.get_true_name(ea) or idaapi.get_true_name(ea, ea)
    else:
        aname = idaapi.get_ea_name(ea, flags.get('flags', idaapi.GN_LOCAL))

    # return the name at the specified address or not
    return utils.string.of(aname) or None
@utils.multicase(string=six.string_types)
@utils.string.decorate_arguments('string', 'suffix')
def name(string, *suffix, **flags):
    '''Renames the current address to `string`.'''
    return name(ui.current.address(), string, *suffix, **flags)
@utils.multicase(none=None.__class__)
def name(none, **flags):
    '''Removes the name at the current address.'''
    return name(ui.current.address(), none or '', **flags)
@utils.multicase(ea=six.integer_types, string=six.string_types)
@utils.string.decorate_arguments('string', 'suffix')
def name(ea, string, *suffix, **flags):
    """Renames the address specified by `ea` to `string`.

    If `ea` is pointing to a global and is not contained by a function, then by default the label will be added to the Names list.
    If `flags` is specified, then use the specified value as the flags.
    If the boolean `listed` is specified, then specify whether to add the label to the Names list or not.
    """
    # combine name with its suffix
    res = (string,) + suffix
    string = interface.tuplename(*res)

    # validate the address, and get the original flags
    ea = interface.address.inside(ea)
    ofl = type.flags(ea)

    ## define some closures that perform the different tasks necessary to
    ## apply a name to a given address
    def apply_name(ea, string, flag):
        '''Apply the given ``string`` to the address ``ea`` with the specified ``flag``.'''

        # convert the specified string into a form that IDA can handle
        ida_string = utils.string.to(string)

        # validate the name
        res = idaapi.validate_name2(ida_string[:]) if idaapi.__version__ < 7.0 else idaapi.validate_name(ida_string[:], idaapi.VNT_VISIBLE)
        if ida_string and ida_string != res:
            logging.info(u"{:s}.name({:#x}, \"{:s}\"{:s}) : Stripping invalid chars from specified name resulted in \"{:s}\".".format(__name__, ea, utils.string.escape(string, '"'), u", {:s}".format(utils.string.kwargs(flags)) if flags else '', utils.string.escape(utils.string.of(res), '"')))
            ida_string = res

        # set the name and use the value of 'flag' if it was explicit
        res, ok = name(ea), idaapi.set_name(ea, ida_string or "", flag)

        if not ok:
            raise E.DisassemblerError(u"{:s}.name({:#x}, \"{:s}\"{:s}) : Unable to call `idaapi.set_name({:#x}, \"{:s}\", {:#x})`.".format(__name__, ea, utils.string.escape(string, '"'), u", {:s}".format(utils.string.kwargs(flags)) if flags else '', ea, utils.string.escape(string, '"'), flag))
        return res

    def name_within(ea, string, flag):
        '''Add or rename a label named ``string`` at the address ``ea`` with the specified ``flags``.'''
        func, realname, localname = idaapi.get_func(ea), idaapi.get_visible_name(ea), idaapi.get_visible_name(ea, idaapi.GN_LOCAL)

        # if there's a public name at this address then use the flag to determine
        # how to update the public name.
        if idaapi.is_public_name(ea) or any(flag & item for item in [idaapi.SN_PUBLIC, idaapi.SN_NON_PUBLIC]):
            flag |= idaapi.SN_PUBLIC if flag & idaapi.SN_PUBLIC else idaapi.SN_NON_PUBLIC

        # if we're pointing to the start of the function, then unless public was explicitly
        # specified we need to set the local name.
        elif interface.range.start(func) == ea and not builtins.all(flag & item for item in [idaapi.SN_PUBLIC, idaapi.SN_NON_PUBLIC]):
            flag |= idaapi.SN_LOCAL

        # if the name is supposed to be in the list, then we need to check if there's a
        # local name.
        elif not flag & idaapi.SN_NOLIST:
            if localname and realname != localname:
                idaapi.del_local_name(ea), idaapi.set_name(ea, localname, idaapi.SN_NOLIST)
            flag &= ~idaapi.SN_LOCAL

        # if a regular name is defined, but not a local one, then we need to set the local
        # one first.
        elif realname and realname == localname:
            flag |= idaapi.SN_NOLIST

        # otherwise we're using a local name because we're inside a function.
        else:
            flag |= idaapi.SN_LOCAL

        # now we can apply the name with the flags that we determined.
        return apply_name(ea, string, flag)

    def name_outside(ea, string, flag):
        '''Add or rename a global named ``string`` at the address ``ea`` with the specified ``flags``.'''
        realname, localname = idaapi.get_visible_name(ea), idaapi.get_visible_name(ea, idaapi.GN_LOCAL)

        # preserve the name if its public
        flag |= idaapi.SN_PUBLIC if idaapi.is_public_name(ea) else idaapi.SN_NON_PUBLIC

        # if 'listed' wasn't explicitly specified then ensure it's not listed as requested.
        if 'listed' not in flags:
            flag |= idaapi.SN_NOLIST

        # then finally apply the name.
        return apply_name(ea, string, flag)

    ## now we can define the actual logic for naming the given address
    flag = idaapi.SN_NON_AUTO
    flag |= idaapi.SN_NOCHECK

    # preserve any flags that were previously applied
    flag |= 0 if idaapi.is_in_nlist(ea) else idaapi.SN_NOLIST
    flag |= idaapi.SN_WEAK if idaapi.is_public_name(ea) and idaapi.is_weak_name(ea) else idaapi.SN_NON_WEAK

    # if the bool `listed` is True, then ensure that it's added to the name list.
    if 'listed' in flags:
        flag = (flag & ~idaapi.SN_NOLIST) if flags.get('listed', False) else (flag | idaapi.SN_NOLIST)

    # if custom flags were specified, then just use those as they should get
    # priority
    if 'flags' in flags:
        return apply_name(ea, string, flags['flags'])

    # if we're within a function, then use the name_within closure to apply the name
    elif function.within(ea):
        return name_within(ea, string, flag)

    # otherwise, we use the name_without closure to apply it
    return name_outside(ea, string, flag)
@utils.multicase(ea=six.integer_types, none=None.__class__)
def name(ea, none, **flags):
    '''Removes the name defined at the address `ea`.'''
    return name(ea, none or '', **flags)

@utils.multicase()
def color():
    '''Return the rgb color at the current address.'''
    return color(ui.current.address())
@utils.multicase(none=None.__class__)
def color(none):
    '''Remove the color from the current address.'''
    return color(ui.current.address(), None)
@utils.multicase(ea=six.integer_types)
def color(ea):
    '''Return the rgb color at the address `ea`.'''
    res = idaapi.get_item_color(interface.address.inside(ea))
    b, r = (res&0xff0000)>>16, res&0x0000ff
    return None if res == 0xffffffff else (r<<16)|(res&0x00ff00)|b
@utils.multicase(ea=six.integer_types, none=None.__class__)
def color(ea, none):
    '''Remove the color at the address `ea`.'''
    return idaapi.set_item_color(interface.address.inside(ea), 0xffffffff)
@utils.multicase(ea=six.integer_types, rgb=six.integer_types)
def color(ea, rgb):
    '''Set the color at address `ea` to `rgb`.'''
    r, b = (rgb&0xff0000) >> 16, rgb&0x0000ff
    return idaapi.set_item_color(interface.address.inside(ea), (b<<16)|(rgb&0x00ff00)|r)

@utils.multicase()
def comment(**repeatable):
    '''Return the comment at the current address.'''
    return comment(ui.current.address(), **repeatable)
@utils.multicase(ea=six.integer_types)
def comment(ea, **repeatable):
    """Return the comment at the address `ea`.

    If the bool `repeatable` is specified, then return the repeatable comment.
    """
    res = idaapi.get_cmt(interface.address.inside(ea), repeatable.get('repeatable', False))

    # return the string in a format the user can process
    return utils.string.of(res)
@utils.multicase(string=six.string_types)
@utils.string.decorate_arguments('string')
def comment(string, **repeatable):
    '''Set the comment at the current address to `string`.'''
    return comment(ui.current.address(), string, **repeatable)
@utils.multicase(none=None.__class__)
def comment(none, **repeatable):
    '''Remove the comment at the current address.'''
    return comment(ui.current.address(), none or '', **repeatable)
@utils.multicase(ea=six.integer_types, string=six.string_types)
@utils.string.decorate_arguments('string')
def comment(ea, string, **repeatable):
    """Set the comment at the address `ea` to `string`.

    If the bool `repeatable` is specified, then modify the repeatable comment.
    """
    # apply the comment to the specified address
    res, ok = comment(ea, **repeatable), idaapi.set_cmt(interface.address.inside(ea), utils.string.to(string), repeatable.get('repeatable', False))
    if not ok:
        raise E.DisassemblerError(u"{:s}.comment({:#x}, {!r}{:s}) : Unable to call `idaapi.set_cmt({:#x}, \"{:s}\", {!s})`.".format(__name__, ea, string, u", {:s}".format(utils.string.kwargs(repeatable)) if repeatable else '', ea, utils.string.escape(string, '"'), repeatable.get('repeatable', False)))
    return res
@utils.multicase(ea=six.integer_types, none=None.__class__)
def comment(ea, none, **repeatable):
    """Remove the comment at the address `ea`.

    If the bool `repeatable` is specified, then remove the repeatable comment.
    """
    return comment(ea, none or '', **repeatable)

class entries(object):
    """
    This namespace can be used to enumerate all of the entry points and
    exports that are defined within the database By default the address
    of each entrypoint will be yielded.

    This namespace is also aliased as ``database.exports``.

    The different types that one can match entrypoints with are the following:

        `address` or `ea` - Match according to the entrypoint's address
        `name` - Match according to the exact name
        `like` - Filter the entrypoint names according to a glob
        `regex` - Filter the entrypoint names according to a regular-expression
        `index` - Match according to the entrypoint's index (ordinal)
        `greater` or `ge` - Filter the entrypoints for any after the specified address (inclusive)
        `gt` - Filter the entrypoints for any after the specified address (exclusive)
        `less` or `le` - Filter the entrypoints for any before the specified address (inclusive)
        `lt` - Filter the entrypoints for any before the specified address (exclusive)
        `predicate` - Filter the entrypoints by passing its index (ordinal) to a callable

    Some examples of using these keywords are as follows::

        > database.entries.list(greater=h())
        > iterable = database.entries.iterate(like='Nt*')
        > result = database.entries.search(index=0)

    """

    __matcher__ = utils.matcher()
    __matcher__.mapping('address', utils.fcompose(idaapi.get_entry_ordinal, idaapi.get_entry))
    __matcher__.mapping('ea', utils.fcompose(idaapi.get_entry_ordinal, idaapi.get_entry))
    __matcher__.boolean('greater', operator.le, idaapi.get_entry_ordinal, idaapi.get_entry)
    __matcher__.boolean('ge', operator.le, idaapi.get_entry_ordinal, idaapi.get_entry)
    __matcher__.boolean('gt', operator.lt, idaapi.get_entry_ordinal, idaapi.get_entry)
    __matcher__.boolean('less', operator.ge, idaapi.get_entry_ordinal, idaapi.get_entry)
    __matcher__.boolean('le', operator.ge, idaapi.get_entry_ordinal, idaapi.get_entry)
    __matcher__.boolean('lt', operator.gt, idaapi.get_entry_ordinal, idaapi.get_entry)
    __matcher__.boolean('name', lambda name, item: name.lower() == item.lower(), idaapi.get_entry_ordinal, idaapi.get_entry_name, utils.string.of)
    __matcher__.combinator('like', utils.fcompose(fnmatch.translate, utils.fpartial(re.compile, flags=re.IGNORECASE), operator.attrgetter('match')), idaapi.get_entry_ordinal, idaapi.get_entry_name, utils.string.of)
    __matcher__.combinator('regex', utils.fcompose(utils.fpartial(re.compile, flags=re.IGNORECASE), operator.attrgetter('match')), idaapi.get_entry_ordinal, idaapi.get_entry_name, utils.string.of)
    __matcher__.predicate('predicate', idaapi.get_entry_ordinal)
    __matcher__.predicate('pred', idaapi.get_entry_ordinal)
    __matcher__.boolean('index', operator.eq)

    def __new__(cls):
        '''Yield the address of each entry point defined within the database.'''
        for ea in cls.iterate():
            yield ea
        return

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def __iterate__(cls, string):
        return cls.__iterate__(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def __iterate__(cls, **type):
        listable = builtins.range(idaapi.get_entry_qty())
        for key, value in (type or {'predicate': utils.fconstant(True)}).items():
            listable = [item for item in cls.__matcher__.match(key, value, listable)]
        for item in listable: yield item

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def iterate(cls, string):
        '''Iterate through all of the entry points in the database with a glob that matches `string`.'''
        return cls.iterate(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def iterate(cls, **type):
        '''Iterate through all of the entry points in the database that match the keyword specified by `type`.'''
        for ea in cls.__iterate__(**type):
            yield cls.__address__(ea)
        return

    @classmethod
    def __index__(cls, ea):
        '''Returns the index of the entry point at the specified `address`.'''
        f = utils.fcompose(idaapi.get_entry_ordinal, idaapi.get_entry)

        # Iterate through each entry point, and yield a tuple containing its address and index.
        Ftransform = utils.fcompose(utils.fmap(f, lambda item: item), builtins.tuple)
        iterable = (Ftransform(item) for item in builtins.range(idaapi.get_entry_qty()))

        # Iterate through each (address, index) looking for the matching address.
        Fcrit = utils.fcompose(utils.first, functools.partial(operator.eq, ea))
        filterable = (item for item in iterable if Fcrit(item))

        # Return the index of the address that matched.
        iterable = (utils.second(item) for item in filterable)
        return builtins.next(iterable, None)

    @classmethod
    def __address__(cls, index):
        '''Returns the address of the entry point at the specified `index`.'''
        res = cls.__entryordinal__(index)
        res = idaapi.get_entry(res)
        return None if res == idaapi.BADADDR else res

    # Returns the name of the entry point at the specified `index`.
    __entryname__ = staticmethod(utils.fcompose(idaapi.get_entry_ordinal, idaapi.get_entry_name, utils.string.of))
    # Returns the ordinal of the entry point at the specified `index`.
    __entryordinal__ = staticmethod(idaapi.get_entry_ordinal)

    @utils.multicase()
    @classmethod
    def ordinal(cls):
        '''Returns the ordinal of the entry point at the current address.'''
        return cls.ordinal(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def ordinal(cls, ea):
        '''Returns the ordinal of the entry point at the address `ea`.'''
        res = cls.__index__(ea)
        if res is not None:
            return cls.__entryordinal__(res)
        raise E.MissingTypeOrAttribute(u"{:s}.ordinal({:#x}) : No entry point at specified address.".format('.'.join([__name__, cls.__name__]), ea))

    @utils.multicase()
    @classmethod
    def name(cls):
        '''Returns the name of the entry point at the current address.'''
        return cls.name(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def name(cls, ea):
        '''Returns the name of the entry point at the address `ea`.'''
        res = cls.__index__(ea)
        if res is not None:
            return cls.__entryname__(res)
        raise E.MissingTypeOrAttribute(u"{:s}.name({:#x}) : No entry point at specified address.".format('.'.join([__name__, cls.__name__]), ea))

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def list(cls, string):
        '''List all of the entry points matching the glob `string` against the name.'''
        return cls.list(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def list(cls, **type):
        '''List all of the entry points in the database that match the keyword specified by `type`.'''
        listable = []

        # Set some reasonable defaults
        maxindex = maxaddr = maxordinal = 0

        # First pass through our listable grabbing the maximum lengths of our fields
        for index in cls.__iterate__(**type):
            maxindex = max(index, maxindex)

            res = idaapi.get_entry_ordinal(index)
            maxaddr = max(idaapi.get_entry(res), maxaddr)
            maxordinal = max(res, maxordinal)

            listable.append(index)

        # Collect the maximum sizes for everything from the first pass
        cindex = math.ceil(math.log(maxindex or 1)/math.log(10))
        caddr = math.ceil(math.log(maxaddr or 1)/math.log(16))
        cordinal = math.ceil(math.log(maxordinal or 1)/math.log(16))

        # List all the fields from everything that matched
        for index in listable:
            ordinal = cls.__entryordinal__(index)
            ea = idaapi.get_entry(ordinal)
            six.print_(u"[{:{:d}d}] {:<#{:d}x} : {:s}{:s}".format(index, int(cindex), ea, 2 + int(caddr), '' if ea == ordinal else "({:#{:d}x}) ".format(ordinal, 2 + int(cindex)), cls.__entryname__(index)))
        return

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def search(cls, string):
        '''Search through all of the entry point names matching the glob `string` and return the first result.'''
        return cls.search(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'like', 'regex')
    def search(cls, **type):
        '''Search through all of the entry points within the database and return the first result matching the keyword specified by `type`.'''
        query_s = utils.string.kwargs(type)

        listable = [item for item in cls.__iterate__(**type)]
        if len(listable) > 1:
            messages = ((u"[{:d}] {:x} : ({:x}) {:s}".format(idx, cls.__address__(idx), cls.__entryordinal__(idx), cls.__entryname__(idx))) for idx in listable)
            [ logging.info(msg) for msg in messages ]
            f = utils.fcompose(idaapi.get_entry_ordinal, idaapi.get_entry)
            logging.warning(u"{:s}.search({:s}) : Found {:d} matching results, Returning the first entry point at {:#x}.".format('.'.join([__name__, cls.__name__]), query_s, len(listable), f(listable[0])))

        iterable = (item for item in listable)
        res = builtins.next(iterable, None)
        if res is None:
            raise E.SearchResultsError(u"{:s}.search({:s}) : Found 0 matching results.".format('.'.join([__name__, cls.__name__]), query_s))
        return cls.__address__(res)

    @utils.multicase()
    @classmethod
    def new(cls):
        '''Makes an entry point at the current address.'''
        ea, entryname, ordinal = ui.current.address(), name(ui.current.address()) or function.name(ui.current.address()), idaapi.get_entry_qty()
        if entryname is None:
            raise E.MissingTypeOrAttribute(u"{:s}.new({:#x}) : Unable to determine name at address.".format( '.'.join([__name__, cls.__name__]), ea))
        return cls.new(ea, entryname, ordinal)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def new(cls, ea):
        '''Makes an entry point at the specified address `ea`.'''
        entryname, ordinal = name(ea) or function.name(ea), idaapi.get_entry_qty()
        if entryname is None:
            raise E.MissingTypeOrAttribute(u"{:s}.new({:#x}) : Unable to determine name at address.".format( '.'.join([__name__, cls.__name__]), ea))
        return cls.new(ea, entryname, ordinal)
    @utils.multicase(name=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('name')
    def new(cls, name):
        '''Adds the current address as an entry point using `name` and the next available index as the ordinal.'''
        return cls.new(ui.current.address(), name, idaapi.get_entry_qty())
    @utils.multicase(ea=six.integer_types, name=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('name')
    def new(cls, ea, name):
        '''Makes the specified address `ea` an entry point having the specified `name`.'''
        ordinal = idaapi.get_entry_qty()
        return cls.new(ea, name, ordinal)
    @utils.multicase(name=six.string_types, ordinal=six.integer_types)
    @classmethod
    @utils.string.decorate_arguments('name')
    def new(cls, name, ordinal):
        '''Adds an entry point with the specified `name` to the database using `ordinal` as its index.'''
        return cls.new(ui.current.address(), name, ordinal)
    @utils.multicase(ea=six.integer_types, name=six.string_types, ordinal=six.integer_types)
    @classmethod
    @utils.string.decorate_arguments('name')
    def new(cls, ea, name, ordinal):
        '''Adds an entry point at `ea` with the specified `name` and `ordinal`.'''
        res = idaapi.add_entry(ordinal, interface.address.inside(ea), utils.string.to(name), 0)
        ui.state.wait()
        return res

    add = utils.alias(new, 'entries')
exports = entries     # XXX: ns alias

def tags():
    '''Returns all of the tag names used globally.'''
    return internal.comment.globals.name()

@utils.multicase()
def tag():
    '''Return all of the tags defined at the current address.'''
    return tag(ui.current.address())
@utils.multicase(ea=six.integer_types)
def tag(ea):
    '''Return all of the tags defined at address `ea`.'''
    ea = interface.address.inside(ea)

    # if not within a function, then use a repeatable comment
    # otherwise, use a non-repeatable one. if our address is
    # pointing to a runtime-linked function, then we actually
    # need to switch the comment type that we're fetching from.
    try:
        func = function.by_address(ea)
        rt, _ = interface.addressOfRuntimeOrStatic(func)
    except E.FunctionNotFoundError:
        rt, func = False, None
    repeatable = False if func and function.within(ea) and not rt else True

    # fetch the tags from the repeatable and non-repeatable comment at the given address
    res = comment(ea, repeatable=False)
    d1 = internal.comment.decode(res)
    res = comment(ea, repeatable=True)
    d2 = internal.comment.decode(res)
    res = function.comment(ea, repeatable=True) if rt else ''
    d3 = internal.comment.decode(res)

    # check to see if they're not overwriting each other
    if six.viewkeys(d1) & six.viewkeys(d2):
        logging.info(u"{:s}.tag({:#x}) : Contents of both the repeatable and non-repeatable comment conflict with one another due to using the same keys ({:s}). Giving the {:s} comment priority.".format(__name__, ea, ', '.join(six.viewkeys(d1) & six.viewkeys(d2)), 'repeatable' if repeatable else 'non-repeatable'))
    if rt and (six.viewkeys(d3) & six.viewkeys(d1) or six.viewkeys(d3) & six.viewkeys(d2)):
        logging.info(u"{:s}.tag({:#x}) : Contents of the runtime-linked comment conflict with one of the database comments due to using the same keys ({:s}). Giving the {:s} comment priority.".format(__name__, ea, ', '.join(six.viewkeys(d3) & six.viewkeys(d2) or six.viewkeys(d3) & six.viewkeys(d1)), 'function'))

    # construct a dictionary that gives priority to repeatable if outside a
    # function and non-repeatable if inside. if the address points to a
    # runtime function, then those tags will get absolute priority.
    res = {}
    [res.update(d) for d in ([d1, d2] if repeatable else [d2, d1])]
    rt and res.update(d3)

    # modify the decoded dictionary with any implicit tags
    aname = name(ea)
    if aname and type.flags(ea, idaapi.FF_NAME): res.setdefault('__name__', aname)

    eprefix = extra.__get_prefix__(ea)
    if eprefix is not None: res.setdefault('__extra_prefix__', eprefix)

    esuffix = extra.__get_suffix__(ea)
    if esuffix is not None: res.setdefault('__extra_suffix__', esuffix)

    col = color(ea)
    if col is not None: res.setdefault('__color__', col)

    # if there's some typeinfo then we need to figure out its name so we can
    # format it.
    try:
        if type.has_typeinfo(ea):
            ti = type(ea)

            # Demangle just the name if it's mangled in some way, and use it to render
            # the typeinfo to return.
            realname = internal.declaration.unmangle_name(aname)
            ti_s = idaapi.print_tinfo('', 0, 0, 0, ti, utils.string.to(realname), '')

            # Add it to our dictionary that we return to the user.
            res.setdefault('__typeinfo__', ti_s)

    # if we caught an exception, then this name might be mangled and we can just rip
    # our type information directly from the name.
    except E.InvalidTypeOrValueError:
        demangled = internal.declaration.demangle(aname)

        # if the demangled name is different from the actual name, then we need
        # to extract its result type and prepend it to the demangled name.
        if demangled != aname:
            res.setdefault('__typeinfo__', demangled)

    # now return what the user cares about
    return res
@utils.multicase(key=six.string_types)
@utils.string.decorate_arguments('key')
def tag(key):
    '''Return the tag identified by `key` at the current address.'''
    return tag(ui.current.address(), key)
@utils.multicase(key=six.string_types)
@utils.string.decorate_arguments('key', 'value')
def tag(key, value):
    '''Set the tag identified by `key` to `value` at the current address.'''
    return tag(ui.current.address(), key, value)
@utils.multicase(ea=six.integer_types, key=six.string_types)
@utils.string.decorate_arguments('key')
def tag(ea, key):
    '''Returns the tag identified by `key` from address `ea`.'''
    res = tag(ea)
    if key in res:
        return res[key]
    raise E.MissingTagError(u"{:s}.tag({:#x}, {!r}) : Unable to read tag \"{:s}\" from address.".format(__name__, ea, key, utils.string.escape(key, '"')))
@utils.multicase(ea=six.integer_types, key=six.string_types)
@utils.string.decorate_arguments('key', 'value')
def tag(ea, key, value):
    '''Set the tag identified by `key` to `value` at the address `ea`.'''
    if value is None:
        raise E.InvalidParameterError(u"{:s}.tag({:#x}, {!r}, {!r}) : Tried to set tag \"{:s}\" to an invalid value {!r}.".format(__name__, ea, key, value, utils.string.escape(key, '"'), value))

    # if an implicit tag was specified, then dispatch to the correct handler
    if key == '__name__':
        return name(ea, value, listed=True)
    if key == '__extra_prefix__':
        return extra.__set_prefix__(ea, value)
    if key == '__extra_suffix__':
        return extra.__set_suffix__(ea, value)
    if key == '__color__':
        return color(ea, value)
    if key == '__typeinfo__':
        return type(ea, value)

    # if we're not within a function, then we need to use a repeatable comment
    # unless we're in a runtime-linked function. this is because for some reason
    # IDA uses function-comments for these.
    try:
        func = function.by_address(ea)
        rt, _ = interface.addressOfRuntimeOrStatic(func)
    except E.FunctionNotFoundError:
        rt, func = False, None
    repeatable = False if func and function.within(ea) and not rt else True

    # figure out which comment type the specified tag was encoded into. if it's
    # in neither, then choose the comment type based on what we determined with
    # the repeatable variable. we need to do special handling for runtime-linked
    # functions because IDA uses repeatable function comments for some reason.
    ea = interface.address.inside(ea)
    state_correct = internal.comment.decode(comment(ea, repeatable=repeatable))
    state_wrong = internal.comment.decode(comment(ea, repeatable=not repeatable))
    state_runtime = internal.comment.decode(function.comment(ea, repeatable=True)) if func else {}
    if rt:
        rt, state, where = (True, state_runtime, True) if key in state_runtime else (False, state_wrong, False) if key in state_wrong else (True, state_runtime, True)
    else:
        state, where = (state_correct, repeatable) if key in state_correct else (state_wrong, not repeatable) if key in state_wrong else (state_correct, repeatable)

    # update the tag's reference if we're actually adding the user's key and not
    # overwriting it. tags for runtime-linked functions are actually globals, so
    # that's also necessary to include in our tests.
    if key not in state:
        if func and function.within(ea) and not rt:
            internal.comment.contents.inc(ea, key)
        else:
            internal.comment.globals.inc(ea, key)

    # grab the previous value, and update the state with the new one so that we
    # can return this to the user.
    res, state[key] = state.get(key, None), value

    # now we're ready to do our updates, but we need to guard the modification
    # so that we don't mistakenly tamper with any references we updated. again,
    # due to IDA using repeatable function comments for runtime-linked addresses,
    # we need to check rt in order to determine which comment type to use.
    hooks = {'changing_cmt', 'cmt_changed', 'changing_range_cmt', 'range_cmt_changed', 'changing_area_cmt', 'area_cmt_changed'} & ui.hook.idb.available
    try:
        [ ui.hook.idb.disable(item) for item in hooks ]
    except Exception:
        raise
    else:
        function.comment(ea, internal.comment.encode(state), repeatable=where) if rt else comment(ea, internal.comment.encode(state), repeatable=where)
    finally:
        [ ui.hook.idb.enable(item) for item in hooks ]

    # we can now return what the user asked for.
    return res
@utils.multicase(key=six.string_types, none=None.__class__)
def tag(key, none):
    '''Remove the tag identified by `key` from the current address.'''
    return tag(ui.current.address(), key, none)
@utils.multicase(ea=six.integer_types, key=six.string_types, none=None.__class__)
@utils.string.decorate_arguments('key')
def tag(ea, key, none):
    '''Removes the tag identified by `key` at the address `ea`.'''
    ea = interface.address.inside(ea)

    # if the '__name__' is being cleared, then really remove it.
    if key == '__name__':
        return name(ea, None, listed=True)
    if key == '__extra_prefix__':
        return extra.__delete_prefix__(ea)
    if key == '__extra_suffix__':
        return extra.__delete_suffix__(ea)
    if key == '__typeinfo__':
        return type(ea, None)
    if key == '__color__':
        return color(ea, None)

    # if not within a function, then fetch the repeatable comment otherwise update the non-repeatable one
    try:
        func = function.by_address(ea)
        rt, _ = interface.addressOfRuntimeOrStatic(func)
    except E.FunctionNotFoundError:
        rt, func = False, None
    repeatable = False if func and function.within(ea) and not rt else True

    # figure out which comment type the user's key is in so that we can remove
    # that one. if we're a runtime-linked address, then we need to remove the
    # tag from a repeatable function comment. if the tag isn't in any of them,
    # then it doesn't really matter since we're going to raise an exception anyways.
    state_correct = internal.comment.decode(comment(ea, repeatable=repeatable))
    state_wrong = internal.comment.decode(comment(ea, repeatable=not repeatable))
    state_runtime = internal.comment.decode(function.comment(ea, repeatable=True)) if func else {}
    if rt:
        rt, state, where = (True, state_runtime, True) if key in state_runtime else (False, state_wrong, False) if key in state_wrong else (True, state_runtime, True)
    else:
        state, where = (state_correct, repeatable) if key in state_correct else (state_wrong, not repeatable) if key in state_wrong else (state_correct, repeatable)

    if key not in state:
        raise E.MissingTagError(u"{:s}.tag({:#x}, {!r}, {!s}) : Unable to remove non-existent tag \"{:s}\" from address.".format(__name__, ea, key, none, utils.string.escape(key, '"')))
    res = state.pop(key)

    # now we can do our update, but we still need to guard the modification so
    # that we don't accidentally tamper with any references that are updated.
    hooks = {'changing_cmt', 'cmt_changed', 'changing_range_cmt', 'range_cmt_changed', 'changing_area_cmt', 'area_cmt_changed'} & ui.hook.idb.available
    try:
        [ ui.hook.idb.disable(item) for item in hooks ]
    except Exception:
        raise
    else:
        function.comment(ea, internal.comment.encode(state), repeatable=where) if rt else comment(ea, internal.comment.encode(state), repeatable=where)
    finally:
        [ ui.hook.idb.enable(item) for item in hooks ]

    # delete its reference since it's been removed from the dict. if
    # it's a runtime-linked function, then we ensure that only the
    # global reference is messed with.
    if func and function.within(ea) and not rt:
        internal.comment.contents.dec(ea, key)
    else:
        internal.comment.globals.dec(ea, key)

    # return the previous value back to the user because we're nice
    return res

# FIXME: consolidate the boolean querying logic into the utils module
# FIXME: document this properly
# FIXME: add support for searching global tags using the addressing cache
@utils.multicase(tag=six.string_types)
@utils.string.decorate_arguments('And', 'Or')
def select(tag, *And, **boolean):
    '''Query all of the global tags in the database for the specified `tag` and any others specified as `And`.'''
    res = {tag} | {item for item in And}
    boolean['And'] = {item for item in boolean.get('And', [])} | res
    return select(**boolean)
@utils.multicase()
@utils.string.decorate_arguments('And', 'Or')
def select(**boolean):
    """Query all the global tags for any tags specified by `boolean`. Yields each address found along with the matching tags as a dictionary.

    If `And` contains an iterable then require the returned address contains them.
    If `Or` contains an iterable then include any other tags that are specified.
    """
    containers = (builtins.tuple, builtins.set, builtins.list)
    boolean = {key : {item for item in value} if isinstance(value, containers) else {value} for key, value in boolean.items()}

    # nothing specific was queried, so just yield all the tags
    if not boolean:
        for ea in internal.comment.globals.address():
            ui.navigation.set(ea)
            res = function.tag(ea) if function.within(ea) else tag(ea)
            if res: yield ea, res
        return

    # collect the keys to query as specified by the user
    Or, And = ({item for item in boolean.get(B, [])} for B in ['Or', 'And'])

    # walk through all tags so we can cross-check them with the query
    for ea in internal.comment.globals.address():
        ui.navigation.set(ea)
        res, d = {}, function.tag(ea) if function.within(ea) else tag(ea)

        # Or(|) includes any tags that were queried
        res.update({key : value for key, value in d.items() if key in Or})

        # And(&) includes any tags that match all of the queried tagnames
        if And:
            if And & six.viewkeys(d) == And:
                res.update({key : value for key, value in d.items() if key in And})
            else: continue

        # if anything matched, then yield the address and the queried tags
        if res: yield ea, res
    return

# FIXME: consolidate the boolean querying logic into the utils module
# FIXME: document this properly
@utils.multicase(tag=six.string_types)
@utils.string.decorate_arguments('tag', 'And', 'Or')
def selectcontents(tag, *Or, **boolean):
    '''Query all function contents for the specified `tag` or any others specified as `Or`.'''
    res = {tag} | {item for item in Or}
    boolean['Or'] = {item for item in boolean.get('Or', [])} | res
    return selectcontents(**boolean)
@utils.multicase()
@utils.string.decorate_arguments('And', 'Or')
def selectcontents(**boolean):
    """Query all function contents for any tags specified by `boolean`. Yields each function and the tags that match as a set.

    If `And` contains an iterable then require the returned function contains them.
    If `Or` contains an iterable then include any other tags that are specified.
    """
    containers = (builtins.tuple, builtins.set, builtins.list)
    boolean = {key : {item for item in value} if isinstance(value, containers) else {value} for key, value in boolean.items()}

    # nothing specific was queried, so just yield all tagnames
    if not boolean:
        for ea, _ in internal.comment.contents.iterate():
            ui.navigation.procedure(ea)
            res = internal.comment.contents.name(ea)
            if res: yield ea, res
        return

    # collect the keys to query as specified by the user
    Or, And = ({item for item in boolean.get(B, [])} for B in ['Or', 'And'])

    # walk through all tagnames so we can cross-check them against the query
    for ea, res in internal.comment.contents.iterate():
        ui.navigation.procedure(ea)
        res, d = {item for item in res}, internal.comment.contents._read(None, ea) or {}

        # check to see that the dict's keys match
        if {key for key in d} != res:
            # FIXME: include query in warning
            q = utils.string.kwargs(boolean)
            logging.warning(u"{:s}.selectcontents({:s}) : Contents cache is out of sync. Using contents blob at {:#x} instead of the sup cache.".format(__name__, q, ea))

        # now start aggregating the keys that the user is looking for
        res, d = {item for item in []}, internal.comment.contents.name(ea)

        # Or(|) includes any of the tagnames being queried
        res.update(Or & d)

        # And(&) includes tags only if they include all of the specified tagnames
        if And:
            if And & d == And:
                res.update(And)
            else: continue

        # if any tags matched, then yield the address and the results
        if res: yield ea, res
    return
selectcontent = utils.alias(selectcontents)

## imports
class imports(object):
    """
    This namespace is used for listing all of the imports within the
    database. Each import is represented by an address along with any
    naming information that is required to dynamically link external
    symbols with the binary.

    By default a tuple is yielded for each import with the format
    `(address, (shared-object, name, hint))`. In this tuple,
    `shared-object` represents the name of the shared object the
    import is imported from. The `name` is the symbol name to link
    with, and `hint` is the import ordinal hint which is used to speed
    up the linking process.

    The different types that one can match imports with are the following:

        `address` or `ea` - Match according to the import's address
        `name` - Match according to the import's symbol name
        `module` - Filter the imports according to the specified module name
        `fullname` - Match according to the full symbol name (module + symbol)
        `like` - Filter the symbol names of all the imports according to a glob
        `regex` - Filter the symbol names of all the imports according to a regular-expression
        `ordinal` - Match according to the import's hint (ordinal)
        `index` - Match according index of the import
        `predicate` Filter the imports by passing the above (default) tuple to a callable

    Some examples of using these keywords are as follows::

        > database.imports.list(module='kernelbase.dll')
        > iterable = database.imports.iterate(like='*alloc*')
        > result = database.imports.search(index=42)

    """
    def __new__(cls):
        return cls.__iterate__()

    @staticmethod
    def __symbol__(module_name_ordinal):
        module, name, ordinal = module_name_ordinal

        # FIXME: I believe this is a windows-only scheme...
        name = name or u"Ordinal{:d}".format(ordinal)

        # FIXME: I think this is a gnu-only thing...
        if module is None and '@@' in name:
            nestname, nestmodule = name.rsplit('@@', 1)
            return utils.string.of(nestmodule), utils.string.of(nestname)
        return utils.string.of(module), utils.string.of(name)

    @staticmethod
    def __formats__(module_name_ordinal):
        _, name = imports.__symbol__(module_name_ordinal)
        return name
    @staticmethod
    def __formatl__(module_name_ordinal):
        module, name = imports.__symbol__(module_name_ordinal)
        # FIXME: use "`" instead of "!" when analyzing an OSX fat binary
        return u"{:s}!{:s}".format(module, name)

    __format__ = __formatl__

    __matcher__ = utils.matcher()
    __matcher__.mapping('address', utils.first), __matcher__.mapping('ea', utils.first)
    __matcher__.boolean('name', lambda name, item: name.lower() == item.lower(), utils.second, __formats__.__func__)
    __matcher__.combinator('fullname', utils.fcompose(fnmatch.translate, utils.fpartial(re.compile, flags=re.IGNORECASE), operator.attrgetter('match')), utils.second, __formatl__.__func__)
    __matcher__.combinator('like', utils.fcompose(fnmatch.translate, utils.fpartial(re.compile, flags=re.IGNORECASE), operator.attrgetter('match')), utils.second, __formats__.__func__)
    __matcher__.combinator('module', utils.fcompose(fnmatch.translate, utils.fpartial(re.compile, flags=re.IGNORECASE), operator.attrgetter('match')), utils.second, utils.first)
    __matcher__.mapping('ordinal', utils.fcompose(utils.second, utils.funbox(lambda module, name, ordinal: ordinal)))
    __matcher__.combinator('regex', utils.fcompose(utils.fpartial(re.compile, flags=re.IGNORECASE), operator.attrgetter('match')), utils.second, __format__.__func__)
    __matcher__.predicate('predicate', lambda item: item)
    __matcher__.predicate('pred', lambda item: item)
    __matcher__.mapping('index', utils.first)

    @classmethod
    def __iterate__(cls):
        """Iterate through all of the imports in the database.

        Yields `(address, (module, name, ordinal))` for each iteration.
        """
        for idx in builtins.range(idaapi.get_import_module_qty()):
            module = idaapi.get_import_module_name(idx)
            listable = []
            idaapi.enum_import_names(idx, utils.fcompose(utils.fbox, listable.append, utils.fconstant(True)))
            for ea, name, ordinal in listable:
                ui.navigation.set(ea)
                realmodule, realname = cls.__symbol__((module, name, ordinal))
                yield ea, (utils.string.of(realmodule), utils.string.of(realname), ordinal)
            continue
        return

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def iterate(cls, string):
        '''Iterate through all of the imports in the database with a glob that matches `string`.'''
        return cls.iterate(like=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'module', 'fullname', 'like', 'regex')
    def iterate(cls, **type):
        '''Iterate through all of the imports in the database that match the keyword specified by `type`.'''
        iterable = cls.__iterate__()
        for key, value in (type or {'predicate': utils.fconstant(True)}).items():
            iterable = (item for item in cls.__matcher__.match(key, value, iterable))
        for item in iterable: yield item

    # searching
    @utils.multicase()
    @classmethod
    def at(cls):
        '''Returns the import at the current address.'''
        return cls.at(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def at(cls, ea):
        '''Return the import at the address `ea`.'''
        ea = interface.address.inside(ea)
        Fcrit = utils.fcompose(utils.first, functools.partial(operator.eq, ea))
        iterable = (item for item in cls.__iterate__() if Fcrit(item))
        try:
            return utils.second(builtins.next(iterable))
        except StopIteration:
            pass
        raise E.MissingTypeOrAttribute(u"{:s}.at({:#x}) : Unable to determine import at specified address.".format('.'.join([__name__, cls.__name__]), ea))

    @utils.multicase()
    @classmethod
    def module(cls):
        '''Return the import module at the current address.'''
        return cls.module(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def module(cls, ea):
        '''Return the import module at the specified address `ea`.'''
        ea = interface.address.inside(ea)
        for addr, (module, _, _) in cls.__iterate__():
            if addr == ea:
                return module
            continue
        raise E.MissingTypeOrAttribute(u"{:s}.module({:#x}) : Unable to determine import module name at specified address.".format('.'.join([__name__, cls.__name__]), ea))

    # specific parts of the import
    @utils.multicase()
    @classmethod
    def fullname(cls):
        '''Return the full name of the import at the current address.'''
        return cls.fullname(ui.current.address())
    @utils.multicase()
    @classmethod
    def fullname(cls, ea):
        '''Return the full name of the import at address `ea`.'''
        return cls.__formatl__(cls.at(ea))

    @utils.multicase()
    @classmethod
    def name(cls):
        '''Return the name of the import at the current address.'''
        return cls.name(ui.current.address())
    @utils.multicase()
    @classmethod
    def name(cls, ea):
        '''Return the name of the import at address `ea`.'''
        return cls.__formats__(cls.at(ea))

    @utils.multicase()
    @classmethod
    def ordinal(cls):
        '''Return the ordinal of the import at the current address.'''
        return cls.ordinal(ui.current.address())
    @utils.multicase()
    @classmethod
    def ordinal(cls, ea):
        '''Return the ordinal of the import at the address `ea`.'''
        _, _, ordinal = cls.at(ea)
        return ordinal

    # FIXME: maybe implement a modules class for getting information on import modules
    @classmethod
    def modules(cls):
        '''Return all of the import modules defined in the database.'''
        iterable = (module for _, (module, _, _) in cls.__iterate__())
        settable = {item for item in iterable if item}
        return [utils.string.of(item) for item in settable]

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def list(cls, string):
        '''List all of the imports matching the glob `string` against the fullname.'''
        return cls.list(fullname=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'module', 'fullname', 'like', 'regex')
    def list(cls, **type):
        '''List all of the imports in the database that match the keyword specified by `type`.'''
        listable = []

        # Set some reasonable defaults
        maxaddr = maxmodule = cordinal = 0
        has_ordinal = False

        # Perform the first pass through our listable grabbing our field lengths
        for ea, (module, name, ordinal) in cls.iterate(**type):
            maxaddr = max(ea, maxaddr)
            maxmodule = max(len(module or ''), maxmodule)
            cordinal = max(len("{:d}".format(ordinal)), cordinal)
            has_ordinal = has_ordinal or ordinal > 0

            listable.append((ea, (module, name, ordinal)))

        # Collect the maximum sizes for the lengths from the first pass
        caddr = math.floor(math.log(maxaddr or 1)/math.log(16))

        # List all the fields of every import that was matched
        for ea, (module, name, ordinal) in listable:
            ui.navigation.set(ea)
            moduleordinal = "{:s}{:s}".format(module or '', "<{:d}>".format(ordinal) if has_ordinal else '')
            six.print_(u"{:<#0{:d}x} : {:s}{:s}".format(ea, 2 + int(caddr), "{:>{:d}s} ".format(moduleordinal, maxmodule + cordinal) if module else ' ' * (1 + maxmodule + cordinal), name))
        return

    @utils.multicase(string=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('string')
    def search(cls, string):
        '''Search through all of the imports matching the fullname glob `string`.'''
        return cls.search(fullname=string)
    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('name', 'module', 'fullname', 'like', 'regex')
    def search(cls, **type):
        '''Search through all of the imports within the database and return the first result matching the keyword specified by `type`.'''
        query_s = utils.string.kwargs(type)

        listable = [item for item in cls.iterate(**type)]
        if len(listable) > 1:
            messages = (u"{:x} {:s}<{:d}> {:s}".format(ea, module, ordinal, name) for ea, (module, name, ordinal) in listable)
            [ logging.info(msg) for msg in messages ]
            f = utils.fcompose(utils.second, cls.__formatl__)
            logging.warning(u"{:s}.search({:s}) : Found {:d} matching results. Returning the first import \"{:s}\".".format('.'.join([__name__, cls.__name__]), query_s, len(listable), utils.string.escape(f(listable[0]), '"')))

        iterable = (item for item in listable)
        res = builtins.next(iterable, None)
        if res is None:
            raise E.SearchResultsError(u"{:s}.search({:s}) : Found 0 matching results.".format('.'.join([__name__, cls.__name__]), query_s))
        return res[0]

###
class address(object):
    """
    This namespace is used for translating an address in the database
    to another address according to a number of constraints or types.
    Essentially these functions are used to assist with navigation.
    As an example, these functions allow one to navigate between the
    next and previous "call" instructions, addresses that contain
    data references, or even to navigate to unknown (undefined)
    addresses.

    This namespace is also aliased as ``database.a``.

    Some of the more common functions are used so often that they're also
    aliased as globals. Each of these can be used for navigation or for
    determining the next valid address. These are:

        ``database.next`` - Return the "next" defined address
        ``database.prev`` - Return the "previous" defined address
        ``database.nextref`` - Return the "next" address with a reference.
        ``database.prevref`` - Return the "previous" address with a reference
        ``database.nextreg`` - Return the "next" address using a register
        ``database.prevreg`` - Return the "previous" address using a register

    Some examples of using this namespace can be::

        > ea = database.a.next(ea)
        > ea = database.a.prevreg(ea, 'edx', write=1)
        > ea = database.a.nextref(ea)
        > ea = database.a.prevcall(ea)

    """

    # FIXME
    # The methods in this namespace should be put into a utils class. This way
    # each of these operations can be exposed to the user in function.chunks,
    # function.block, etc. Most of these functions only need to know their
    # searching boundaries, and so we should derive from that logic for our class.

    @utils.multicase()
    def __new__(cls):
        '''Return the address of the current address.'''
        return cls.head(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    def __new__(cls, ea):
        '''Return the address of the item containing the address `ea`.'''
        return cls.head(ea)

    @utils.multicase()
    @classmethod
    def bounds(cls):
        '''Return the bounds of the current address in a tuple formatted as `(left, right)`.'''
        return cls.bounds(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def bounds(cls, ea):
        '''Return the bounds of the specified address `ea` in a tuple formatted as `(left, right)`.'''
        return interface.bounds_t(ea, ea + type.size(ea))

    @staticmethod
    def __walk__(ea, next, match):
        '''Return the first address from `ea` using `next` for stepping until the provided callable doesn't `match`.'''
        res = interface.address.inside(ea)
        while res not in {None, idaapi.BADADDR} and match(res):
            res = next(res)
        return res

    @utils.multicase(end=six.integer_types)
    @classmethod
    def iterate(cls, end):
        '''Iterate from the current address to `end`.'''
        return cls.iterate(ui.current.address(), end)
    @utils.multicase(end=six.integer_types, step=callable)
    @classmethod
    def iterate(cls, end, step):
        '''Iterate from the current address to `end` using the callable `step` to determine the next address.'''
        return cls.iterate(ui.current.address(), end, step)
    @utils.multicase(start=six.integer_types, end=six.integer_types)
    @classmethod
    def iterate(cls, start, end):
        '''Iterate from address `start` to `end`.'''
        start, end = interface.address.within(start, end)
        step = cls.prev if start > end else cls.next
        return cls.iterate(start, end, step)
    @utils.multicase(start=six.integer_types, end=six.integer_types, step=callable)
    @classmethod
    def iterate(cls, start, end, step):
        '''Iterate from address `start` to `end` using the callable `step` to determine the next address.'''
        start, end = interface.address.inside(start, end)
        left, right = config.bounds()

        if start == end: return
        op = operator.lt if start < end else operator.ge

        try:
            res = start
            while res not in {idaapi.BADADDR, None} and left <= res < right and op(res, end):
                yield res
                res = step(res)
        except E.OutOfBoundsError: pass
    @utils.multicase(bounds=tuple)
    @classmethod
    def iterate(cls, bounds):
        '''Iterate through all of the addresses defined within `bounds`.'''
        left, right = bounds
        return cls.iterate(left, cls.prev(right))
    @utils.multicase(bounds=tuple, step=callable)
    @classmethod
    def iterate(cls, bounds, step):
        '''Iterate through all of the addresses defined within `bounds` using the callable `step` to determine the next address.'''
        left, right = bounds
        return cls.iterate(left, cls.prev(right), step)

    @classmethod
    @utils.multicase(end=six.integer_types)
    def blocks(cls, end):
        '''Yields the boundaries of each block from the current address to `end`.'''
        return cls.blocks(ui.current.address(), end)
    @classmethod
    @utils.multicase(bounds=tuple)
    def blocks(cls, bounds):
        '''Yields the boundaries of each block within the specified `bounds`.'''
        left, right = bounds
        return cls.blocks(left, right)
    @classmethod
    @utils.multicase(start=six.integer_types, end=six.integer_types)
    def blocks(cls, start, end):
        '''Yields the boundaries of each block between the addresses `start` and `end`.'''
        block, _ = start, end = interface.address.head(start), address.tail(end) + 1
        for ea in cls.iterate(start, end):
            nextea = cls.next(ea)

            ## XXX: it seems that idaapi.is_basic_block_end requires the following to be called
            # idaapi.decode_insn(insn, ea)
            ## XXX: for some reason is_basic_block_end will occasionally include some stray 'call' instructions
            # if idaapi.is_basic_block_end(ea):
            #     yield block, nextea
            ## XXX: in later versions of ida, is_basic_block_end takes two args (ea, bool call_insn_stops_block)

            # skip call instructions
            if _instruction.type.is_call(ea):
                continue

            # halting instructions terminate a block
            if _instruction.type.is_return(ea):
                yield block, nextea
                block = ea

            # branch instructions will terminate a block
            elif cxdown(ea):
                yield block, nextea
                block = nextea

            # a branch target will also terminate a block
            elif cxup(ea) and block != ea:
                yield block, ea
                block = ea
            continue
        return

    @utils.multicase()
    @classmethod
    def head(cls):
        '''Return the address of the byte at the beginning of the current address.'''
        return cls.head(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def head(cls, ea):
        '''Return the address of the byte at the beginning of the address `ea`.'''
        ea = interface.address.within(ea)
        return idaapi.get_item_head(ea)

    @utils.multicase()
    @classmethod
    def tail(cls):
        '''Return the last byte at the end of the current address.'''
        return cls.tail(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def tail(cls, ea):
        '''Return the address of the last byte at the end of the address at `ea`.'''
        ea = interface.address.within(ea)
        return idaapi.get_item_end(ea)-1

    @utils.multicase()
    @classmethod
    def prev(cls):
        '''Return the previous address from the current address.'''
        return cls.prev(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def prev(cls, predicate):
        '''Return the previous address from the current address that matches `predicate`.'''
        return cls.prev(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def prev(cls, ea):
        '''Return the previous address from the address specified by `ea`.'''
        return cls.prev(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def prev(cls, ea, predicate):
        '''Return the previous address from the address `ea` that matches `predicate`.'''
        return cls.prevF(ea, predicate, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def prev(cls, ea, count):
        '''Return the previous `count` addresses from the address specified by `ea`.'''
        return cls.prevF(ea, utils.fidentity, count)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable, count=six.integer_types)
    @classmethod
    def prev(cls, ea, predicate, count):
        """Return the previous address from the address `ea` that matches `predicate`.

        Skip `count` addresses before returning.
        """
        return cls.prevF(ea, predicate, count)

    @utils.multicase()
    @classmethod
    def next(cls):
        '''Return the next address from the current address.'''
        return cls.next(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def next(cls, predicate):
        '''Return the next address from the current address that matches `predicate`.'''
        return cls.next(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def next(cls, ea):
        '''Return the next address from the address `ea`.'''
        return cls.next(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def next(cls, ea, predicate):
        '''Return the next address from the address `ea` that matches `predicate`.'''
        return cls.nextF(ea, predicate, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def next(cls, ea, count):
        '''Return the next `count` addresses from the address specified by `ea`.'''
        return cls.nextF(ea, utils.fidentity, count)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable, count=six.integer_types)
    @classmethod
    def next(cls, ea, predicate, count):
        """Return the next address from the address `ea` that matches `predicate`.

        Skip `count` addresses before returning.
        """
        return cls.nextF(ea, predicate, count)

    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def prevF(cls, predicate):
        '''Return the previous address from the current one that matches `predicate`.'''
        return cls.prevF(ui.current.address(), predicate, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def prevF(cls, ea, predicate):
        '''Return the previous address from the address `ea`. that matches `predicate`.'''
        return cls.prevF(ea, predicate, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable, count=six.integer_types)
    @classmethod
    def prevF(cls, ea, predicate, count):
        """Return the previous address from the address `ea` that matches `predicate`.

        Skip `count` addresses before returning.
        """
        Fprev, Finverse = utils.fcompose(interface.address.within, idaapi.prev_not_tail), utils.fcompose(predicate, operator.not_)

        # if we're at the very bottom address of the database
        # then skip the ``interface.address.within`` check.
        if ea == config.bounds()[1]:
            Fprev = idaapi.prev_not_tail

        if Fprev(ea) == idaapi.BADADDR:
            raise E.AddressOutOfBoundsError(u"{:s}.prevF: Refusing to seek past the top of the database ({:#x}). Stopped at address {:#x}.".format('.'.join([__name__, cls.__name__]), config.bounds()[0], ea))

        res = cls.__walk__(Fprev(ea), Fprev, Finverse)
        return cls.prevF(res, predicate, count-1) if count > 1 else res

    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def nextF(cls, predicate):
        '''Return the next address from the current one that matches `predicate`.'''
        return cls.nextF(ui.current.address(), predicate, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def nextF(cls, ea, predicate):
        '''Return the next address from the address `ea`. that matches `predicate`.'''
        return cls.nextF(ea, predicate, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable, count=six.integer_types)
    @classmethod
    def nextF(cls, ea, predicate, count):
        """Return the next address from the address `ea` that matches `predicate`..

        Skip `count` addresses before returning.
        """
        Fnext, Finverse = utils.fcompose(interface.address.within, idaapi.next_not_tail), utils.fcompose(predicate, operator.not_)
        if Fnext(ea) == idaapi.BADADDR:
            raise E.AddressOutOfBoundsError(u"{:s}.nextF: Refusing to seek past the bottom of the database ({:#x}). Stopped at address {:#x}.".format('.'.join([__name__, cls.__name__]), config.bounds()[1], idaapi.get_item_end(ea)))
        res = cls.__walk__(Fnext(ea), Fnext, Finverse)
        return cls.nextF(res, predicate, count-1) if count > 1 else res

    @utils.multicase()
    @classmethod
    def prevref(cls):
        '''Returns the previous address that has anything referencing it.'''
        return cls.prevref(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def prevref(cls, predicate):
        '''Returns the previous address that has anything referencing it and matches `predicate`.'''
        return cls.prevref(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def prevref(cls, ea):
        '''Returns the previous address from `ea` that has anything referencing it.'''
        return cls.prevref(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def prevref(cls, ea, predicate):
        '''Returns the previous address from `ea` that has anything referencing it and matches `predicate`.'''
        Fxref = utils.fcompose(xref.up, len, functools.partial(operator.lt, 0))
        F = utils.fcompose(utils.fmap(Fxref, predicate), builtins.all)
        return cls.prevF(ea, F, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def prevref(cls, ea, count):
        '''Returns the previous `count` addresses from `ea` that has anything referencing it.'''
        Fxref = utils.fcompose(xref.up, len, functools.partial(operator.lt, 0))
        return cls.prevF(ea, Fxref, count)

    @utils.multicase()
    @classmethod
    def nextref(cls):
        '''Returns the next address that has anything referencing it.'''
        return cls.nextref(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def nextref(cls, predicate):
        '''Returns the next address that has anything referencing it and matches `predicate`.'''
        return cls.nextref(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def nextref(cls, ea):
        '''Returns the next address from `ea` that has anything referencing it.'''
        return cls.nextref(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def nextref(cls, ea, predicate):
        '''Returns the next address from `ea` that has anything referencing it and matches `predicate`.'''
        Fxref = utils.fcompose(xref.up, len, functools.partial(operator.lt, 0))
        F = utils.fcompose(utils.fmap(Fxref, predicate), builtins.all)
        return cls.nextF(ea, Fxref, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def nextref(cls, ea, count):
        '''Returns the next `count` addresses from `ea` that has anything referencing it.'''
        Fxref = utils.fcompose(xref.up, len, functools.partial(operator.lt, 0))
        return cls.nextF(ea, Fxref, count)

    @utils.multicase()
    @classmethod
    def prevdref(cls):
        '''Returns the previous address that has data referencing it.'''
        return cls.prevdref(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def prevdref(cls, predicate):
        '''Returns the previous address that has data referencing it and matches `predicate`.'''
        return cls.prevdref(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def prevdref(cls, ea):
        '''Returns the previous address from `ea` that has data referencing it.'''
        return cls.prevdref(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def prevdref(cls, ea, predicate):
        '''Returns the previous address from `ea` that has data referencing it and matches `predicate`.'''
        Fdref = utils.fcompose(xref.data_up, len, functools.partial(operator.lt, 0))
        F = utils.fcompose(utils.fmap(Fdref, predicate), builtins.all)
        return cls.prevF(ea, F, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def prevdref(cls, ea, count):
        '''Returns the previous `count` addresses from `ea` that has data referencing it.'''
        Fdref = utils.fcompose(xref.data_up, len, functools.partial(operator.lt, 0))
        return cls.prevF(ea, Fdref, count)

    @utils.multicase()
    @classmethod
    def nextdref(cls):
        '''Returns the next address that has data referencing it.'''
        return cls.nextdref(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def nextdref(cls, predicate):
        '''Returns the next address that has data referencing it and matches `predicate`.'''
        return cls.nextdref(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def nextdref(cls, ea):
        '''Returns the next address from `ea` that has data referencing it.'''
        return cls.nextdref(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def nextdref(cls, ea, predicate):
        '''Returns the next address from `ea` that has data referencing it and matches `predicate`.'''
        Fdref = utils.fcompose(xref.data_up, len, functools.partial(operator.lt, 0))
        F = utils.fcompose(utils.fmap(Fdref, predicate), builtins.all)
        return cls.nextF(ea, F, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def nextdref(cls, ea, count):
        '''Returns the next `count` addresses from `ea` that has data referencing it.'''
        Fdref = utils.fcompose(xref.data_up, len, functools.partial(operator.lt, 0))
        return cls.nextF(ea, Fdref, count)
    prevdata, nextdata = utils.alias(prevdref, 'address'), utils.alias(nextdref, 'address')

    @utils.multicase()
    @classmethod
    def prevcref(cls):
        '''Returns the previous address that has code referencing it.'''
        return cls.prevcref(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def prevcref(cls, predicate):
        '''Returns the previous address that has code referencing it and matches `predicate`.'''
        return cls.prevcref(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def prevcref(cls, ea):
        '''Returns the previous address from `ea` that has code referencing it.'''
        return cls.prevcref(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def prevcref(cls, ea, predicate):
        '''Returns the previous address from `ea` that has code referencing it and matches `predicate`.'''
        Fcref = utils.fcompose(xref.code_up, len, functools.partial(operator.lt, 0))
        F = utils.fcompose(utils.fmap(Fcref, predicate), builtins.all)
        return cls.prevF(ea, Fcref, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def prevcref(cls, ea, count):
        '''Returns the previous `count` addresses from `ea` that has code referencing it.'''
        Fcref = utils.fcompose(xref.code_up, len, functools.partial(operator.lt, 0))
        return cls.prevF(ea, Fcref, count)

    @utils.multicase()
    @classmethod
    def nextcref(cls):
        '''Returns the next address that has code referencing it.'''
        return cls.nextcref(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def nextcref(cls, predicate):
        '''Returns the next address that has code referencing it and matches `predicate`.'''
        return cls.nextcref(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def nextcref(cls, ea):
        '''Returns the next address from `ea` that has code referencing it.'''
        return cls.nextcref(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def nextcref(cls, ea, predicate):
        '''Returns the next address from `ea` that has code referencing it and matches `predicate`.'''
        Fcref = utils.fcompose(xref.code_up, len, functools.partial(operator.lt, 0))
        F = utils.fcompose(utils.fmap(Fcref, predicate), builtins.all)
        return cls.nextF(ea, Fcref, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def nextcref(cls, ea, count):
        '''Returns the next `count` addresses from `ea` that has code referencing it.'''
        Fcref = utils.fcompose(xref.code_up, len, functools.partial(operator.lt, 0))
        return cls.nextF(ea, Fcref, count)
    prevcode, nextcode = utils.alias(prevcref, 'address'), utils.alias(nextcref, 'address')

    @utils.multicase(reg=(six.string_types, interface.register_t))
    @classmethod
    def prevreg(cls, reg, *regs, **modifiers):
        '''Return the previous address containing an instruction that uses `reg` or any one of the specified registers `regs`.'''
        return cls.prevreg(ui.current.address(), reg, *regs, **modifiers)
    @utils.multicase(predicate=builtins.callable, reg=(six.string_types, interface.register_t))
    @classmethod
    def prevreg(cls, predicate, reg, *regs, **modifiers):
        '''Return the previous address containing an instruction that uses `reg` or any one of the specified registers `regs` and matches `predicate`.'''
        return cls.prevreg(ui.current.address(), predicate, reg, *regs, **modifiers)
    @utils.multicase(ea=six.integer_types, reg=(six.string_types, interface.register_t))
    @classmethod
    def prevreg(cls, ea, reg, *regs, **modifiers):
        '''Return the previous address from `ea` containing an instruction that uses `reg` or any one of the specified registers `regs`.'''
        return cls.prevreg(ea, utils.fconst(True), reg, *regs, **modifiers)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable, reg=(six.string_types, interface.register_t))
    @classmethod
    def prevreg(cls, ea, predicate, reg, *regs, **modifiers):
        '''Return the previous address from `ea` containing an instruction that uses `reg` or any one of the specified registers `regs` and matches `predicate`.'''
        regs = (reg,) + regs
        count = modifiers.get('count', 1)
        args = u', '.join(["{:x}".format(ea)] + ["{!r}".format(predicate)] + ["\"{:s}\"".format(utils.string.escape(str(reg), '"')) for reg in regs])
        args = args + (u", {:s}".format(utils.string.kwargs(modifiers)) if modifiers else '')

        # generate each helper using the regmatch class
        iterops = interface.regmatch.modifier(**modifiers)
        uses_register = interface.regmatch.use(regs)

        # if within a function, then make sure we're within the chunk's bounds and we're a code type
        if function.within(ea):
            (start, _) = function.chunk(ea)
            fwithin = utils.fcompose(utils.fmap(functools.partial(operator.le, start), type.is_code), builtins.all)

        # otherwise ensure that we're not in the function and we're a code type.
        else:
            fwithin = utils.fcompose(utils.fmap(utils.fcompose(function.within, operator.not_), type.is_code), builtins.all)

            start = cls.__walk__(ea, cls.prev, fwithin)
            start = top() if start == idaapi.BADADDR else start

        # define a predicate for cls.walk to continue looping when true
        Freg = lambda ea: fwithin(ea) and not builtins.any(uses_register(ea, opnum) for opnum in iterops(ea))
        Fnot = utils.fcompose(predicate, operator.not_)
        F = utils.fcompose(utils.fmap(Freg, Fnot), builtins.any)

        ## skip the current address
        prevea = cls.prev(ea)
        if prevea is None:
            # FIXME: include registers in message
            logging.fatal(u"{:s}.prevreg({:s}) : Unable to start walking from the previous address of {:#x}.".format('.'.join([__name__, cls.__name__]), args, ea))
            return ea

        # now walk while none of our registers match
        res = cls.__walk__(prevea, cls.prev, F)
        if res in {None, idaapi.BADADDR} or (cls == address and res < start):
            # FIXME: include registers in message
            raise E.RegisterNotFoundError(u"{:s}.prevreg({:s}) : Unable to find register{:s} within the chunk {:#x}{:+#x}. Stopped at address {:#x}.".format('.'.join([__name__, cls.__name__]), args, '' if len(regs)==1 else 's', start, ea, res))

        # if the address is not a code type, then recurse so we can skip it.
        if not type.is_code(res):
            return cls.prevreg(res, predicate, *regs, **modifiers)

        # recurse if the user specified it
        modifiers['count'] = count - 1
        return cls.prevreg(res, predicate, *regs, **modifiers) if count > 1 else res

    @utils.multicase(reg=(six.string_types, interface.register_t))
    @classmethod
    def nextreg(cls, reg, *regs, **modifiers):
        '''Return the next address containing an instruction that uses `reg` or any one of the registers in `regs`.'''
        return cls.nextreg(ui.current.address(), reg, *regs, **modifiers)
    @utils.multicase(predicate=builtins.callable, reg=(six.string_types, interface.register_t))
    @classmethod
    def nextreg(cls, predicate, reg, *regs, **modifiers):
        '''Return the next address containing an instruction that matches `predicate` and uses `reg` or any one of the registers in `regs`.'''
        return cls.nextreg(ui.current.address(), predicate, reg, *regs, **modifiers)
    @utils.multicase(ea=six.integer_types, reg=(six.string_types, interface.register_t))
    @classmethod
    def nextreg(cls, ea, reg, *regs, **modifiers):
        '''Return the next address from `ea` containing an instruction that uses `reg` or any one of the registers in `regs`.'''
        return cls.nextreg(ea, utils.fconst(True), reg, *regs, **modifiers)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable, reg=(six.string_types, interface.register_t))
    @classmethod
    def nextreg(cls, ea, predicate, reg, *regs, **modifiers):
        '''Return the next address from `ea` containing an instruction that matches `predicate` and uses `reg` or any one of the registers in `regs`.'''
        regs = (reg,) + regs
        count = modifiers.get('count', 1)
        args = u', '.join(["{:x}".format(ea)] + ["{!r}".format(predicate)] + ["\"{:s}\"".format(utils.string.escape(str(reg), '"')) for reg in regs])
        args = args + (u", {:s}".format(utils.string.kwargs(modifiers)) if modifiers else '')

        # generate each helper using the regmatch class
        iterops = interface.regmatch.modifier(**modifiers)
        uses_register = interface.regmatch.use(regs)

        # if within a function, then make sure we're within the chunk's bounds.
        if function.within(ea):
            (_, end) = function.chunk(ea)
            fwithin = utils.fcompose(utils.fmap(functools.partial(operator.gt, end), type.is_code), builtins.all)

        # otherwise ensure that we're not in a function and we're a code type.
        else:
            fwithin = utils.fcompose(utils.fmap(utils.fcompose(function.within, operator.not_), type.is_code), builtins.all)

            end = cls.__walk__(ea, cls.next, fwithin)
            end = bottom() if end == idaapi.BADADDR else end

        # define a predicate for cls.walk to continue looping when true
        Freg = lambda ea: fwithin(ea) and not builtins.any(uses_register(ea, opnum) for opnum in iterops(ea))
        Fnot = utils.fcompose(predicate, operator.not_)
        F = utils.fcompose(utils.fmap(Freg, Fnot), builtins.any)

        # skip the current address
        nextea = cls.next(ea)
        if nextea is None:
            # FIXME: include registers in message
            logging.fatal(u"{:s}.nextreg({:s}) : Unable to start walking from the next address of {:#x}.".format('.'.join([__name__, cls.__name__]), args, ea))
            return ea

        # now walk while none of our registers match
        res = cls.__walk__(nextea, cls.next, F)
        if res in {None, idaapi.BADADDR} or (cls == address and res >= end):
            # FIXME: include registers in message
            raise E.RegisterNotFoundError(u"{:s}.nextreg({:s}) : Unable to find register{:s} within chunk {:#x}{:+#x}. Stopped at address {:#x}.".format('.'.join([__name__, cls.__name__]), args, '' if len(regs)==1 else 's', ea, end, res))

        # if the address is not a code type, then recurse so we can skip it.
        if not type.is_code(res):
            return cls.nextreg(res, predicate, *regs, **modifiers)

        # recurse if the user specified it
        modifiers['count'] = count - 1
        return cls.nextreg(res, predicate, *regs, **modifiers) if count > 1 else res

    # FIXME: modify this to just locate _any_ amount of change in the sp delta by default
    @utils.multicase(delta=six.integer_types)
    @classmethod
    def prevstack(cls, delta):
        '''Return the previous instruction that is past the specified sp `delta`.'''
        return cls.prevstack(ui.current.address(), delta)
    @utils.multicase(ea=six.integer_types, delta=six.integer_types)
    @classmethod
    def prevstack(cls, ea, delta):
        '''Return the previous instruction from `ea` that is past the specified sp `delta`.'''

        # FIXME: it'd be much better to keep track of this with a global class that wraps the logger
        if getattr(cls, '__prevstack_warning_count__', 0) == 0:
            logging.warning(u"{:s}.prevstack({:#x}, {:#x}) : This function's semantics are subject to change and may be deprecated in the future..".format('.'.join([__name__, cls.__name__]), ea, delta))
            cls.__prevstack_warning_count__ = getattr(cls, '__prevstack_warning_count__', 0) + 1

        # determine the boundaries that we're not allowed to seek past
        fn, sp = function.top(ea), function.get_spdelta(ea)
        start, _ = function.chunk(ea)
        fwithin = lambda ea: ea >= start and abs(function.get_spdelta(ea) - sp) < delta

        # walk to the previous major change in the stack delta, and keep
        # looping if we haven't found it yet.
        found = False
        while not found:
            res = cls.__walk__(ea, cls.prev, fwithin)
            if res == idaapi.BADADDR or res < start:
                raise E.AddressOutOfBoundsError(u"{:s}.prevstack({:#x}, {:+#x}) : Unable to locate instruction matching contraints due to encountering the top ({:#x}) of the function {:#x}. Stopped at {:#x}.".format('.'.join([__name__, cls.__name__]), ea, delta, start, fn, res))
            found, ea = type.is_code(res), cls.prev(res)
        return res

    # FIXME: modify this to just locate _any_ amount of change in the sp delta by default
    @utils.multicase(delta=six.integer_types)
    @classmethod
    def nextstack(cls, delta):
        '''Return the next instruction that is past the sp `delta`.'''
        return cls.nextstack(ui.current.address(), delta)
    @utils.multicase(ea=six.integer_types, delta=six.integer_types)
    @classmethod
    def nextstack(cls, ea, delta):
        '''Return the next instruction from `ea` that is past the sp `delta`.'''

        # FIXME: it'd be much better to keep track of this with a global class that wraps the logger
        if getattr(cls, '__nextstack_warning_count__', 0) == 0:
            logging.warning(u"{:s}.nextstack({:#x}, {:#x}) : This function's semantics are subject to change and may be deprecatd in the future.".format('.'.join([__name__, cls.__name__]), ea, delta))
            cls.__nextstack_warning_count__ = getattr(cls, '__nextstack_warning_count__', 0) + 1

        # determine the boundaries that we're not allowed to seek past
        fn, sp = function.top(ea), function.get_spdelta(ea)
        _, end = function.chunk(ea)

        # walk to the next major change in the stack delta, and keep
        # looping if we haven't found it yet.
        found = False
        while not found:
            res = cls.__walk__(ea, cls.next, lambda ea: ea < end and abs(function.get_spdelta(ea) - sp) < delta)
            if res == idaapi.BADADDR or res >= end:
                raise E.AddressOutOfBoundsError(u"{:s}.nextstack({:#x}, {:+#x}) : Unable to locate instruction matching contraints due to encountering the bottom ({:#x}) of the function {:#x}. Stopped at {:#x}.".format('.'.join([__name__, cls.__name__]), ea, delta, end, fn, res))
            found, ea = type.is_code(res), cls.next(res)
        return res

    prevdelta, nextdelta = utils.alias(prevstack, 'address'), utils.alias(nextstack, 'address')

    @utils.multicase()
    @classmethod
    def prevcall(cls):
        '''Return the previous call instruction.'''
        return cls.prevcall(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def prevcall(cls, predicate):
        '''Return the previous call instruction that matches `predicate`.'''
        return cls.prevcall(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def prevcall(cls, ea):
        '''Return the previous call instruction from the address `ea`.'''
        return cls.prevcall(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def prevcall(cls, ea, predicate):
        '''Return the previous call instruction from the address `ea` that matches `predicate`.'''
        F = utils.fcompose(utils.fmap(_instruction.type.is_call, predicate), builtins.all)
        return cls.prevF(ea, F, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def prevcall(cls, ea, count):
        return cls.prevF(ea, _instruction.type.is_call, count)

    @utils.multicase()
    @classmethod
    def nextcall(cls):
        '''Return the next call instruction.'''
        return cls.nextcall(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def nextcall(cls, predicate):
        '''Return the next call instruction that matches `predicate`.'''
        return cls.nextcall(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def nextcall(cls, ea):
        '''Return the next call instruction from the address `ea`.'''
        return cls.nextcall(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def nextcall(cls, ea, predicate):
        '''Return the next call instruction from the address `ea` that matches `predicate`.'''
        F = utils.fcompose(utils.fmap(_instruction.type.is_call, predicate), builtins.all)
        return cls.nextF(ea, F, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def nextcall(cls, ea, count):
        return cls.nextF(ea, _instruction.type.is_call, count)

    @utils.multicase()
    @classmethod
    def prevbranch(cls):
        '''Return the previous branch instruction.'''
        return cls.prevbranch(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def prevbranch(cls, predicate):
        '''Return the previous branch instruction that matches `predicate`.'''
        return cls.prevbranch(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def prevbranch(cls, ea):
        '''Return the previous branch instruction from the address `ea`.'''
        return cls.prevbranch(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def prevbranch(cls, ea, predicate):
        '''Return the previous branch instruction from the address `ea` that matches `predicate`.'''
        Fnocall = utils.fcompose(_instruction.type.is_call, operator.not_)
        Fbranch = _instruction.type.is_branch
        Fx = utils.fcompose(utils.fmap(Fnocall, Fbranch), builtins.all)
        F = utils.fcompose(utils.fmap(Fx, predicate), builtins.all)
        return cls.prevF(ea, F, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def prevbranch(cls, ea, count):
        Fnocall = utils.fcompose(_instruction.type.is_call, operator.not_)
        Fbranch = _instruction.type.is_branch
        F = utils.fcompose(utils.fmap(Fnocall, Fbranch), builtins.all)
        return cls.prevF(ea, F, count)

    @utils.multicase()
    @classmethod
    def nextbranch(cls):
        '''Return the next branch instruction.'''
        return cls.nextbranch(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def nextbranch(cls, predicate):
        '''Return the next branch instruction that matches `predicate`.'''
        return cls.nextbranch(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def nextbranch(cls, ea):
        '''Return the next branch instruction from the address `ea`.'''
        return cls.nextbranch(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def nextbranch(cls, ea, predicate):
        '''Return the next branch instruction from the address `ea` that matches `predicate`.'''
        Fnocall = utils.fcompose(_instruction.type.is_call, operator.not_)
        Fbranch = _instruction.type.is_branch
        Fx = utils.fcompose(utils.fmap(Fnocall, Fbranch), builtins.all)
        F = utils.fcompose(utils.fmap(Fx, predicate), builtins.all)
        return cls.nextF(ea, F, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def nextbranch(cls, ea, count):
        Fnocall = utils.fcompose(_instruction.type.is_call, operator.not_)
        Fbranch = _instruction.type.is_branch
        F = utils.fcompose(utils.fmap(Fnocall, Fbranch), builtins.all)
        return cls.nextF(ea, F, count)

    @utils.multicase()
    @classmethod
    def prevlabel(cls):
        '''Return the address of the previous label.'''
        return cls.prevlabel(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def prevlabel(cls, predicate):
        '''Return the address of the previous label that matches `predicate`.'''
        return cls.prevlabel(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def prevlabel(cls, ea):
        '''Return the address of the previous label from the address `ea`.'''
        return cls.prevlabel(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def prevlabel(cls, ea, predicate):
        '''Return the address of the previous label from the address `ea` that matches `predicate`.'''
        Flabel = type.has_label
        F = utils.fcompose(utils.fmap(Flabel, predicate), builtins.all)
        return cls.prevF(ea, F, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def prevlabel(cls, ea, count):
        return cls.prevF(ea, type.has_label, count)

    @utils.multicase()
    @classmethod
    def nextlabel(cls):
        '''Return the address of the next label.'''
        return cls.nextlabel(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def nextlabel(cls, predicate):
        '''Return the address of the next label that matches `predicate`.'''
        return cls.nextlabel(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def nextlabel(cls, ea):
        '''Return the address of the next label from the address `ea`.'''
        return cls.nextlabel(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def nextlabel(cls, ea, predicate):
        '''Return the address of the next label from the address `ea` that matches `predicate`.'''
        Flabel = type.has_label
        F = utils.fcompose(utils.fmap(Flabel, predicate), builtins.all)
        return cls.nextF(ea, F, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def nextlabel(cls, ea, count):
        return cls.nextF(ea, type.has_label, count)

    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('tagname')
    def prevtag(cls, **tagname):
        '''Return the previous address that contains a tag.'''
        return cls.prevtag(ui.current.address(), 1, **tagname)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    @utils.string.decorate_arguments('tagname')
    def prevtag(cls, predicate, **tagname):
        '''Return the previous address that contains a tag and matches `predicate`.'''
        return cls.prevtag(ui.current.address(), predicate, **tagname)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    @utils.string.decorate_arguments('tagname')
    def prevtag(cls, ea, **tagname):
        """Returns the previous address from `ea` that contains a tag.

        If the string `tagname` is specified, then only return the address if the specified tag is defined.
        """
        return cls.prevtag(ea, 1, **tagname)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    @utils.string.decorate_arguments('tagname')
    def prevtag(cls, ea, predicate, **tagname):
        '''Returns the previous address from `ea` that contains a tag and matches `predicate`.'''
        tagname = tagname.get('tagname', None)
        Ftag = type.has_comment if tagname is None else utils.fcompose(tag, utils.frpartial(operator.contains, tagname))
        F = utils.fcompose(utils.fmap(Ftag, predicate), builtins.all)
        return cls.prevF(ea, F, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    @utils.string.decorate_arguments('tagname')
    def prevtag(cls, ea, count, **tagname):
        tagname = tagname.get('tagname', None)
        Ftag = type.has_comment if tagname is None else utils.fcompose(tag, utils.frpartial(operator.contains, tagname))
        return cls.prevF(ea, Ftag, count)

    @utils.multicase()
    @classmethod
    @utils.string.decorate_arguments('tagname')
    def nexttag(cls, **tagname):
        '''Return the next address that contains a tag.'''
        return cls.nexttag(ui.current.address(), 1, **tagname)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    @utils.string.decorate_arguments('tagname')
    def nexttag(cls, predicate, **tagname):
        '''Return the next address that contains a tag and matches `predicate`.'''
        return cls.nexttag(ui.current.address(), predicate, **tagname)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    @utils.string.decorate_arguments('tagname')
    def nexttag(cls, ea, **tagname):
        """Returns the next address from `ea` that contains a tag.

        If the string `tagname` is specified, then only return the address if the specified tag is defined.
        """
        return cls.nexttag(ea, 1, **tagname)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    @utils.string.decorate_arguments('tagname')
    def nexttag(cls, ea, predicate, **tagname):
        '''Returns the next address from `ea` that contains a tag and matches `predicate`.'''
        tagname = tagname.get('tagname', None)
        Ftag = type.has_comment if tagname is None else utils.fcompose(tag, utils.frpartial(operator.contains, tagname))
        F = utils.fcompose(utils.fmap(Ftag, predicate), builtins.all)
        return cls.nextF(ea, F, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    @utils.string.decorate_arguments('tagname')
    def nexttag(cls, ea, count, **tagname):
        tagname = tagname.get('tagname', None)
        Ftag = type.has_comment if tagname is None else utils.fcompose(tag, utils.frpartial(operator.contains, tagname))
        return cls.nextF(ea, Ftag, count)
    prevcomment, nextcomment = utils.alias(prevtag, 'address'), utils.alias(nexttag, 'address')

    @utils.multicase()
    @classmethod
    def prevunknown(cls):
        '''Return the previous address that is undefined.'''
        return cls.prevunknown(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def prevunknown(cls, predicate):
        '''Return the previous address that is undefined and matches `predicate`.'''
        return cls.prevunknown(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def prevunknown(cls, ea):
        '''Return the previous address from `ea` that is undefined.'''
        return cls.prevunknown(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def prevunknown(cls, ea, predicate):
        '''Return the previous address from `ea` that is undefined and matches `predicate`.'''
        return cls.prevF(ea, type.is_unknown, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def prevunknown(cls, ea, count):
        return cls.prevF(ea, type.is_unknown, count)

    @utils.multicase()
    @classmethod
    def nextunknown(cls):
        '''Return the next address that is undefined.'''
        return cls.nextunknown(ui.current.address(), 1)
    @utils.multicase(predicate=builtins.callable)
    @classmethod
    def nextunknown(cls, predicate):
        '''Return the next address that is undefined and matches `predicate`.'''
        return cls.nextunknown(ui.current.address(), predicate)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def nextunknown(cls, ea):
        '''Return the next address from `ea` that is undefined.'''
        return cls.nextunknown(ea, 1)
    @utils.multicase(ea=six.integer_types, predicate=builtins.callable)
    @classmethod
    def nextunknown(cls, ea, predicate):
        '''Return the next address from `ea` that is undefined and matches `predicate`.'''
        return cls.nextF(ea, type.is_unknown, 1)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def nextunknown(cls, ea, count):
        return cls.nextF(ea, type.is_unknown, count)

    # address translations
    @classmethod
    def by_offset(cls, offset):
        '''Return the specified `offset` translated to an address in the database.'''
        return config.baseaddress() + offset
    byoffset = utils.alias(by_offset, 'address')

    @utils.multicase()
    @classmethod
    def offset(cls):
        '''Return the current address translated to an offset relative to the base address of the database.'''
        return offset(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def offset(cls, ea):
        '''Return the address `ea` translated to an offset relative to the base address of the database.'''
        return interface.address.inside(ea) - config.baseaddress()
    getoffset = utils.alias(offset, 'address')

a = addr = address  # XXX: ns alias

# address translations
offset = getoffset = get_offset = getOffset = utils.alias(address.offset, 'address')
byoffset = by_offset = byOffset = utils.alias(address.by_offset, 'address')

# datapoint navigation
prev, next = utils.alias(address.prev, 'address'), utils.alias(address.next, 'address')
prevref, nextref = utils.alias(address.prevref, 'address'), utils.alias(address.nextref, 'address')
prevreg, nextreg = utils.alias(address.prevreg, 'address'), utils.alias(address.nextreg, 'address')

class type(object):
    """
    This namespace is for fetching type information from the different
    addresses defined within the database. The functions within this
    namespace allow one to extract various type information from the
    different locations within the database.

    This namespace is also aliased as ``database.t``.

    By default, this namespace will return the ``idaapi.DT_TYPE`` of the
    specified address.

    Some examples of using this namespace can be::

        > print database.type.size(ea)
        > print database.type.is_initialized(ea)
        > print database.type.is_data(ea)
        > length = database.t.array.length(ea)
        > st = database.t.structure(ea)

    """

    @utils.multicase()
    def __new__(cls):
        '''Return the typeinfo at the current address as an ``idaapi.tinfo_t``.'''
        return cls(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    def __new__(cls, ea):
        '''Return the typeinfo at the address `ea` as an ``idaapi.tinfo_t``.'''
        ti = idaapi.tinfo_t()

        # Try and guess the typeinfo for the given address
        res = idaapi.guess_tinfo2(ea, ti) if idaapi.__version__ < 7.0 else idaapi.guess_tinfo(ti, ea)

        # If we failed, then we'll try and hack around it using idaapi.print_type.
        if res != idaapi.GUESS_FUNC_OK:
            fl = idaapi.PRTYPE_1LINE
            info_s = idaapi.print_type(ea, fl)

            # If we still couldn't get the typeinfo, then return None because
            # there isn't any typeinfo associated with the specified address.
            if info_s is None:
                return None

            # Parse the typeinfo string that IDA gave us and return it.
            ti = internal.declaration.parse(info_s)
            if ti is None:
                raise E.InvalidTypeOrValueError(u"{:s}.info({:#x}) : Unable to parse the returned type declaration ({!s}).".format('.'.join([__name__, cls.__name__]), ea, utils.string.repr(info_s)))
            return ti
        return ti
    @utils.multicase(none=None.__class__)
    def __new__(cls, none):
        '''Remove the typeinfo from the current address.'''
        return cls(ui.current.address(), None)
    @utils.multicase(info=(six.string_types, idaapi.tinfo_t))
    def __new__(cls, info):
        '''Apply the ``idaapi.tinfo_t`` typeinfo or typeinfo string in `info` to the current address.'''
        return cls(ui.current.address(), info)
    @utils.multicase(ea=six.integer_types, info=idaapi.tinfo_t)
    def __new__(cls, ea, info):
        '''Apply the ``idaapi.tinfo_t`` typeinfo in `info` to the address `ea`.'''
        info_s = "{!s}".format(info)

        # Check if we're pointing at an export or directly at a function. If we
        # are, then we need to use function.type.
        try:
            rt, ea = interface.addressOfRuntimeOrStatic(ea)
            if rt or function.address(ea) == ea:
                return function.type(ea, info)

        except E.FunctionNotFoundError:
            pass

        # All we need to do is to use idaapi to apply our parsed tinfo_t to the
        # address we were given.
        ok = idaapi.apply_tinfo(ea, info, idaapi.TINFO_DEFINITE)
        if not ok:
            raise E.DisassemblerError(u"{:s}.info({:#x}, {!s}) : Unable to apply typeinfo ({!s}) to the address ({:#x}).".format('.'.join([__name__, cls.__name__]), ea, utils.string.repr(info_s), utils.string.repr(info_s), ea))

        # Return the typeinfo that was applied to the specified address.
        return cls(ea)
    @utils.multicase(none=None.__class__)
    def __new__(cls, ea, none):
        '''Remove the typeinfo from the address `ea`.'''
        ti = idaapi.tinfo_t()

        # Grab the previous typeinfo if there was something there, and coerce
        # it to None if we got an error of some sort.
        try:
            result = cls(ea)

        except E.DisassemblerError:
            result = None

        # Clear the tinfo_t we created, and apply it to the given address. We
        # discard the result because IDA will _always_ give us an error despite
        # successfully clearing the typeinfo.
        ti.clear()
        _ = idaapi.apply_tinfo(ea, ti, idaapi.TINFO_DEFINITE)

        return result

    @utils.multicase(ea=six.integer_types, info=six.string_types)
    @utils.string.decorate_arguments('info')
    def __new__(cls, ea, info):
        '''Parse the typeinfo string in `info` to an ``idaapi.tinfo_t`` and apply it to the address `ea`.'''

        # Check if we're pointing at an export or directly at a function. If we
        # are, then we need to use function.type.
        try:
            rt, ea = interface.addressOfRuntimeOrStatic(ea)
            if rt or function.address(ea) == ea:
                return function.type(ea, info)

        except E.FunctionNotFoundError:
            pass

        # Strip out any invalid characters and replace them with '_'
        # declaration next.
        valid = {item for item in ': &*()[]@,' + string.digits}
        info_s = str().join(item if item in valid or idaapi.is_valid_typename(utils.string.to(item)) else '_' for item in info)

        # Now that we've prepped everything, ask IDA to parse this into a
        # tinfo_t for us. If we received None, then raise an exception due
        # to there being a parsing error of some sort.
        ti = internal.declaration.parse(info_s)
        if ti is None:
            raise E.InvalidTypeOrValueError(u"{:s}.info({:#x}) : Unable to parse the specified type declaration ({!s}).".format('.'.join([__name__, cls.__name__]), ea, utils.string.repr(info)))

        # Recurse into ourselves now that we have the actual typeinfo.
        return cls(ea, ti)

    @utils.multicase()
    @classmethod
    def size(cls):
        '''Returns the size of the item at the current address.'''
        return size(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def size(cls, ea):
        '''Returns the size of the item at the address `ea`.'''
        ea = interface.address.within(ea)
        return idaapi.get_item_size(ea)

    @utils.multicase()
    @classmethod
    def flags(cls):
        '''Returns the flags of the item at the current address.'''
        return cls.flags(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def flags(cls, ea):
        '''Returns the flags of the item at the address `ea`.'''
        getflags = idaapi.getFlags if idaapi.__version__ < 7.0 else idaapi.get_full_flags
        return getflags(interface.address.within(ea))
    @utils.multicase(ea=six.integer_types, mask=six.integer_types)
    @classmethod
    def flags(cls, ea, mask):
        '''Returns the flags at the address `ea` masked with `mask`.'''
        getflags = idaapi.getFlags if idaapi.__version__ < 7.0 else idaapi.get_full_flags
        return getflags(interface.address.within(ea)) & idaapi.as_uint32(mask)
    @utils.multicase(ea=six.integer_types, mask=six.integer_types, value=six.integer_types)
    @classmethod
    def flags(cls, ea, mask, value):
        '''Sets the flags at the address `ea` masked with `mask` set to `value`.'''
        if idaapi.__version__ < 7.0:
            ea = interface.address.within(ea)
            res = idaapi.getFlags(ea)
            idaapi.setFlags(ea, (res & ~mask) | value)
            return res & mask
        raise E.UnsupportedVersion(u"{:s}.flags({:#x}, {:#x}, {:d}) : IDA 7.0 has unfortunately deprecated `idaapi.setFlags(...)`.".format('.'.join([__name__, cls.__name__]), ea, mask, value))

    @utils.multicase()
    @staticmethod
    def is_initialized():
        '''Return if the current address is initialized.'''
        return type.is_initialized(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_initialized(ea):
        '''Return if the address specified by `ea` is initialized.'''
        return type.flags(interface.address.within(ea), idaapi.FF_IVL) == idaapi.FF_IVL
    @utils.multicase(ea=six.integer_types, size=six.integer_types)
    @staticmethod
    def is_initialized(ea, size):
        '''Return if the address specified by `ea` up to `size` bytes is initialized.'''
        ea = interface.address.within(ea)
        return all(type.flags(ea + offset, idaapi.FF_IVL) == idaapi.FF_IVL for offset in builtins.range(size))
    initializedQ = utils.alias(is_initialized, 'type')

    @utils.multicase()
    @staticmethod
    def is_code():
        '''Return if the current address is marked as code.'''
        return type.is_code(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_code(ea):
        '''Return if the address specified by `ea` is marked as code.'''
        return type.flags(interface.address.within(ea), idaapi.MS_CLS) == idaapi.FF_CODE
    @utils.multicase(ea=six.integer_types, size=six.integer_types)
    @staticmethod
    def is_code(ea, size):
        '''Return if the address specified by `ea` up to `size` bytes is marked as code.'''
        ea = interface.address.within(ea)
        return all(type.flags(ea + offset, idaapi.MS_CLS) == idaapi.FF_CODE for offset in builtins.range(size))
    codeQ = utils.alias(is_code, 'type')

    @utils.multicase()
    @staticmethod
    def is_data():
        '''Return if the current address is marked as data.'''
        return type.is_data(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_data(ea):
        '''Return if the address specified by `ea` is marked as data.'''
        return type.flags(interface.address.within(ea), idaapi.MS_CLS) == idaapi.FF_DATA
    @utils.multicase(ea=six.integer_types, size=six.integer_types)
    @staticmethod
    def is_data(ea, size):
        '''Return if the address specified by `ea` up to `size` bytes is marked as data.'''
        ea = interface.address.within(ea)
        return all(type.flags(ea + offset, idaapi.MS_CLS) == idaapi.FF_DATA for offset in builtins.range(size))
    dataQ = utils.alias(is_data, 'type')

    # True if ea marked unknown
    @utils.multicase()
    @staticmethod
    def is_unknown():
        '''Return if the current address is marked as unknown.'''
        return type.is_unknown(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_unknown(ea):
        '''Return if the address specified by `ea` is marked as unknown.'''
        return type.flags(interface.address.within(ea), idaapi.MS_CLS) == idaapi.FF_UNK
    @utils.multicase(ea=six.integer_types, size=six.integer_types)
    @staticmethod
    def is_unknown(ea, size):
        '''Return if the address specified by `ea` up to `size` bytes is marked as unknown.'''
        ea = interface.address.within(ea)
        return all(type.flags(ea + offset, idaapi.MS_CLS) == idaapi.FF_UNK for offset in builtins.range(size))
    unknownQ = is_undefined = undefinedQ = utils.alias(is_unknown, 'type')

    @utils.multicase()
    @staticmethod
    def is_head():
        '''Return if the current address is aligned to a definition in the database.'''
        return type.is_head(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_head(ea):
        '''Return if the address `ea` is aligned to a definition in the database.'''
        return type.flags(interface.address.within(ea), idaapi.FF_DATA) != 0
    headQ = utils.alias(is_head, 'type')

    @utils.multicase()
    @staticmethod
    def is_tail():
        '''Return if the current address is not aligned to a definition in the database.'''
        return type.is_tail(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_tail(ea):
        '''Return if the address `ea` is not aligned to a definition in the database.'''
        return type.flags(interface.address.within(ea), idaapi.MS_CLS) == idaapi.FF_TAIL
    tailQ = utils.alias(is_tail, 'type')

    @utils.multicase()
    @staticmethod
    def is_align():
        '''Return if the current address is defined as an alignment.'''
        return type.is_align(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_align(ea):
        '''Return if the address at `ea` is defined as an alignment.'''
        is_align = idaapi.isAlign if idaapi.__version__ < 7.0 else idaapi.is_align
        return is_align(type.flags(ea))
    alignQ = utils.alias(is_align, 'type')

    @utils.multicase()
    @staticmethod
    def has_comment():
        '''Return if the current address is commented.'''
        return type.has_comment(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def has_comment(ea):
        '''Return if the address at `ea` is commented.'''
        return type.flags(interface.address.within(ea), idaapi.FF_COMM) == idaapi.FF_COMM
    commentQ = utils.alias(has_comment, 'type')

    @utils.multicase()
    @staticmethod
    def has_reference():
        '''Return if the current address is referencing another address.'''
        return type.has_reference(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def has_reference(ea):
        '''Return if the address at `ea` is referencing another address.'''
        return type.flags(interface.address.within(ea), idaapi.FF_REF) == idaapi.FF_REF
    referenceQ = refQ = utils.alias(has_reference, 'type')

    @utils.multicase()
    @staticmethod
    def has_label():
        '''Return if the current address has a label.'''
        return type.has_label(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def has_label(ea):
        '''Return if the address at `ea` has a label.'''
        return idaapi.has_any_name(type.flags(ea)) or type.has_dummyname(ea) or type.has_customname(ea)
    labelQ = nameQ = has_name = utils.alias(has_label, 'type')

    @utils.multicase()
    @staticmethod
    def has_customname():
        '''Return if the current address has a custom name.'''
        return type.has_customname(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def has_customname(ea):
        '''Return if the address at `ea` has a custom name.'''
        return type.flags(interface.address.within(ea), idaapi.FF_NAME) == idaapi.FF_NAME
    customnameQ = utils.alias(has_customname, 'type')

    @utils.multicase()
    @staticmethod
    def has_dummyname():
        '''Return if the current address has a dummy name.'''
        return type.has_dummyname(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def has_dummyname(ea):
        '''Return if the address at `ea` has a dummy name.'''
        return type.flags(ea, idaapi.FF_LABL) == idaapi.FF_LABL
    dummynameQ = utils.alias(has_dummyname, 'type')

    @utils.multicase()
    @staticmethod
    def has_autoname():
        '''Return if the current address was automatically named.'''
        return type.has_autoname(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def has_autoname(ea):
        '''Return if the address `ea` was automatically named.'''
        return idaapi.has_auto_name(type.flags(ea))
    autonameQ = utils.alias(has_autoname, 'type')

    @utils.multicase()
    @staticmethod
    def has_publicname():
        '''Return if the current address has a public name.'''
        return type.has_publicname(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def has_publicname(ea):
        '''Return if the address at `ea` has a public name.'''
        return idaapi.is_public_name(interface.address.within(ea))
    publicnameQ = utils.alias(has_publicname, 'type')

    @utils.multicase()
    @staticmethod
    def has_weakname():
        '''Return if the current address has a name with a weak type.'''
        return type.has_weakname(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def has_weakname(ea):
        '''Return if the address at `ea` has a name with a weak type.'''
        return idaapi.is_weak_name(interface.address.within(ea))
    weaknameQ = utils.alias(has_weakname, 'type')

    @utils.multicase()
    @staticmethod
    def has_listedname():
        '''Return if the current address has a name that is listed.'''
        return type.has_listedname(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def has_listedname(ea):
        '''Return if the address at `ea` has a name that is listed.'''
        return idaapi.is_in_nlist(interface.address.within(ea))
    listednameQ = utils.alias(has_listedname, 'type')

    @utils.multicase()
    @staticmethod
    def has_typeinfo():
        '''Return if the current address has typeinfo associated with it.'''
        return type.has_typeinfo(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def has_typeinfo(ea):
        '''Return if the address at `ea` has typeinfo associated with it.'''
        try:
            ok = type(ea) is not None

        # If we got an exception raised, then we were unable to parse this type
        # properly. Prior to failing, check to see if the name is a mangled C++
        # symbol that contains type information.
        except E.InvalidTypeOrValueError as e:
            #logging.warning(u"{:s}.has_typeinfo({:#x}) : Unable to interpret the type information at address {:#x}.".format('.'.join([__name__, type.__name__]), ea, ea), exc_info=True)
            realname = name(ea)
            ok = internal.declaration.demangle(realname) != realname
        return ok
    typeinfoQ = infoQ = utils.alias(has_typeinfo, 'type')

    @utils.multicase()
    @staticmethod
    def is_string():
        '''Return if the current address is defined as a string.'''
        return type.is_string(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_string(ea):
        '''Return if the address at `ea` is defined as a string.'''
        FF_STRLIT = idaapi.FF_STRLIT if hasattr(idaapi, 'FF_STRLIT') else idaapi.FF_ASCI
        return type.flags(ea, idaapi.DT_TYPE) == FF_STRLIT
    stringQ = utils.alias(is_string, 'type')

    @utils.multicase()
    @staticmethod
    def is_structure():
        '''Return if the current address is defined as a structure.'''
        return type.is_structure(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_structure(ea):
        '''Return if the address at `ea` is defined as a structure.'''
        FF_STRUCT = idaapi.FF_STRUCT if hasattr(idaapi, 'FF_STRUCT') else idaapi.FF_STRU
        return type.flags(ea, idaapi.DT_TYPE) == FF_STRUCT
    structQ = structureQ = is_struc = is_struct = utils.alias(is_structure, 'type')

    @utils.multicase()
    @staticmethod
    def is_reference():
        '''Return if the data at the current address is referenced by another address.'''
        return type.is_reference(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_reference(ea):
        '''Return if the data at the address `ea` is referenced by another address.'''
        X, flags = idaapi.xrefblk_t(), idaapi.XREF_FAR | idaapi.XREF_DATA
        return X.first_to(ea, flags)
    is_ref = is_referenced = utils.alias(is_reference, 'type')

    class array(object):
        """
        This namespace is for returning type information about an array
        that is defined within the database. By default this namespace
        will return the array's element type and its number of elements
        as a list `[size, count]`.

        Some examples of using this namespace can be::

            > type, length = database.t.array()
            > print database.t.array.size(ea)
            > print database.t.array.member(ea)
            > print database.t.array.element(ea)
            > print database.t.array.length(ea)

        """
        @utils.multicase()
        def __new__(cls):
            '''Return the `[type, length]` of the array at the current address.'''
            return cls(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        def __new__(cls, ea):
            '''Return the `[type, length]` of the array at the address specified by `ea`.'''
            F, ti, cb = type.flags(ea), idaapi.opinfo_t(), idaapi.get_item_size(ea)

            # get the opinfo at the current address to verify if there's a structure or not
            ok = idaapi.get_opinfo(ea, 0, F, ti) if idaapi.__version__ < 7.0 else idaapi.get_opinfo(ti, ea, 0, F)
            tid = ti.tid if ok else idaapi.BADADDR

            # convert it to a pythonic type
            res = interface.typemap.dissolve(F, tid, cb)

            # if it's a list, then validate the result and return it
            if isinstance(res, list):
                element, length = res
                return [element, length]

            # this shouldn't ever happen, but if it does then it's a
            # single element array
            return [res, 1]

        @utils.multicase()
        @classmethod
        def member(cls):
            '''Return the type for the member of the array at the current address.'''
            return cls.member(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def member(cls, ea):
            '''Return the type for the member of the array at the address specified by `ea`.'''
            res, _ = cls(ea)
            return res

        @utils.multicase()
        @classmethod
        def element(cls):
            '''Return the type information for the member of the array defined at the current address.'''
            return cls.element(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def element(cls, ea):
            '''Return the type information for the member of the array defined at the address specified by `ea`.'''
            ti = type(ea)
            if ti is None:
                raise E.MissingTypeOrAttribute(u"{:s}.info({:#x}) : Unable to fetch any type information from the address at {:#x}.".format('.'.join([__name__, 'type', cls.__name__]), ea, ea))
            return ti.get_array_element() if ti.is_array() else ti
        info = typeinfo = utils.alias(element, 'type.array')

        @utils.multicase()
        @classmethod
        def size(cls):
            '''Return the size of a member in the array at the current address.'''
            return cls.size(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def size(cls, ea):
            '''Return the size of a member in the array at the address specified by `ea`.'''
            FF_STRUCT = idaapi.FF_STRUCT if hasattr(idaapi, 'FF_STRUCT') else idaapi.FF_STRU

            ea, F, T = interface.address.within(ea), type.flags(ea), type.flags(ea, idaapi.DT_TYPE)
            return _structure.size(type.structure.id(ea)) if T == FF_STRUCT else idaapi.get_full_data_elsize(ea, F)

        @utils.multicase()
        @classmethod
        def length(cls):
            '''Return the number of members in the array at the current address.'''
            return cls.length(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def length(cls, ea):
            '''Return the number of members in the array at the address specified by `ea`.'''
            ea, F = interface.address.within(ea), type.flags(ea)
            sz, ele = idaapi.get_item_size(ea), idaapi.get_full_data_elsize(ea, F)
            return sz // ele

    class structure(object):
        """
        This namespace for returning type information about a structure
        that is defined within the database. By default this namespace
        will return the ``structure_t`` at the given address.

        Some of the ways to use this namespace are::

            > st = database.t.struct()
            > print database.t.struct.size()
            > st = structure.by(database.t.id(ea))

        """
        @utils.multicase()
        def __new__(cls):
            '''Return the structure type at the current address.'''
            return cls(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        def __new__(cls, ea):
            '''Return the structure type at address `ea`.'''
            res = cls.id(ea)
            return _structure.by(res)

        @utils.multicase()
        @classmethod
        def id(cls):
            '''Return the identifier of the structure at the current address.'''
            return cls.id(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def id(cls, ea):
            '''Return the identifier of the structure at address `ea`.'''
            FF_STRUCT = idaapi.FF_STRUCT if hasattr(idaapi, 'FF_STRUCT') else idaapi.FF_STRU

            ea = interface.address.within(ea)

            res = type.flags(ea, idaapi.DT_TYPE)
            if res != FF_STRUCT:
                raise E.MissingTypeOrAttribute(u"{:s}.id({:#x}) : The type at specified address is not an FF_STRUCT({:#x}) and is instead {:#x}.".format('.'.join([__name__, 'type', cls.__name__]), ea, FF_STRUCT, res))

            ti, F = idaapi.opinfo_t(), type.flags(ea)
            res = idaapi.get_opinfo(ea, 0, F, ti) if idaapi.__version__ < 7.0 else idaapi.get_opinfo(ti, ea, 0, F)
            if not res:
                raise E.DisassemblerError(u"{:s}.id({:#x}) : The call to `idaapi.get_opinfo()` failed at {:#x}.".format('.'.join([__name__, 'type', cls.__name__]), ea, ea))
            return ti.tid

        @utils.multicase()
        @classmethod
        def size(cls):
            '''Return the total size of the structure at the current address.'''
            return cls.size(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def size(cls, ea):
            '''Return the total size of the structure at address `ea`.'''
            id = cls.id(ea)
            ptr = idaapi.get_struc(id)
            return idaapi.get_struc_size(ptr)
    struc = struct = structure  # ns alias

    @utils.multicase()
    @classmethod
    def switch(cls):
        '''Return the switch_t at the current address.'''
        return get.switch(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def switch(cls, ea):
        '''Return the switch_t at the address `ea`.'''
        return get.switch(ea)

    @utils.multicase()
    @staticmethod
    def is_importref():
        '''Returns true if the instruction at the current address references an import.'''
        return type.is_importref(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_importref(ea):
        '''Returns true if the instruction at `ea` references an import.'''
        ea = interface.address.inside(ea)

        # FIXME: this doesn't seem like the right way to determine an instruction is reffing an import
        datarefs, coderefs = xref.data_down(ea), xref.code_down(ea)
        return len(datarefs) == len(coderefs) and len(coderefs) > 0
    isimportref = importrefQ = utils.alias(is_importref, 'type')

    @utils.multicase()
    @staticmethod
    def is_globalref():
        '''Returns true if the instruction at the current address references a global.'''
        return is_globalref(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def is_globalref(ea):
        '''Returns true if the instruction at `ea` references a global.'''
        ea = interface.address.inside(ea)

        # FIXME: this doesn't seem like the right way to determine this...
        datarefs, coderefs = xref.data_down(ea), xref.code_down(ea)
        return len(datarefs) > len(coderefs)
    isglobalref = globalrefQ = utils.alias(is_globalref, 'type')

t = type    # XXX: ns alias

## information about a given address
size = utils.alias(type.size, 'type')
is_code = utils.alias(type.is_code, 'type')
is_data = utils.alias(type.is_data, 'type')
is_unknown = utils.alias(type.is_unknown, 'type')
is_head = utils.alias(type.is_head, 'type')
is_tail = utils.alias(type.is_tail, 'type')
is_align = utils.alias(type.is_align, 'type')

class xref(object):
    """
    This namespace is for navigating the cross-references (xrefs)
    associated with an address in the database. This lets one identify
    code xrefs from data xrefs and even allows one to add or remove
    xrefs as they see fit.

    This namespace is also aliased as ``database.x``.

    Some of the more common functions are used so often that they're
    also aliased as globals. Some of these are:

        ``database.up`` - Return all addresses that reference an address
        ``database.down`` - Return all addresses that an address references
        ``database.drefs`` - Return all the data references for an address
        ``database.crefs`` - Return all the code references for an address
        ``database.dxup`` - Return all the data references that reference an address
        ``database.dxdown`` - Return all the data references that an address references
        ``database.cxup`` - Return all the code references that reference an address
        ``database.cxdown`` - Return all the code references that an address references

    Some ways to utilize this namespace can be::

        > print database.x.up()
        > for ea in database.x.down(): ...
        > for ea in database.x.cu(ea): ...
        > ok = database.x.add_code(ea, target)
        > ok = database.x.rm_data(ea)

    """

    @utils.multicase()
    @staticmethod
    def code():
        '''Return all of the code xrefs that refer to the current address.'''
        return xref.code(ui.current.address(), False)
    @utils.multicase(descend=bool)
    @staticmethod
    def code(descend):
        return xref.code(ui.current.address(), descend)
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def code(ea):
        '''Return all of the code xrefs that refer to the address `ea`.'''
        return xref.code(ea, False)
    @utils.multicase(ea=six.integer_types, descend=bool)
    @staticmethod
    def code(ea, descend):
        """Return all of the code xrefs that refer to the address `ea`.

        If the bool `descend` is defined, then return only code refs that are referred by the specified address.
        """
        if descend:
            start, next = idaapi.get_first_cref_from, idaapi.get_next_cref_from
        else:
            start, next = idaapi.get_first_cref_to, idaapi.get_next_cref_to

        ea = interface.address.inside(ea)
        for addr in interface.xiterate(ea, start, next):
            yield addr
        return
    c = utils.alias(code, 'xref')

    @utils.multicase()
    @staticmethod
    def data():
        '''Return all of the data xrefs that refer to the current address.'''
        return xref.data(ui.current.address(), False)
    @utils.multicase(descend=bool)
    @staticmethod
    def data(descend):
        return xref.data(ui.current.address(), descend)
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def data(ea):
        '''Return all of the data xrefs that refer to the address `ea`.'''
        return xref.data(ea, False)
    @utils.multicase(ea=six.integer_types, descend=bool)
    @staticmethod
    def data(ea, descend):
        """Return all of the data xrefs that refer to the address `ea`.

        If the bool `descend` is defined, then return only the data refs that are referred by the specified address.
        """
        if descend:
            start, next = idaapi.get_first_dref_from, idaapi.get_next_dref_from
        else:
            start, next = idaapi.get_first_dref_to, idaapi.get_next_dref_to

        ea = interface.address.inside(ea)
        for addr in interface.xiterate(ea, start, next):
            yield addr
        return
    d = utils.alias(data, 'xref')

    @utils.multicase()
    @staticmethod
    def data_down():
        '''Return all of the data xrefs that are referenced by the current address.'''
        return xref.data_down(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def data_down(ea):
        '''Return all of the data xrefs that are referenced by the address `ea`.'''
        return sorted(xref.data(ea, True))
    dd = utils.alias(data_down, 'xref')

    @utils.multicase()
    @staticmethod
    def data_up():
        '''Return all of the data xrefs that refer to the current address.'''
        return xref.data_up(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def data_up(ea):
        '''Return all of the data xrefs that refer to the address `ea`.'''
        return sorted(xref.data(ea, False))
    du = utils.alias(data_up, 'xref')

    @utils.multicase()
    @staticmethod
    def code_down():
        '''Return all of the code xrefs that are referenced by the current address.'''
        return xref.code_down(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def code_down(ea):
        '''Return all of the code xrefs that are referenced by the address `ea`.'''
        res = {item for item in xref.code(ea, True)}

        # if we're not pointing at code, then the logic that follows is irrelevant
        if not type.is_code(ea):
            return sorted(res)

        try:
            # try and grab the next instruction which might be referenced
            next_ea = address.next(ea)

            # if the current instruction is a non-"stop" instruction, then it will
            # include a reference to the next instruction. so, we'll remove it.
            if type.is_code(ea) and _instruction.type.feature(ea, idaapi.CF_STOP) != idaapi.CF_STOP:
                res.discard(next_ea)

        except E.OutOfBoundsError:
            pass

        return sorted(res)
    cd = utils.alias(code_down, 'xref')

    @utils.multicase()
    @staticmethod
    def code_up():
        '''Return all of the code xrefs that are referenced by the current address.'''
        return xref.code_up(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def code_up(ea):
        '''Return all of the code xrefs that refer to the address `ea`.'''
        res = {item for item in xref.code(ea, False)}

        # if we're not pointing at code, then the logic that follows is irrelevant
        if not type.is_code(ea):
            return sorted(res)

        try:
            # try and grab the previous instruction which be referenced
            prev_ea = address.prev(ea)

            # if the previous instruction is a non-"stop" instruction, then it will
            # reference the current instruction which is a reason to remove it.
            if type.is_code(prev_ea) and _instruction.type.feature(prev_ea, idaapi.CF_STOP) != idaapi.CF_STOP:
                res.discard(prev_ea)

        except E.OutOfBoundsError:
            pass

        return sorted(res)
    cu = utils.alias(code_up, 'xref')

    @utils.multicase()
    @staticmethod
    def up():
        '''Return all of the references that refer to the current address.'''
        return xref.up(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def up(ea):
        '''Return all of the references that refer to the address `ea`.'''
        code, data = {item for item in xref.code_up(ea)}, {item for item in xref.data_up(ea)}
        return sorted(code | data)
    u = utils.alias(up, 'xref')

    # All locations that are referenced by the specified address
    @utils.multicase()
    @staticmethod
    def down():
        '''Return all of the references that are referred by the current address.'''
        return xref.down(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def down(ea):
        '''Return all of the references that are referred by the address `ea`.'''
        code, data = {item for item in xref.code_down(ea)}, {item for item in xref.data_down(ea)}
        return sorted(code | data)
    d = utils.alias(down, 'xref')

    @utils.multicase(target=six.integer_types)
    @staticmethod
    def add_code(target, **reftype):
        '''Add a code reference from the current address to `target`.'''
        return xref.add_code(ui.current.address(), target, **reftype)
    @utils.multicase(ea=six.integer_types, target=six.integer_types)
    @staticmethod
    def add_code(ea, target, **reftype):
        """Add a code reference from address `ea` to `target`.

        If the reftype `call` is true, then specify this ref as a function call.
        """
        ea, target = interface.address.head(ea, target)

        isCall = builtins.next((reftype[k] for k in ['call', 'is_call', 'isCall', 'iscall', 'callQ'] if k in reftype), None)
        if abs(target - ea) > 2**(config.bits() // 2):
            flowtype = idaapi.fl_CF if isCall else idaapi.fl_JF
        else:
            flowtype = idaapi.fl_CN if isCall else idaapi.fl_JN
        idaapi.add_cref(ea, target, flowtype | idaapi.XREF_USER)
        return target in xref.code_down(ea)
    ac = utils.alias(add_code, 'xref')

    @utils.multicase(target=six.integer_types)
    @staticmethod
    def add_data(target, **reftype):
        '''Add a data reference from the current address to `target`.'''
        return xref.add_data(ui.current.address(), target, **reftype)
    @utils.multicase(ea=six.integer_types, target=six.integer_types)
    @staticmethod
    def add_data(ea, target, **reftype):
        """Add a data reference from the address `ea` to `target`.

        If the reftype `write` is true, then specify that this ref is writing to the target.
        """
        ea, target = interface.address.head(ea, target)
        isWrite = reftype.get('write', False)
        flowtype = idaapi.dr_W if isWrite else idaapi.dr_R
        idaapi.add_dref(ea, target, flowtype | idaapi.XREF_USER)
        return target in xref.data_down(ea)
    ad = utils.alias(add_data, 'xref')

    @utils.multicase()
    @staticmethod
    def rm_code():
        '''Delete _all_ the code references at the current address.'''
        return xref.rm_code(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def rm_code(ea):
        '''Delete _all_ the code references at `ea`.'''
        ea = interface.address.inside(ea)
        [ idaapi.del_cref(ea, target, 0) for target in xref.code_down(ea) ]
        return False if len(xref.code_down(ea)) > 0 else True
    @utils.multicase(ea=six.integer_types, target=six.integer_types)
    @staticmethod
    def rm_code(ea, target):
        '''Delete any code references at `ea` that point to address `target`.'''
        ea = interface.address.inside(ea)
        idaapi.del_cref(ea, target, 0)
        return target not in xref.code_down(ea)
    rc = utils.alias(rm_code, 'xref')

    @utils.multicase()
    @staticmethod
    def rm_data():
        '''Delete _all_ the data references at the current address.'''
        return xref.rm_data(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def rm_data(ea):
        '''Delete _all_ the data references at `ea`.'''
        ea = interface.address.inside(ea)
        [ idaapi.del_dref(ea, target) for target in xref.data_down(ea) ]
        return False if len(xref.data_down(ea)) > 0 else True
    @utils.multicase(ea=six.integer_types, target=six.integer_types)
    @staticmethod
    def rm_data(ea, target):
        '''Delete any data references at `ea` that point to address `target`.'''
        ea = interface.address.inside(ea)
        idaapi.del_dref(ea, target)
        return target not in xref.data_down(ea)
    rd = utils.alias(rm_data, 'xref')

    @utils.multicase()
    @staticmethod
    def erase():
        '''Clear all references at the current address.'''
        return xref.erase(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @staticmethod
    def erase(ea):
        '''Clear all references at the address `ea`.'''
        ea = interface.address.inside(ea)
        return all(ok for ok in [xref.rm_code(ea), xref.rm_data(ea)])
    rx = utils.alias(rm_data, 'xref')

x = xref    # XXX: ns alias

drefs, crefs = utils.alias(xref.data, 'xref'), utils.alias(xref.code, 'xref')
dxdown, dxup = utils.alias(xref.data_down, 'xref'), utils.alias(xref.data_up, 'xref')
cxdown, cxup = utils.alias(xref.code_down, 'xref'), utils.alias(xref.code_up, 'xref')
up, down = utils.alias(xref.up, 'xref'), utils.alias(xref.down, 'xref')

# create/erase a mark at the specified address in the .idb
class marks(object):
    """
    This namespace is for interacting with the marks table within the
    database. By default, this namespace is capable of yielding the
    `(address, description)` of each mark within the database.

    This allows one to manage the marks. Although it is suggested to
    utilize "tags" as they provide significantly more flexibility.
    Using marks allows for one to use IDA's mark window for quick
    navigation to a mark.

    The functions in this namespace can be used like::

        > for ea, descr in database.marks(): ...
        > database.marks.new('this is my description')
        > database.marks.remove(ea)
        > ea, descr = database.marks.by(ea)

    """
    MAX_SLOT_COUNT = 0x400
    table = {}

    # FIXME: implement a matcher class for this too
    def __new__(cls):
        '''Yields each of the marked positions within the database.'''
        listable = [item for item in cls.iterate()] # make a copy in-case someone is actively modifying it
        for ea, comment in listable:
            yield ea, comment
        return

    @utils.multicase(description=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('description')
    def new(cls, description):
        '''Create a mark at the current address with the given `description`.'''
        return cls.new(ui.current.address(), description)
    @utils.multicase(ea=six.integer_types, description=six.string_types)
    @classmethod
    @utils.string.decorate_arguments('description')
    def new(cls, ea, description, **extra):
        '''Create a mark at the address `ea` with the given `description` and return its index.'''
        ea = interface.address.inside(ea)
        try:
            idx = cls.__find_slotaddress(ea)
            ea, res = cls.by_index(idx)
            logging.warning(u"{:s}.new({:#x}, {!r}{:s}) : Replacing mark {:d} at {:#x} and changing the description from \"{:s}\" to \"{:s}\".".format('.'.join([__name__, cls.__name__]), ea, description, u", {:s}".format(utils.string.kwargs(extra)) if extra else '', idx, ea, utils.string.escape(res, '"'), utils.string.escape(description, '"')))
        except (E.ItemNotFoundError, E.OutOfBoundsError):
            res, idx = None, cls.__free_slotindex()
            logging.info(u"{:s}.new({:#x}, {!r}{:s}) : Creating mark {:d} at {:#x} with the description \"{:s}\".".format('.'.join([__name__, cls.__name__]), ea, description, u", {:s}".format(utils.string.kwargs(extra)) if extra else '', idx, ea, utils.string.escape(description, '"')))
        cls.__set_description(idx, ea, description, **extra)
        return res

    @utils.multicase()
    @classmethod
    def remove(cls):
        '''Remove the mark at the current address.'''
        return cls.remove(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def remove(cls, ea):
        '''Remove the mark at the specified address `ea` returning the previous description.'''
        ea = interface.address.inside(ea)
        idx = cls.__find_slotaddress(ea)
        descr = cls.__get_description(idx)
        cls.__set_description(idx, ea, '')
        logging.warning(u"{:s}.remove({:#x}) : Removed mark {:d} at {:#x} with the description \"{:s}\".".format('.'.join([__name__, cls.__name__]), ea, idx, ea, utils.string.escape(descr, '"')))
        return descr

    @classmethod
    def iterate(cls):
        '''Iterate through all of the marks in the database.'''
        count = 0
        try:
            for idx in builtins.range(cls.MAX_SLOT_COUNT):
                yield cls.by_index(idx)
        except (E.OutOfBoundsError, E.AddressNotFoundError):
            pass
        return

    @classmethod
    def length(cls):
        '''Return the number of marks in the database.'''
        listable = [item for item in cls.iterate()]
        return len(listable)

    @classmethod
    def by_index(cls, index):
        '''Return the `(address, description)` of the mark at the specified `index` in the mark list.'''
        if 0 <= index < cls.MAX_SLOT_COUNT:
            return (cls.__get_slotaddress(index), cls.__get_description(index))
        raise E.IndexOutOfBoundsError(u"{:s}.by_index({:d}) : The specified mark slot index ({:d}) is out of bounds ({:s}).".format('.'.join([__name__, cls.__name__]), index, index, ("{:d} < 0".format(index)) if index < 0 else ("{:d} >= MAX_SLOT_COUNT".format(index))))
    byindex = utils.alias(by_index, 'marks')

    @utils.multicase()
    @classmethod
    def by_address(cls):
        '''Return the mark at the current address.'''
        return cls.by_address(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def by_address(cls, ea):
        '''Return the `(address, description)` of the mark at the given address `ea`.'''
        return cls.by_index(cls.__find_slotaddress(ea))
    by = byaddress = utils.alias(by_address, 'marks')

    ## Internal functions depending on which version of IDA is being used (<7.0)
    if idaapi.__version__ < 7.0:
        @classmethod
        def __location(cls, **attrs):
            '''Return a location_t object with the specified attributes.'''
            res = idaapi.curloc()
            [item for item in itertools.starmap(functools.partial(setattr, res), attrs.items())]
            return res

        @classmethod
        @utils.string.decorate_arguments('description')
        def __set_description(cls, index, ea, description, **extra):
            '''Modify the mark at `index` to point to the address `ea` with the specified `description`.'''
            res = cls.__location(ea=ea, x=extra.get('x', 0), y=extra.get('y', 0), lnnum=extra.get('y', 0))
            title, descr = map(utils.string.to, (description, description))
            res.mark(index, title, descr)
            #raise E.DisassemblerError(u"{:s}.set_description({:d}, {:#x}, {!r}{:s}) : Unable to get slot address for specified index.".format('.'.join([__name__, cls.__name__]), index, ea, description, u", {:s}".format(utils.string.kwargs(extra)) if extra else '')))
            return index

        @classmethod
        def __get_description(cls, index):
            '''Return the description of the mark at the specified `index`.'''
            res = cls.__location().markdesc(index)
            return utils.string.of(res)

        @classmethod
        def __find_slotaddress(cls, ea):
            '''Return the index of the mark at the specified address `ea`.'''
            # FIXME: figure out how to fail if this address isn't found
            res = itertools.islice(itertools.count(), cls.MAX_SLOT_COUNT)
            res, iterable = itertools.tee(map(cls.__get_slotaddress, res))
            try:
                count = len(builtins.list(itertools.takewhile(lambda item: item != ea, res)))
            except:
                raise E.AddressNotFoundError(u"{:s}.find_slotaddress({:#x}) : Unable to find specified slot address.".format('.'.join([__name__, cls.__name__]), ea))
            [item for item in itertools.islice(iterable, count)]
            if builtins.next(iterable) != ea:
                raise E.AddressNotFoundError(u"{:s}.find_slotaddress({:#x}) : Unable to find specified slot address.".format('.'.join([__name__, cls.__name__]), ea))
            return count

        @classmethod
        def __free_slotindex(cls):
            '''Return the index of the next available mark slot.'''
            return cls.length()

        @classmethod
        def __get_slotaddress(cls, index):
            '''Return the address of the mark at the specified `index`.'''
            loc = cls.__location()
            intp = idaapi.int_pointer()
            intp.assign(index)
            res = loc.markedpos(intp)
            if res == idaapi.BADADDR:
                raise E.AddressNotFoundError(u"{:s}.get_slotaddress({:d}) : Unable to get slot address for specified index.".format('.'.join([__name__, cls.__name__]), index))
            return address.head(res)

    ## Internal functions depending on which version of IDA is being used (>= 7.0)
    else:
        @classmethod
        @utils.string.decorate_arguments('description')
        def __set_description(cls, index, ea, description, **extra):
            '''Modify the mark at `index` to point to the address `ea` with the specified `description`.'''
            res = utils.string.to(description)
            idaapi.mark_position(ea, extra.get('lnnum', 0), extra.get('x', 0), extra.get('y', 0), index, res)
            #raise E.AddressNotFoundError(u"{:s}.set_description({:d}, {:#x}, {!r}{:s}) : Unable to get slot address for specified index.".format('.'.join([__name__, cls.__name__]), index, ea, description, u", {:s}".format(utils.string.kwargs(extra)) if extra else ''))
            return index

        @classmethod
        def __get_description(cls, index):
            '''Return the description of the mark at the specified `index`.'''
            res = idaapi.get_mark_comment(index)
            return utils.string.of(res)

        @classmethod
        def __find_slotaddress(cls, ea):
            '''Return the index of the mark at the specified address `ea`.'''
            res = itertools.islice(itertools.count(), cls.MAX_SLOT_COUNT)
            res, iterable = itertools.tee(map(cls.__get_slotaddress, res))
            try:
                count = len(builtins.list(itertools.takewhile(lambda item: item != ea, res)))
            except:
                raise E.AddressNotFoundError(u"{:s}.find_slotaddress({:#x}) : Unable to find specified slot address.".format('.'.join([__name__, cls.__name__]), ea))
            [item for item in itertools.islice(iterable, count)]
            if builtins.next(iterable) != ea:
                raise E.AddressNotFoundError(u"{:s}.find_slotaddress({:#x}) : Unable to find specified slot address.".format('.'.join([__name__, cls.__name__]), ea))
            return count

        @classmethod
        def __free_slotindex(cls):
            '''Return the index of the next available mark slot.'''
            res = builtins.next((i for i in builtins.range(cls.MAX_SLOT_COUNT) if idaapi.get_marked_pos(i) == idaapi.BADADDR), None)
            if res is None:
                raise OverflowError("{:s}.free_slotindex() : No free slots available for mark.".format('.'.join([__name__, 'marks', cls.__name__])))
            return res

        @classmethod
        def __get_slotaddress(cls, index):
            '''Get the address of the mark at index `index`.'''
            res = idaapi.get_marked_pos(index)
            if res == idaapi.BADADDR:
                raise E.AddressNotFoundError(u"{:s}.get_slotaddress({:d}) : Unable to get slot address for specified index.".format('.'.join([__name__, cls.__name__]), index))
            return address.head(res)

@utils.multicase()
def mark():
    '''Return the mark at the current address.'''
    _, res = marks.by_address(ui.current.address())
    return res
@utils.multicase(none=None.__class__)
def mark(none):
    '''Remove the mark at the current address.'''
    return mark(ui.current.address(), None)
@utils.multicase(ea=six.integer_types)
def mark(ea):
    '''Return the mark at the specified address `ea`.'''
    _, res = marks.by_address(ea)
    return res
@utils.multicase(description=six.string_types)
@utils.string.decorate_arguments('description')
def mark(description):
    '''Set the mark at the current address to the specified `description`.'''
    return mark(ui.current.address(), description)
@utils.multicase(ea=six.integer_types, none=None.__class__)
def mark(ea, none):
    '''Erase the mark at address `ea`.'''
    try:
        tag(ea, 'mark', None)
    except E.MissingTagError:
        pass
    color(ea, None)
    return marks.remove(ea)
@utils.multicase(ea=six.integer_types, description=six.string_types)
@utils.string.decorate_arguments('description')
def mark(ea, description):
    '''Sets the mark at address `ea` to the specified `description`.'''
    return marks.new(ea, description)

class extra(object):
    r"""
    This namespace is for interacting with IDA's "extra" comments that
    can be associated with an address. This allows one to prefix or
    suffix an address with a large block of text simulating a
    multilined or paragraph comment.

    To add extra comments, one can do this like::

        > res = database.ex.prefix(ea, 'this\nis\na\nmultilined\ncomment')
        > res = database.ex.suffix(ea, "whee\nok...i'm over it.")
        > database.ex.insert(ea, 1)
        > database.extra.append(ea, 2)

    """

    MAX_ITEM_LINES = 5000   # defined in cfg/ida.cfg according to python/idc.py
    MAX_ITEM_LINES = (idaapi.E_NEXT-idaapi.E_PREV) if idaapi.E_NEXT > idaapi.E_PREV else idaapi.E_PREV-idaapi.E_NEXT

    @classmethod
    def __has_extra__(cls, ea, base):
        sup = internal.netnode.sup
        return sup.get(ea, base, type=memoryview) is not None

    @utils.multicase()
    @classmethod
    def has_prefix(cls):
        '''Returns true if the item at the current address has extra prefix lines.'''
        return cls.__has_extra__(ui.current.address(), idaapi.E_PREV)
    @utils.multicase()
    @classmethod
    def has_suffix(cls):
        '''Returns true if the item at the current address has extra suffix lines.'''
        return cls.__has_extra__(ui.current.address(), idaapi.E_NEXT)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def has_prefix(cls, ea):
        '''Returns true if the item at the address `ea` has extra prefix lines.'''
        return cls.__has_extra__(ea, idaapi.E_PREV)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def has_suffix(cls, ea):
        '''Returns true if the item at the address `ea` has extra suffix lines.'''
        return cls.__has_extra__(ea, idaapi.E_NEXT)
    prefixQ, suffixQ = utils.alias(has_prefix, 'extra'), utils.alias(has_suffix, 'extra')

    @classmethod
    def __count__(cls, ea, base):
        sup = internal.netnode.sup
        for i in builtins.range(cls.MAX_ITEM_LINES):
            row = sup.get(ea, base + i, type=memoryview)
            if row is None: break
        return i or None

    if idaapi.__version__ < 7.0:
        @classmethod
        def __hide__(cls, ea):
            '''Hide the extra comment(s) at address ``ea``.'''
            if type.flags(ea, idaapi.FF_LINE) == idaapi.FF_LINE:
                type.flags(ea, idaapi.FF_LINE, 0)
                return True
            return False

        @classmethod
        def __show__(cls, ea):
            '''Show the extra comment(s) at address ``ea``.'''
            if type.flags(ea, idaapi.FF_LINE) != idaapi.FF_LINE:
                type.flags(ea, idaapi.FF_LINE, idaapi.FF_LINE)  # FIXME: IDA 7.0 : ida_nalt.set_visible_item?
                return True
            return False

        @classmethod
        def __get__(cls, ea, base):
            '''Fetch the extra comment(s) for the address ``ea`` at the index ``base``.'''
            sup = internal.netnode.sup

            # count the number of rows
            count = cls.__count__(ea, base)
            if count is None: return None

            # now we can fetch them
            res = (sup.get(ea, base + i, type=bytes) for i in builtins.range(count))

            # remove the null-terminator if there is one
            res = (row.rstrip(b'\0') for row in res)

            # fetch them from IDA and join them with newlines
            return '\n'.join(map(utils.string.of, res))
        @classmethod
        @utils.string.decorate_arguments('string')
        def __set__(cls, ea, string, base):
            '''Set the extra comment(s) for the address ``ea`` with the newline-delimited ``string`` at the index ``base``.'''
            cls.__hide__(ea)
            sup = internal.netnode.sup

            # break the string up into rows, and encode each type for IDA
            res = [ utils.string.to(item) for item in string.split('\n') ]

            # assign them directly into IDA
            [ sup.set(ea, base + i, row + b'\0') for i, row in enumerate(res) ]

            # now we can show (refresh) them
            cls.__show__(ea)

            # an exception before this happens would imply failure
            return True
        @classmethod
        def __delete__(cls, ea, base):
            '''Remove the extra comment(s) for the address ``ea`` at the index ``base``.'''
            sup = internal.netnode.sup

            # count the number of rows to remove
            count = cls.__count__(ea, base)
            if count is None: return False

            # hide them before we modify it
            cls.__hide__(ea)

            # now we can remove them
            [ sup.remove(ea, base + i) for i in builtins.range(count) ]

            # and then show (refresh) it
            cls.__show__(ea)
            return True
    else:
        @classmethod
        def __get__(cls, ea, base):
            '''Fetch the extra comment(s) for the address ``ea`` at the index ``base``.'''
            # count the number of rows
            count = cls.__count__(ea, base)
            if count is None: return None

            # grab the extra comments from the database
            iterable = (idaapi.get_extra_cmt(ea, base + i) or '' for i in builtins.range(count))

            # convert them back into Python and join them with a newline
            iterable = (utils.string.of(item) for item in iterable)
            return '\n'.join(iterable)
        @classmethod
        @utils.string.decorate_arguments('string')
        def __set__(cls, ea, string, base):
            '''Set the extra comment(s) for the address ``ea`` with the newline-delimited ``string`` at the index ``base``.'''
            # break the string up into rows, and encode each type for IDA
            iterable = (utils.string.to(item) for item in string.split('\n'))

            # assign them into IDA using its api
            [ idaapi.update_extra_cmt(ea, base + i, row) for i, row in enumerate(iterable) ]

            # return how many newlines there were
            return string.count('\n')
        @classmethod
        def __delete__(cls, ea, base):
            '''Remove the extra comment(s) for the address ``ea`` at the index ``base``.'''

            # count the number of extra comments to remove
            res = cls.__count__(ea, base)
            if res is None: return 0

            # now we can delete them using the api
            [idaapi.del_extra_cmt(ea, base + i) for i in builtins.range(res)]

            # return how many comments we deleted
            return res

    @utils.multicase(ea=six.integer_types)
    @classmethod
    def __get_prefix__(cls, ea):
        '''Return the prefixed comment at address `ea`.'''
        return cls.__get__(ea, idaapi.E_PREV)

    @utils.multicase(ea=six.integer_types)
    @classmethod
    def __get_suffix__(cls, ea):
        '''Return the suffixed comment at address `ea`.'''
        return cls.__get__(ea, idaapi.E_NEXT)

    @utils.multicase(ea=six.integer_types)
    @classmethod
    def __delete_prefix__(cls, ea):
        '''Delete the prefixed comment at address `ea`.'''
        res = cls.__get__(ea, idaapi.E_PREV)
        cls.__delete__(ea, idaapi.E_PREV)
        return res
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def __delete_suffix__(cls, ea):
        '''Delete the suffixed comment at address `ea`.'''
        res = cls.__get__(ea, idaapi.E_NEXT)
        cls.__delete__(ea, idaapi.E_NEXT)
        return res

    @utils.multicase(ea=six.integer_types, string=six.string_types)
    @classmethod
    def __set_prefix__(cls, ea, string):
        '''Set the prefixed comment at address `ea` to the specified `string`.'''
        res, ok = cls.__delete_prefix__(ea), cls.__set__(ea, string, idaapi.E_PREV)
        ok = cls.__set__(ea, string, idaapi.E_PREV)
        return res
    @utils.multicase(ea=six.integer_types, string=six.string_types)
    @classmethod
    def __set_suffix__(cls, ea, string):
        '''Set the suffixed comment at address `ea` to the specified `string`.'''
        res, ok = cls.__delete_suffix__(ea), cls.__set__(ea, string, idaapi.E_NEXT)
        return res

    @utils.multicase()
    @classmethod
    def __get_prefix__(cls):
        '''Return the prefixed comment at the current address.'''
        return cls.__get_prefix__(ui.current.address())
    @utils.multicase()
    @classmethod
    def __get_suffix__(cls):
        '''Return the suffixed comment at the current address.'''
        return cls.__get_suffix__(ui.current.address())
    @utils.multicase()
    @classmethod
    def __delete_prefix__(cls):
        '''Delete the prefixed comment at the current address.'''
        return cls.__delete_prefix__(ui.current.address())
    @utils.multicase()
    @classmethod
    def __delete_suffix__(cls):
        '''Delete the suffixed comment at the current address.'''
        return cls.__delete_suffix__(ui.current.address())
    @utils.multicase(string=six.string_types)
    @classmethod
    def __set_prefix__(cls, string):
        '''Set the prefixed comment at the current address to the specified `string`.'''
        return cls.__set_prefix__(ui.current.address(), string)
    @utils.multicase(string=six.string_types)
    @classmethod
    def __set_suffix__(cls, string):
        '''Set the suffixed comment at the current address to the specified `string`.'''
        return cls.__set_suffix__(ui.current.address(), string)

    @utils.multicase()
    @classmethod
    def prefix(cls):
        '''Return the prefixed comment at the current address.'''
        return cls.__get_prefix__(ui.current.address())
    @utils.multicase(string=six.string_types)
    @classmethod
    def prefix(cls, string):
        '''Set the prefixed comment at the current address to the specified `string`.'''
        return cls.__set_prefix__(ui.current.address(), string)
    @utils.multicase(none=None.__class__)
    @classmethod
    def prefix(cls, none):
        '''Delete the prefixed comment at the current address.'''
        return cls.__delete_prefix__(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def prefix(cls, ea):
        '''Return the prefixed comment at address `ea`.'''
        return cls.__get_prefix__(ea)
    @utils.multicase(ea=six.integer_types, string=six.string_types)
    @classmethod
    def prefix(cls, ea, string):
        '''Set the prefixed comment at address `ea` to the specified `string`.'''
        return cls.__set_prefix__(ea, string)
    @utils.multicase(ea=six.integer_types, none=None.__class__)
    @classmethod
    def prefix(cls, ea, none):
        '''Delete the prefixed comment at address `ea`.'''
        return cls.__delete_prefix__(ea)

    @utils.multicase()
    @classmethod
    def suffix(cls):
        '''Return the suffixed comment at the current address.'''
        return cls.__get_suffix__(ui.current.address())
    @utils.multicase(string=six.string_types)
    @classmethod
    def suffix(cls, string):
        '''Set the suffixed comment at the current address to the specified `string`.'''
        return cls.__set_suffix__(ui.current.address(), string)
    @utils.multicase(none=None.__class__)
    @classmethod
    def suffix(cls, none):
        '''Delete the suffixed comment at the current address.'''
        return cls.__delete_suffix__(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def suffix(cls, ea):
        '''Return the suffixed comment at address `ea`.'''
        return cls.__get_suffix__(ea)
    @utils.multicase(ea=six.integer_types, string=six.string_types)
    @classmethod
    def suffix(cls, ea, string):
        '''Set the suffixed comment at address `ea` to the specified `string`.'''
        return cls.__set_suffix__(ea, string)
    @utils.multicase(ea=six.integer_types, none=None.__class__)
    @classmethod
    def suffix(cls, ea, none):
        '''Delete the suffixed comment at address `ea`.'''
        return cls.__delete_suffix__(ea)

    @classmethod
    def __insert_space(cls, ea, count, getter_setter_remover):
        getter, setter, remover = getter_setter_remover

        res = getter(ea)
        lstripped, nl = ('', 0) if res is None else (res.lstrip('\n'), len(res) - len(res.lstrip('\n')) + 1)
        return setter(ea, '\n'*(nl + count - 1) + lstripped) if nl + count > 0 or lstripped else remover(ea)
    @classmethod
    def __append_space(cls, ea, count, getter_setter_remover):
        getter, setter, remover = getter_setter_remover

        res = getter(ea)
        rstripped, nl = ('', 0) if res is None else (res.rstrip('\n'), len(res) - len(res.rstrip('\n')) + 1)
        return setter(ea, rstripped + '\n'*(nl + count - 1)) if nl + count > 0 or rstripped else remover(ea)

    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def preinsert(cls, ea, count):
        '''Insert `count` lines in front of the item at address `ea`.'''
        res = cls.__get_prefix__, cls.__set_prefix__, cls.__delete_prefix__
        return cls.__insert_space(ea, count, res)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def preappend(cls, ea, count):
        '''Append `count` lines in front of the item at address `ea`.'''
        res = cls.__get_prefix__, cls.__set_prefix__, cls.__delete_prefix__
        return cls.__append_space(ea, count, res)

    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def postinsert(cls, ea, count):
        '''Insert `count` lines after the item at address `ea`.'''
        res = cls.__get_suffix__, cls.__set_suffix__, cls.__delete_suffix__
        return cls.__insert_space(ea, count, res)
    @utils.multicase(ea=six.integer_types, count=six.integer_types)
    @classmethod
    def postappend(cls, ea, count):
        '''Append `count` lines after the item at address `ea`.'''
        res = cls.__get_suffix__, cls.__set_suffix__, cls.__delete_suffix__
        return cls.__append_space(ea, count, res)

    @utils.multicase(count=six.integer_types)
    @classmethod
    def preinsert(cls, count):
        '''Insert `count` lines in front of the item at the current address.'''
        return cls.preinsert(ui.current.address(), count)
    @utils.multicase(count=six.integer_types)
    @classmethod
    def preappend(cls, count):
        '''Append `count` lines in front of the item at the current address.'''
        return cls.preappend(ui.current.address(), count)

    @utils.multicase(count=six.integer_types)
    @classmethod
    def postinsert(cls, count):
        '''Insert `count` lines after the item at the current address.'''
        return cls.postinsert(ui.current.address(), count)
    @utils.multicase(count=six.integer_types)
    @classmethod
    def postappend(cls, count):
        '''Append `count` lines after the item at the current address.'''
        return cls.postappend(ui.current.address(), count)

    insert, append = utils.alias(preinsert, 'extra'), utils.alias(preappend, 'extra')
ex = extra  # XXX: ns alias

class set(object):
    """
    This namespace for setting the type of an address within the
    database. This allows one to apply a particular type to a given
    address. This allows one to specify whether a type is a string,
    undefined, code, data, an array, or even a structure.

    This can be used as in the following examples::

        > database.set.unknown(ea)
        > database.set.aligned(ea, alignment=0x10)
        > database.set.string(ea)
        > database.set.structure(ea, structure.by('mystructure'))

    """

    @utils.multicase(info=(six.string_types, idaapi.tinfo_t))
    @classmethod
    def info(cls, info):
        '''Set the typeinfo at the current address to `info`.'''
        return cls.info(ui.current.address(), info)
    @utils.multicase(ea=six.integer_types, info=(six.string_types, idaapi.tinfo_t))
    @classmethod
    def info(cls, ea, info):
        '''Set the typeinfo at the address `ea` to `info`.'''
        return type(ea, info)
    typeinfo = utils.alias(info, 'set')

    @utils.multicase()
    @classmethod
    def unknown(cls):
        '''Set the data at the current address to undefined.'''
        return cls.unknown(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def unknown(cls, ea):
        '''Set the data at address `ea` to undefined.'''
        size = idaapi.get_item_size(ea)
        if idaapi.__version__ < 7.0:
            ok = idaapi.do_unknown_range(ea, size, idaapi.DOUNK_SIMPLE)
        else:
            ok = idaapi.del_items(ea, idaapi.DELIT_SIMPLE, size)
        return size if ok and type.is_unknown(ea, size) else idaapi.get_item_size(ea) if type.is_unknown(ea) else 0
    @utils.multicase(ea=six.integer_types, size=six.integer_types)
    @classmethod
    def unknown(cls, ea, size):
        '''Set the data at address `ea` to undefined.'''
        if idaapi.__version__ < 7.0:
            ok = idaapi.do_unknown_range(ea, size, idaapi.DOUNK_SIMPLE)
        else:
            ok = idaapi.del_items(ea, idaapi.DELIT_SIMPLE, size)
        return size if ok and type.is_unknown(ea, size) else idaapi.get_item_size(ea) if type.is_unknown(ea) else 0
    undef = undefine = undefined = utils.alias(unknown, 'set')

    @utils.multicase()
    @classmethod
    def code(cls):
        '''Set the data at the current address to code.'''
        return cls.code(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def code(cls, ea):
        '''Set the data at address `ea` to code.'''
        if idaapi.__version__ < 7.0:
            return idaapi.create_insn(ea)

        res = idaapi.insn_t()
        try:
            return idaapi.create_insn(ea, res)
        except TypeError:
            pass
        return idaapi.create_insn(res, ea)

    @utils.multicase(size=six.integer_types)
    @classmethod
    def data(cls, size, **type):
        '''Set the data at the current address to have the specified `size` and `type`.'''
        return cls.data(ui.current.address(), size, **type)
    @utils.multicase(ea=six.integer_types, size=six.integer_types)
    @classmethod
    def data(cls, ea, size, **type):
        """Set the data at address `ea` to have the specified `size` and `type`.

        If `type` is not specified, then choose the correct type based on the size.
        """

        ## Set some constants for anything older than IDA 7.0
        if idaapi.__version__ < 7.0:
            FF_STRUCT = idaapi.FF_STRU

            # Try and fetch some attributes..if we're unable to then we use None
            # as a placeholder so that we know that we need to use the older way
            # that IDA applies structures or alignment
            create_data, create_struct, create_align = idaapi.do_data_ex, getattr(idaapi, 'doStruct', None), getattr(idaapi, 'doAlign', None)

            lookup = {
                1 : idaapi.FF_BYTE, 2 : idaapi.FF_WORD, 4 : idaapi.FF_DWRD,
                8 : idaapi.FF_QWRD
            }

            # Older versions of IDA might not define FF_OWRD, so we just
            # try and add if its available. We fall back to an array anyways.
            if hasattr(idaapi, 'FF_OWRD'): lookup[16] = idaapi.FF_OWRD

        ## Set some constants used for IDA 7.0 and newer
        else:
            FF_STRUCT = idaapi.FF_STRUCT
            create_data, create_struct, create_align = idaapi.create_data, idaapi.create_struct, idaapi.create_align

            lookup = {
                1 : idaapi.FF_BYTE, 2 : idaapi.FF_WORD, 4 : idaapi.FF_DWORD,
                8 : idaapi.FF_QWORD, 16 : idaapi.FF_OWORD
            }

        ## Now we can apply the type to the given address
        try:
            res = type['type'] if 'type' in type else lookup[size]

        # If the size doesn't exist, then let the user know that we don't know what to do
        except KeyError:
            raise E.InvalidTypeOrValueError("{:s}.data({:#x}, {:d}{:s}) : Unable to determine the correct type for the specified size ({:+d}) to assign to the data.".format('.'.join([__name__, cls.__name__]), ea, size, u", {:s}".format(utils.string.kwargs(type)) if type else '', size))

        # Check if we need to use older IDA logic by checking of any of our api calls are None
        if idaapi.__version__ < 7.0 and any(f is None for f in [create_struct, create_align]):
            ok = create_data(ea, idaapi.FF_STRUCT if isinstance(res, _structure.structure_t) else res, size, res.id if isinstance(res, _structure.structure_t) else 0)

        # Otherwise we can create structures normally
        elif isinstance(res, _structure.structure_t):
            ok = create_struct(ea, size, res.id)

        # Or apply alignment properly...
        elif res == idaapi.FF_ALIGN and hasattr(idaapi, 'create_align'):
            ok = create_align(ea, size, 0)

        # Anything else is just regular data that we can fall back to
        else:
            ok = idaapi.create_data(ea, res, size, 0)

        # Return our new size if we were successful
        return idaapi.get_item_size(ea) if ok else 0

    @utils.multicase()
    @classmethod
    def alignment(cls, **alignment):
        '''Set the data at the current address as aligned with the specified `alignment`.'''
        return cls.align(ui.current.address(), **alignment)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def alignment(cls, ea, **alignment):
        """Set the data at address `ea` as aligned.

        If `alignment` is specified, then use it as the default alignment.
        If `size` is specified, then align that number of bytes.
        """
        if not type.is_unknown(ea):
            logging.warning("{:s}.set.alignment({:#x}{:s}) : Refusing to align the specified address ({:#x}) as it has already been defined.".format('.'.join([__name__, cls.__name__]), ea, u", {:s}".format(utils.string.kwargs(alignment)) if alignment else '', ea))  # XXX: define a custom warning
            return 0

        # grab the size out of the kwarg
        if 'size' in alignment:
            size = alignment['size']

        # otherwise, figure it out by counting repetitions
        # if the address is actually initialized
        elif type.is_initialized(ea):
            size, by = 0, read(ea, 1)
            while read(ea + size, 1) == by:
                size += 1
            pass

        # if it's uninitialized, then use the nextlabel as the
        # boundary to determine the size
        else:
            size = address.nextlabel(ea) - ea

        # if idaapi.create_align doesn't exist, then just hand this
        # off to idaapi.create_data with the determined size.
        if not hasattr(idaapi, 'create_align'):
            return cls.data(ea, size, type=idaapi.FF_ALIGN)

        # grab the aligment out of the kwarg
        if any(k in alignment for k in ['align', 'alignment']):
            align = builtins.next((alignment[k] for k in ['align', 'alignment'] if k in alignment))
            e = math.trunc(math.log(align) / math.log(2))

        # or we again...just figure it out via brute force
        else:
            e, target = 13, ea + size
            while e > 0:
                if target & (2**e-1) == 0:
                    break
                e -= 1

        # we should be good to go
        ok = idaapi.create_align(ea, size, e)

        # return the new size, or a failure
        return idaapi.get_item_size(ea) if ok else 0
    align = aligned = utils.alias(alignment, 'set')

    @utils.multicase()
    @classmethod
    def string(cls, **strtype):
        '''Set the data at the current address to a string with the specified `strtype`.'''
        return cls.string(ui.current.address(), **strtype)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def string(cls, ea, **strtype):
        '''Set the data at address `ea` to a string with the specified `strtype`.'''
        return cls.string(ea, strtype.pop('length', 0), **strtype)
    @utils.multicase(ea=six.integer_types, length=six.integer_types)
    @classmethod
    def string(cls, ea, length, **strtype):
        """Set the data at address `ea` to a string with the specified `length`.

        If the integer `strtype` is specified, then apply a string of the specified character width.
        If the tuple `strtype` is specified, the first item is the string's character width and the second item is the size of the length prefix.
        """
        widthtype = {1: idaapi.STRWIDTH_1B, 2: idaapi.STRWIDTH_2B, 4: idaapi.STRWIDTH_4B}
        lengthtype = {0: idaapi.STRLYT_TERMCHR, 1: idaapi.STRLYT_PASCAL1, 2: idaapi.STRLYT_PASCAL2, 4: idaapi.STRLYT_PASCAL4}

        # First grab the type that the user gave us from either the old or new parameter.
        res = builtins.next((strtype[item] for item in ['strtype', 'type'] if item in strtype), (1, 0))

        # If it's not tuple, then convert it to one that uses a null-terminator.
        if not isinstance(res, (builtins.list, builtins.tuple)):
            res = (res, 0)

        # Now we can extract the width and the length size so we can validate them.
        width_t, length_t = res
        if not operator.contains(widthtype, width_t):
            raise E.InvalidTypeOrValueError("{:s}.string({:#x}, {:d}{:s}) : The requested character width ({:d}) is unsupported.".format('.'.join([__name__, cls.__name__]), ea, length, u", {!s}".format(utils.string.kwargs(strtype)) if strtype else '', width_t))
        if not operator.contains(lengthtype, length_t):
            raise E.InvalidTypeOrValueError("{:s}.string({:#x}, {:d}{:s}) : An invalid size ({:d}) was provided for the string length prefix.".format('.'.join([__name__, cls.__name__]), ea, length, u", {!s}".format(utils.string.kwargs(strtype)) if strtype else '', length_t))

        # Convert the width and length into an actual size.
        size = width_t * length

        # Now we can combine them into the string type that IDA actually understands.
        res = (lengthtype[length_t] << idaapi.STRLYT_SHIFT) & idaapi.STRLYT_MASK
        res|= widthtype[width_t] & idaapi.STRWIDTH_MASK

        # If the size is larger than 0, then the user knows what they want and we
        # need to undefine that number of bytes first. The value of length_t is
        # added because we need to undefine the length prefix as well.
        if size > 0 and not type.is_unknown(ea):
            cb = cls.unknown(ea, length_t + size)
            if cb != length_t + size:
                raise E.DisassemblerError(u"{:s}.string({:#x}, {:d}{:s}) : Unable to undefine {:d} bytes for the requested string.".format('.'.join([__name__, cls.__name__]), ea, length, u", {:s}".format(utils.string.kwargs(strtype)) if strtype else '', length_t + size))

        # Make a string at the specified address of the suggested size with
        # the desired string type.
        ok = idaapi.make_ascii_string(ea, size and (size + length_t), res) if idaapi.__version__ < 7.0 else idaapi.create_strlit(ea, size and (size + length_t), res)
        if not ok:
            raise E.DisassemblerError(u"{:s}.string({:#x}, {:d}{:s}) : Unable to define the specified address as a string of the requested strtype {:#04x}.".format('.'.join([__name__, cls.__name__]), ea, length, u", {:s}".format(utils.string.kwargs(strtype)) if strtype else '', res))

        # In order to determine the correct length, we need to subtract the
        # length prefix the size, and divide the total by the character width.
        res = idaapi.get_item_size(ea) - length_t
        return get.string(ea, length=res // width_t)

    class integer(object):
        """
        This namespace used for applying various sized integer types to
        a particular address.

        This namespace is also aliased as ``database.set.i`` and can be used
        as follows::

            > database.set.i.uint8_t(ea)
            > database.set.i.uint64_t(ea)

        """
        @utils.multicase()
        def __new__(cls):
            '''Set the data at the current address to an integer.'''
            return cls(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        def __new__(cls, ea):
            '''Set the data at address `ea` to an integer of a type determined by its size.'''
            res = type.size(ea)
            return cls(ea, res)
        @utils.multicase(ea=six.integer_types, size=six.integer_types)
        def __new__(cls, ea, size):
            '''Set the data at the address `ea` to an integer of the specified `size`.'''
            res = set.unknown(ea, size)
            if not type.is_unknown(ea, size) or res < size:
                raise E.DisassemblerError(u"{:s}({:#x}, {:d}) : Unable to undefine {:d} byte{:s} for the integer.".format('.'.join([__name__, 'set', cls.__name__]), ea, size, '' if size == 1 else 's'))

            ok = set.data(ea, size)
            if not ok:
                raise E.DisassemblerError(u"{:s}({:#x}, {:d}) : Unable to set the specified address to an integer ({:d}-bit).".format('.'.join([__name__, 'set', cls.__name__]), ea, size, 8 * size))
            return get.signed(ea, size) if type.flags(ea, idaapi.FF_SIGN) else get.unsigned(ea, size)

        @utils.multicase()
        @classmethod
        def uint8_t(cls):
            '''Set the data at the current address to a uint8_t.'''
            return cls.uint8_t(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def uint8_t(cls, ea):
            '''Set the data at address `ea` to a uint8_t.'''
            res = set.unknown(ea, 1)
            if not type.is_unknown(ea, 1) or res < 1:
                raise E.DisassemblerError(u"{:s}.uint8_t({:#x}) : Unable to undefine {:d} byte for the integer.".format('.'.join([__name__, 'set', cls.__name__]), ea, 1))

            # Apply our data type after undefining it
            ok = set.data(ea, res, type=idaapi.FF_BYTE)
            if not ok:
                raise E.DisassemblerError(u"{:s}.uint8_t({:#x}) : Unable to set the specified address to an integer ({:d}-bit).".format('.'.join([__name__, 'set', cls.__name__]), ea, 8 * res))

            # Check if we need to flip the sign flag, and do it if necessary
            if type.flags(ea, idaapi.FF_SIGN):
                idaapi.toggle_sign(ea, 0)

            # Return our new size
            return get.unsigned(ea, res)
        @utils.multicase()
        @classmethod
        def sint8_t(cls):
            '''Set the data at the current address to a sint8_t.'''
            return cls.sint8_t(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def sint8_t(cls, ea):
            '''Set the data at address `ea` to a sint8_t.'''
            res = set.unknown(ea, 1)
            if not type.is_unknown(ea, 1) or res < 1:
                raise E.DisassemblerError(u"{:s}.sint8_t({:#x}) : Unable to undefine {:d} byte for the integer.".format('.'.join([__name__, 'set', cls.__name__]), ea, 1))

            # Apply our data type after undefining it
            ok = set.data(ea, res, type=idaapi.FF_BYTE)
            if not ok:
                raise E.DisassemblerError(u"{:s}.sint8_t({:#x}) : Unable to set the specified address to an integer ({:d}-bit).".format('.'.join([__name__, 'set', cls.__name__]), ea, 8 * res))

            # Check if we need to flip the sign flag, and do it if necessary
            if not type.flags(ea, idaapi.FF_SIGN):
                idaapi.toggle_sign(ea, 0)

            # Return our new size
            return get.signed(ea, res)
        byte = utils.alias(uint8_t, 'set.integer')

        @utils.multicase()
        @classmethod
        def uint16_t(cls):
            '''Set the data at the current address to a uint16_t.'''
            return cls.uint16_t(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def uint16_t(cls, ea):
            '''Set the data at address `ea` to a uint16_t.'''
            res = set.unknown(ea, 2)
            if not type.is_unknown(ea, 2) or res < 2:
                raise E.DisassemblerError(u"{:s}.uint16_t({:#x}) : Unable to undefine {:d} bytes for the integer.".format('.'.join([__name__, 'set', cls.__name__]), ea, 2))

            # Apply our data type after undefining it
            ok = set.data(ea, res, type=idaapi.FF_WORD)
            if not ok:
                raise E.DisassemblerError(u"{:s}.uint16_t({:#x}) : Unable to set the specified address to an integer ({:d}-bit).".format('.'.join([__name__, 'set', cls.__name__]), ea, 8 * res))

            # Check if we need to flip the sign flag, and do it if necessary
            if type.flags(ea, idaapi.FF_SIGN):
                idaapi.toggle_sign(ea, 0)

            # Return our new size
            return get.unsigned(ea, res)
        @utils.multicase()
        @classmethod
        def sint16_t(cls):
            '''Set the data at the current address to a sint16_t.'''
            return cls.sint16_t(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def sint16_t(cls, ea):
            '''Set the data at address `ea` to a sint16_t.'''
            res = set.unknown(ea, 2)
            if not type.is_unknown(ea, 2) or res < 2:
                raise E.DisassemblerError(u"{:s}.sint16_t({:#x}) : Unable to undefine {:d} bytes for the integer.".format('.'.join([__name__, 'set', cls.__name__]), ea, 2))

            # Apply our data type after undefining it
            ok = set.data(ea, res, type=idaapi.FF_WORD)
            if not ok:
                raise E.DisassemblerError(u"{:s}.sint16_t({:#x}) : Unable to set the specfied address to an integer ({:d}-bit).".format('.'.join([__name__, 'set', cls.__name__]), ea, 8 * res))

            # Check if we need to flip the sign flag, and do it if necessary
            if not type.flags(ea, idaapi.FF_SIGN):
                idaapi.toggle_sign(ea, 0)

            # Return our new size
            return get.signed(ea, res)
        word = utils.alias(uint16_t, 'set.integer')

        @utils.multicase()
        @classmethod
        def uint32_t(cls):
            '''Set the data at the current address to a uint32_t.'''
            return cls.uint32_t(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def uint32_t(cls, ea):
            '''Set the data at address `ea` to a uint32_t.'''
            FF_DWORD = idaapi.FF_DWORD if hasattr(idaapi, 'FF_DWORD') else idaapi.FF_DWRD

            # Undefine the data at the specified address
            res = set.unknown(ea, 4)
            if not type.is_unknown(ea, 4) or res < 4:
                raise E.DisassemblerError(u"{:s}.uint32_t({:#x}) : Unable to undefine {:d} bytes for the integer.".format('.'.join([__name__, 'set', cls.__name__]), ea, 4))

            # Apply our new data type after undefining it
            ok = set.data(ea, res, type=FF_DWORD)
            if not ok:
                raise E.DisassemblerError(u"{:s}.uint32_t({:#x}) : Unable to set the specified address to an integer ({:d}-bit).".format('.'.join([__name__, 'set', cls.__name__]), ea, 8 * res))

            # Check if we need to flip the sign flag, and do it if necessary
            if type.flags(ea, idaapi.FF_SIGN):
                idaapi.toggle_sign(ea, 0)

            # Now we can return our new size
            return get.unsigned(ea, res)
        @utils.multicase()
        @classmethod
        def sint32_t(cls):
            '''Set the data at the current address to a sint32_t.'''
            return cls.sint32_t(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def sint32_t(cls, ea):
            '''Set the data at address `ea` to a sint32_t.'''
            FF_DWORD = idaapi.FF_DWORD if hasattr(idaapi, 'FF_DWORD') else idaapi.FF_DWRD

            # Undefine the data at the specified address
            res = set.unknown(ea, 4)
            if not type.is_unknown(ea, 4) or res < 4:
                raise E.DisassemblerError(u"{:s}.uint32_t({:#x}) : Unable to undefine {:d} bytes for the integer.".format('.'.join([__name__, 'set', cls.__name__]), ea, 4))

            # Apply our new data type after undefining it
            ok = set.data(ea, res, type=FF_DWORD)
            if not ok:
                raise E.DisassemblerError(u"{:s}.uint32_t({:#x}) : Unable to set the specified address to an integer ({:d}-bit).".format('.'.join([__name__, 'set', cls.__name__]), ea, 8 * res))

            # Check if we need to flip the sign flag, and do it if necessary
            if not type.flags(ea, idaapi.FF_SIGN):
                idaapi.toggle_sign(ea, 0)

            # Now we can return our new size
            return get.signed(ea, res)
        dword = utils.alias(uint32_t, 'set.integer')

        @utils.multicase()
        @classmethod
        def uint64_t(cls):
            '''Set the data at the current address to a uint64_t.'''
            return cls.uint64_t(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def uint64_t(cls, ea):
            '''Set the data at address `ea` to a uint64_t.'''
            FF_QWORD = idaapi.FF_QWORD if hasattr(idaapi, 'FF_QWORD') else idaapi.FF_QWRD

            # Undefine the data at the specified address
            res = set.unknown(ea, 8)
            if not type.is_unknown(ea, 8) or res < 8:
                raise E.DisassemblerError(u"{:s}.uint64_t({:#x}) : Unable to undefine {:d} bytes for the integer.".format('.'.join([__name__, 'set', cls.__name__]), ea, 8))

            # Apply our new data type after undefining it
            ok = set.data(ea, res, type=FF_QWORD)
            if not ok:
                raise E.DisassemblerError(u"{:s}.uint64_t({:#x}) : Unable to set the specified address to an integer ({:d}-bit).".format('.'.join([__name__, 'set', cls.__name__]), ea, 8 * res))

            # Check if we need to flip the sign flag, and do it if necessary
            if type.flags(ea, idaapi.FF_SIGN):
                idaapi.toggle_sign(ea, 0)

            # Now we can return our new value since everything worked
            return get.unsigned(ea, res)
        @utils.multicase()
        @classmethod
        def sint64_t(cls):
            '''Set the data at the current address to a sint64_t.'''
            return cls.sint64_t(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def sint64_t(cls, ea):
            '''Set the data at address `ea` to a sint64_t.'''
            FF_QWORD = idaapi.FF_QWORD if hasattr(idaapi, 'FF_QWORD') else idaapi.FF_QWRD

            # Undefine the data at the specified address
            res = set.unknown(ea, 8)
            if not type.is_unknown(ea, 8) or res < 8:
                raise E.DisassemblerError(u"{:s}.uint64_t({:#x}) : Unable to undefine {:d} bytes for the integer.".format('.'.join([__name__, 'set', cls.__name__]), ea, 8))

            # Apply our new data type after undefining it
            ok = set.data(ea, res, type=FF_QWORD)
            if not ok:
                raise E.DisassemblerError(u"{:s}.uint64_t({:#x}) : Unable to set the specified address to an integer ({:d}-bit).".format('.'.join([__name__, 'set', cls.__name__]), ea, 8 * res))

            # Check if we need to flip the sign flag, and do it if necessary
            if not type.flags(ea, idaapi.FF_SIGN):
                idaapi.toggle_sign(ea, 0)

            # Now we can return our new value since everything worked
            return get.signed(ea, res)
        qword = utils.alias(uint64_t, 'set.integer')

        @utils.multicase()
        @classmethod
        def uint128_t(cls):
            '''Set the data at the current address to an uint128_t.'''
            return cls.uint128_t(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def uint128_t(cls, ea):
            '''Set the data at address `ea` to an uint128_t.'''
            FF_OWORD = idaapi.FF_OWORD if hasattr(idaapi, 'FF_OWORD') else idaapi.FF_OWRD

            # Undefine the data at the specified address
            res = set.unknown(ea, 16)
            if not type.is_unknown(ea, 16) or res < 16:
                raise E.DisassemblerError(u"{:s}.uint128_t({:#x}) : Unable to undefine {:d} bytes for the integer.".format('.'.join([__name__, 'set', cls.__name__]), ea, 16))

            # Apply our new data type after undefining it
            ok = set.data(ea, res, type=FF_OWORD)
            if not ok:
                raise E.DisassemblerError(u"{:s}.uint128_t({:#x}) : Unable to set the specified address to an integer ({:d}-bit).".format('.'.join([__name__, 'set', cls.__name__]), ea, 8 * res))

            # Check if we need to flip the sign flag, and do it if necessary
            if type.flags(ea, idaapi.FF_SIGN):
                idaapi.toggle_sign(ea, 0)

            # Now we can return our new value if we succeeded
            return get.signed(ea, res)
        @utils.multicase()
        @classmethod
        def sint128_t(cls):
            '''Set the data at the current address to a sint128_t.'''
            return cls.sint128_t(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def sint128_t(cls, ea):
            '''Set the data at address `ea` to an sint128_t.'''
            FF_OWORD = idaapi.FF_OWORD if hasattr(idaapi, 'FF_OWORD') else idaapi.FF_OWRD

            # Undefine the data at the specified address
            res = set.unknown(ea, 16)
            if not type.is_unknown(ea, 16) or res < 16:
                raise E.DisassemblerError(u"{:s}.uint128_t({:#x}) : Unable to undefine {:d} bytes for the integer.".format('.'.join([__name__, 'set', cls.__name__]), ea, 16))

            # Apply our new data type after undefining it
            ok = set.data(ea, res, type=FF_OWORD)
            if not ok:
                raise E.DisassemblerError(u"{:s}.uint128_t({:#x}) : Unable to set the specified address to an integer ({:d}-bit).".format('.'.join([__name__, 'set', cls.__name__]), ea, 8 * res))

            # Check if we need to flip the sign flag, and do it if necessary
            if not type.flags(ea, idaapi.FF_SIGN):
                idaapi.toggle_sign(ea, 0)

            # Now we can return our new value if we succeeded
            return get.signed(ea, res)
        oword = utils.alias(uint128_t, 'set.integer')

    i = integer # XXX: ns alias

    class float(object):
        """
        This namespace used for applying various sized floating-point types
        to a particular address.

        This namespace is aliased as ``database.set.f`` and can be used as
        follows::

            > database.set.f.single(ea)
            > database.set.f.double(ea)

        """
        @utils.multicase()
        def __new__(cls):
            '''Sets the data at the current address to an IEEE-754 floating-point number based on its size.'''
            return cls(ui.current.address())
        @utils.multicase()
        def __new__(cls, ea):
            '''Sets the data at address `ea` to an IEEE-754 floating-point number based on its size.'''
            size = type.size(ea)
            if size < 4 and type.is_unknown(ea, 4):
                logging.warning(u"{:s}({:#x}) : Promoting number at address {:#x} to 32-bit single due to item size ({:+d}) being less than the smallest available IEEE-754 number ({:+d}).".format('.'.join([__name__, 'set', cls.__name__]), ea, size, 4))
                return cls.single(ea)
            elif size == 4:
                return cls.single(ea)
            elif size == 8:
                return cls.double(ea)
            raise E.InvalidTypeOrValueError(u"{:s}({:#x}) : Unable to determine the type of floating-point number for the item's size ({:+#x}).".format('.'.join([__name__, 'set', cls.__name__]), ea, size))

        @utils.multicase()
        @classmethod
        def single(cls):
            '''Set the data at the current address to an IEEE-754 single'''
            return cls.single(ui.current.address())
        @utils.multicase()
        @classmethod
        def single(cls, ea):
            '''Set the data at address `ea` to an IEEE-754 single.'''
            res = set.unknown(ea, 4)
            if not type.is_unknown(ea, 4) or res < 4:
                raise E.DisassemblerError(u"{:s}.single({:#x}) : Unable to undefine {:d} bytes for the float.".format('.'.join([__name__, 'set', cls.__name__]), ea, 4))

            # Apply our data type after undefining it
            ok = set.data(ea, res, type=idaapi.FF_FLOAT & 0xf0000000)
            if not ok:
                raise E.DisassemblerError(u"{:s}.single({:#x}) : Unable to assign a single to the specified address.".format('.'.join([__name__, 'set', cls.__name__]), ea))

            # Return our new value
            return get.float.single(ea)

        @utils.multicase()
        @classmethod
        def double(cls):
            '''Set the data at the current address to an IEEE-754 double'''
            return cls.double(ui.current.address())
        @utils.multicase()
        @classmethod
        def double(cls, ea):
            '''Set the data at address `ea` to an IEEE-754 double.'''
            res = set.unknown(ea, 8)
            if not type.is_unknown(ea, 8) or res < 8:
                raise E.DisassemblerError(u"{:s}.double({:#x}) : Unable to undefine {:d} bytes for the float.".format('.'.join([__name__, 'set', cls.__name__]), ea, 8))

            # Apply our data type after undefining it
            ok = set.data(ea, res, type=idaapi.FF_DOUBLE & 0xf0000000)
            if not ok:
                raise E.DisassemblerError(u"{:s}.double({:#x}) : Unable to assign a double to the specified address.".format('.'.join([__name__, 'set', cls.__name__]), ea))

            # Return our new value
            return get.float.double(ea)

    f = float   # XXX: ns alias

    @utils.multicase(type=_structure.structure_t)
    @classmethod
    def structure(cls, type):
        '''Set the data at the current address to the structure_t specified by `type`.'''
        return cls.structure(ui.current.address(), type)
    @utils.multicase(ea=six.integer_types, type=_structure.structure_t)
    @classmethod
    def structure(cls, ea, type):
        '''Set the data at address `ea` to the structure_t specified by `type`.'''
        ok = cls.data(ea, type.size, type=type)
        if not ok:
            raise E.DisassemblerError(u"{:s}.structure({:#x}, {!r}) : Unable to define the specified address as a structure.".format('.'.join([__name__, cls.__name__]), ea, type))
        return get.structure(ea, structure=type)

    struc = struct = utils.alias(structure, 'set')

    @utils.multicase()
    @classmethod
    def array(cls, type):
        '''Set the data at the current address to an array of the specified `type`.'''
        return cls.array(ui.current.address(), type)
    @utils.multicase(length=six.integer_types)
    @classmethod
    def array(cls, type, length):
        '''Set the data at the current address to an array with the specified `length` and `type`.'''
        return cls.array(ui.current.address(), type, length)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def array(cls, ea, type):
        '''Set the data at the address `ea` to an array of the specified `type`.'''
        type, length = type if isinstance(type, builtins.list) else (type, 1)
        return cls.array(ea, type, length)
    @utils.multicase(ea=six.integer_types, length=six.integer_types)
    @classmethod
    def array(cls, ea, type, length):
        '''Set the data at the address `ea` to an array with the specified `length` and `type`.'''

        # if the type is already specifying a list, then combine it with
        # the specified length
        if isinstance(type, list):
            t, l = type
            realtype, reallength = [t, l * length], l * length

        # otherwise, promote it into an array
        else:
            realtype, reallength = [type, length], length

        # now we can figure out its IDA type
        flags, typeid, nbytes = interface.typemap.resolve(realtype)
        ok = idaapi.create_data(ea, flags, nbytes, typeid)
        if not ok:
            raise E.DisassemblerError(u"{:s}.array({:#x}, {!r}, {:d}) : Unable to define the specified address as an array.".format('.'.join([__name__, cls.__name__]), ea, type, length))
        return get.array(ea, length=reallength)

class get(object):
    """
    This namespace used to fetch and decode the data from the database
    at a given address. This allows one to interpret the semantics of
    parts of the database and then perform an action based on what was
    decoded. This includes standard functions for reading integers of
    different sizes, decoding structures, and even reading of arrays
    from the database.

    In order to decode various things out of the database, some of the
    following examples can be used::

        > res = database.get.signed()
        > res = database.get.unsigned(ea, 8, byteorder='big')
        > res = database.get.array(ea)
        > res = database.get.array(length=42)
        > res = database.get.structure(ea)
        > res = database.get.structure(ea, structure=structure.by('mystructure'))

    """
    @utils.multicase()
    @classmethod
    def info(cls):
        '''Return the typeinfo at the current address as an ``idaapi.tinfo_t``.'''
        return cls.info(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def info(cls, ea):
        '''Return the typeinfo at the address `ea` as an ``idaapi.tinfo_t``.'''
        return type(ea)
    typeinfo = utils.alias(info, 'get')

    @utils.multicase()
    @classmethod
    def unsigned(cls, **byteorder):
        '''Read an unsigned integer from the current address.'''
        ea = ui.current.address()
        return cls.unsigned(ea, type.size(ea), **byteorder)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def unsigned(cls, ea, **byteorder):
        '''Read an unsigned integer from the address `ea` using the size defined in the database.'''
        return cls.unsigned(ea, type.size(ea), **byteorder)
    @utils.multicase(ea=six.integer_types, size=six.integer_types)
    @classmethod
    def unsigned(cls, ea, size, **byteorder):
        """Read an unsigned integer from the address `ea` with the specified `size`.

        If `byteorder` is 'big' then read in big-endian form.
        If `byteorder` is 'little' then read in little-endian form.

        The default value of `byteorder` is the same as specified by the database architecture.
        """
        data = read(ea, size)
        endian = byteorder.get('order', None) or byteorder.get('byteorder', config.byteorder())
        if endian.lower().startswith('little'):
            data = data[::-1]
        return functools.reduce(lambda agg, byte: agg << 8 | byte, bytearray(data), 0)

    @utils.multicase()
    @classmethod
    def signed(cls, **byteorder):
        '''Read a signed integer from the current address.'''
        ea = ui.current.address()
        return cls.signed(ea, type.size(ea), **byteorder)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def signed(cls, ea, **byteorder):
        '''Read a signed integer from the address `ea` using the size defined in the database.'''
        return cls.signed(ea, type.size(ea), **byteorder)
    @utils.multicase(ea=six.integer_types, size=six.integer_types)
    @classmethod
    def signed(cls, ea, size, **byteorder):
        """Read a signed integer from the address `ea` with the specified `size`.

        If `byteorder` is 'big' then read in big-endian form.
        If `byteorder` is 'little' then read in little-endian form.

        The default value of `byteorder` is the same as specified by the database architecture.
        """
        bits = size*8
        sf = (2**bits)>>1
        res = cls.unsigned(ea, size, **byteorder)
        return (res - (2**bits)) if res&sf else res

    class integer(object):
        """
        This namespace contains the different ISO standard integer types that
        can be used to read integers out of the database.

        This namespace is also aliased as ``database.get.i`` and can be used
        like in the following examples::

            > res = database.get.i.uint32_t()
            > res = database.get.i.sint64_t(ea)
            > res = database.get.i.uint8_t(ea)

        """
        @utils.multicase()
        def __new__(cls, **byteorder):
            '''Read an integer from the current address.'''
            return get.signed(**byteorder) if type.flags(ui.current.address(), idaapi.FF_SIGN) else get.unsigned(**byteorder)
        @utils.multicase(ea=six.integer_types)
        def __new__(cls, ea, **byteorder):
            '''Read an integer from the address `ea`.'''
            return get.signed(ea, **byteorder) if type.flags(ea, idaapi.FF_SIGN) else get.unsigned(ea, **byteorder)
        @utils.multicase(ea=six.integer_types, size=six.integer_types)
        def __new__(cls, ea, size, **byteorder):
            '''Read an integer of the specified `size` from the address `ea`.'''
            return get.signed(ea, size, **byteorder) if type.flags(ea, idaapi.FF_SIGN) else get.unsigned(ea, size, **byteorder)

        @utils.multicase()
        @classmethod
        def uint8_t(cls, **byteorder):
            '''Read a uint8_t from the current address.'''
            return get.unsigned(ui.current.address(), 1, **byteorder)
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def uint8_t(cls, ea, **byteorder):
            '''Read a uint8_t from the address `ea`.'''
            return get.unsigned(ea, 1, **byteorder)
        @utils.multicase()
        @classmethod
        def sint8_t(cls, **byteorder):
            '''Read a sint8_t from the current address.'''
            return get.signed(ui.current.address(), 1, **byteorder)
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def sint8_t(cls, ea, **byteorder):
            '''Read a sint8_t from the address `ea`.'''
            return get.signed(ea, 1, **byteorder)
        byte = utils.alias(uint8_t, 'get.integer')

        @utils.multicase()
        @classmethod
        def uint16_t(cls, **byteorder):
            '''Read a uint16_t from the current address.'''
            return get.unsigned(ui.current.address(), 2, **byteorder)
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def uint16_t(cls, ea, **byteorder):
            '''Read a uint16_t from the address `ea`.'''
            return get.unsigned(ea, 2, **byteorder)
        @utils.multicase()
        @classmethod
        def sint16_t(cls, **byteorder):
            '''Read a sint16_t from the current address.'''
            return get.signed(ui.current.address(), 2, **byteorder)
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def sint16_t(cls, ea, **byteorder):
            '''Read a sint16_t from the address `ea`.'''
            return get.signed(ea, 2, **byteorder)
        word = utils.alias(uint16_t, 'get.integer')

        @utils.multicase()
        @classmethod
        def uint32_t(cls, **byteorder):
            '''Read a uint32_t from the current address.'''
            return get.unsigned(ui.current.address(), 4, **byteorder)
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def uint32_t(cls, ea, **byteorder):
            '''Read a uint32_t from the address `ea`.'''
            return get.unsigned(ea, 4, **byteorder)
        @utils.multicase()
        @classmethod
        def sint32_t(cls, **byteorder):
            '''Read a sint32_t from the current address.'''
            return get.signed(ui.current.address(), 4, **byteorder)
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def sint32_t(cls, ea, **byteorder):
            '''Read a sint32_t from the address `ea`.'''
            return get.signed(ea, 4, **byteorder)
        dword = utils.alias(uint32_t, 'get.integer')

        @utils.multicase()
        @classmethod
        def uint64_t(cls, **byteorder):
            '''Read a uint64_t from the current address.'''
            return get.unsigned(ui.current.address(), 8, **byteorder)
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def uint64_t(cls, ea, **byteorder):
            '''Read a uint64_t from the address `ea`.'''
            return get.unsigned(ea, 8, **byteorder)
        @utils.multicase()
        @classmethod
        def sint64_t(cls, **byteorder):
            '''Read a sint64_t from the current address.'''
            return get.signed(ui.current.address(), 8, **byteorder)
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def sint64_t(cls, ea, **byteorder):
            '''Read a sint64_t from the address `ea`.'''
            return get.signed(ea, 8, **byteorder)
        qword = utils.alias(uint64_t, 'get.integer')

        @utils.multicase()
        @classmethod
        def uint128_t(cls, **byteorder):
            '''Read a uint128_t from the current address.'''
            return get.unsigned(ui.current.address(), 16)
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def uint128_t(cls, ea, **byteorder):
            '''Read a uint128_t from the address `ea`.'''
            return get.unsigned(ea, 16, **byteorder)
        @utils.multicase()
        @classmethod
        def sint128_t(cls, **byteorder):
            '''Read a sint128_t from the current address.'''
            return get.signed(ui.current.address(), 16)
        @utils.multicase(ea=six.integer_types)
        @classmethod
        def sint128_t(cls, ea, **byteorder):
            '''Read a sint128_t from the address `ea`.'''
            return get.signed(ea, 16, **byteorder)
        oword = utils.alias(uint128_t, 'get.integer')

    i = integer # XXX: ns alias

    class float(object):
        """
        This namespace contains a number of functions for fetching floating
        point numbers out of the database. These floating-point numbers are
        encoded according to the IEEE-754 specification.

        This namespace is also aliased as ``database.get.f`` and can be used
        as in the following examples::

            > res = database.get.f.half()
            > res = database.get.f.single(ea)
            > res = database.get.f.double(ea)

        If one needs to describe a non-standard encoding for a floating-point
        number, one can use the ``database.float`` function. This function
        takes a tuple representing the number of bits for the different
        components of a floating-point number. This can be used as in the
        following for reading a floating-point "half" from the database::

            > res = database.get.float(components=(10, 5, 1))

        This specifies 10-bits for the mantissa, 5 for the exponent, and 1
        bit for the signed flag. This allows one to specify arbitrary
        encodings for different floating-point numbers.
        """

        @utils.multicase()
        def __new__(cls, **byteorder):
            '''Read a floating-number from the current address using the number type that matches its size.'''
            return cls(ui.current.address(), **byteorder)
        @utils.multicase(ea=six.integer_types)
        def __new__(cls, ea, **byteorder):
            '''Read a floating-number at the address `ea` using the number type that matches its size.'''
            size = type.size(ea)
            if size == 2:
                return cls.half(ea, **byteorder)
            elif size == 4:
                return cls.single(ea, **byteorder)
            elif size == 8:
                return cls.double(ea, **byteorder)
            elif size > 8:
                logging.warning(u"{:s}({:#x}) : Demoting size ({:+d}) for floating-point number at {:#x} down to largest available IEEE-754 number ({:+d}).".format('.'.join([__name__, 'get', cls.__name__]), size, ea, 8))
                return cls.double(ea, **byteorder)
            raise E.InvalidTypeOrValueError(u"{:s}({:#x}) : Unable to determine the type of floating-point number for the item's size ({:+#x}).".format('.'.join([__name__, 'get', cls.__name__]), ea, size))

        @utils.multicase(components=tuple)
        def __new__(cls, components, **byteorder):
            '''Read a floating-point number at the current address encoded with the specified `components`.'''
            return cls(ui.current.address(), components, **byteorder)
        @utils.multicase(ea=six.integer_types, components=tuple)
        def __new__(cls, ea, components, **byteorder):
            """Read a floating-point number at the address `ea` that is encoded with the specified `components`.

            The `components` parameter is a tuple (mantissa, exponent, sign) representing the number of bits for each component of the floating-point number.
            If `byteorder` is 'big' then read in big-endian form.
            If `byteorder` is 'little' then read in little-endian form.

            The default value of `byteorder` is the same as specified by the database architecture.
            """
            cb = sum(components) // 8

            # Read our data from the database as an integer, as we'll use this
            # to decode our individual components.
            integer = get.unsigned(ea, cb, **byteorder)

            # Unpack the components the user gave us.
            fraction, exponent, sign = components

            # Use the components to decode the floating point number
            try:
                res = utils.float_of_integer(integer, fraction, exponent, sign)

            except ValueError as message:
                raise ValueError(u"{:s}({:#x}, {!s}) : {!s}".format('.'.join([__name__, cls.__name__]), ea, components, message))

            return res

        @utils.multicase()
        @classmethod
        def half(cls, **byteorder):
            '''Read a half from the current address.'''
            return cls.half(ui.current.address(), **byteorder)
        @utils.multicase()
        @classmethod
        def half(cls, ea, **byteorder):
            '''Read a half from the address `ea`.'''
            bits = 10, 5, 1
            return cls(ea, bits, **byteorder)

        @utils.multicase()
        @classmethod
        def single(cls, **byteorder):
            '''Read a single from the current address.'''
            return cls.single(ui.current.address(), **byteorder)
        @utils.multicase()
        @classmethod
        def single(cls, ea, **byteorder):
            '''Read a single from the address `ea`.'''
            bits = 23, 8, 1
            return cls(ea, bits, **byteorder)

        @utils.multicase()
        @classmethod
        def double(cls, **byteorder):
            '''Read a double from the current address.'''
            return cls.double(ui.current.address(), **byteorder)
        @utils.multicase()
        @classmethod
        def double(cls, ea, **byteorder):
            '''Read a double from the address `ea`.'''
            bits = 52, 11, 1
            return cls(ea, bits, **byteorder)

    f = float   # XXX: ns alias

    @utils.multicase()
    @classmethod
    def array(cls, **length):
        '''Return the values of the array at the current address.'''
        return cls.array(ui.current.address(), **length)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def array(cls, ea, **length):
        """Return the values of the array at the address specified by `ea`.

        If the integer `length` is defined, then use it as the number of elements for the array.
        If a pythonic type is passed to `type`, then use it for the element type of the array when decoding.
        """
        ea = interface.address.within(ea)
        FF_STRUCT = idaapi.FF_STRUCT if hasattr(idaapi, 'FF_STRUCT') else idaapi.FF_STRU
        FF_STRLIT = idaapi.FF_STRLIT if hasattr(idaapi, 'FF_STRLIT') else idaapi.FF_ASCI

        def numeric_lookup_tables():
            '''
            This closure is responsible for returning the lookup tables to map IDA types to
            either lengths or array typecodes which will be used for decoding the elements
            of the array.
            '''

            # This numerics table is responsible for mapping an idaapi.DT_TYPE
            # type to a typecode for the _array class.
            numerics = {
                idaapi.FF_BYTE : utils.get_array_typecode(1),
                idaapi.FF_WORD : utils.get_array_typecode(2),
                idaapi.FF_DWORD if hasattr(idaapi, 'FF_DWORD') else idaapi.FF_DWRD : utils.get_array_typecode(4),
                idaapi.FF_FLOAT : 'f',
                idaapi.FF_DOUBLE : 'd',
            }

            # Some 32-bit versions of python might not have array.array('Q')
            # and some versions of IDA also might not have FF_QWORD..
            try:
                _array.array(utils.get_array_typecode(8))
                numerics[idaapi.FF_QWORD if hasattr(idaapi, 'FF_QWORD') else idaapi.FF_QWRD] = utils.get_array_typecode(8)
            except (AttributeError, ValueError):
                pass

            # This long-numerics table is a mapping-type for converting an
            # idaapi.DT_TYPE to a length. This way we can manually read the
            # elements of the array into a list that we can return to the user.
            lnumerics = {
                idaapi.FF_BYTE : 1,
                idaapi.FF_WORD : 2,
                idaapi.FF_DWORD if hasattr(idaapi, 'FF_DWORD') else idaapi.FF_DWRD : 4,
                idaapi.FF_FLOAT : 4,
                idaapi.FF_DOUBLE : 8,
            }

            # If we have FF_QWORD defined but it cannot be represented by the
            # _array class, then we'll need to add its size to our long-numerics
            # table so that we can still read its elements manually.
            if any(hasattr(idaapi, name) for name in {'FF_QWRD', 'FF_QWORD'}):
                name = builtins.next(name for name in {'FF_QWRD', 'FF_QWORD'} if hasattr(idaapi, name))
                value = getattr(idaapi, name)
                if value not in numerics:
                    lnumerics[value] = 8
                pass

            # FF_OWORD, FF_YWORD and FF_ZWORD might not exist in older versions
            # of IDA, so try to add them to our long-numerics "softly".
            try:
                lnumerics[idaapi.FF_QWORD if hasattr(idaapi, 'FF_QWORD') else idaapi.FF_QWRD] = 8
                lnumerics[idaapi.FF_OWORD if hasattr(idaapi, 'FF_OWORD') else idaapi.FF_OWRD] = 16
                lnumerics[idaapi.FF_YWORD if hasattr(idaapi, 'FF_YWORD') else idaapi.FF_YWRD] = 32
                lnumerics[idaapi.FF_ZWORD if hasattr(idaapi, 'FF_ZWORD') else idaapi.FF_ZWRD] = 64
            except AttributeError:
                pass

            # Depending on the version of IDAPython, some of IDA's flags (FF_*) can
            # be signed or unsigned. Since we're explicitly testing for them by using
            # container membership, we'll need to ensure that they're unsigned when
            # storing them into their lookup tables. This way our membership tests
            # will actually work when determining the types to use.
            numerics = { idaapi.as_uint32(ff) : typecode for ff, typecode in numerics.items() }
            lnumerics = { idaapi.as_uint32(ff) : length for ff, length in lnumerics.items() }

            # Now they're safe to return to the caller for people to use.
            return numerics, lnumerics

        def decode_array(ea, T, count, numerics, lnumerics):
            '''
            This closure is responsible for decoding an array from the given address
            using the provided type (T) and count for the number of elements. The
            `numerics` and `lnumerics` tables are used for looking up the typecode
            or length given a DT_TYPE.
            '''

            # If the array has a refinfo_t at its address or the signed flag is
            # set, then we need to lowercase the typecode to get signed or
            # relative values from the array.
            if _instruction.ops_refinfo(ea) or F & idaapi.FF_SIGN:

                # FIXME: If the user has set the signed flag, then we need to return
                #        the negative values that are displayed instead of just
                #        decoding the array's integers as signed.
                typecode = numerics[T].lower()

            # Otherwise, we can simply lookup the typecode and use that one.
            else:
                typecode = numerics[T]

            # Create an _array using the typecode that we determined so that it can
            # be decoded and then returned to the caller.
            res = _array.array(typecode)

            # If our _array's itemsize doesn't match the element size that we expected,
            # then we need to warn the user that something fucked up and that we're
            # hijacking the array decoding with our own hardcoded unsigned length.
            cb = lnumerics[T]
            if res.itemsize != cb:
                logging.warning(u"{:s}.array({:#x}{:s}) : Refusing to decode array at address {:#x} using the array size ({:+d}) identified for DT_TYPE ({:#x}) due to the size of the DT_TYPE ({:#x}) not corresponding to the desired element size ({:+d}).".format('.'.join([__name__, cls.__name__]), ea, u", {:s}".format(utils.string.kwargs(length)) if length else '', ea, res.itemsize, T, T, cb))

                # Reconstruct the array but with the expected element size.
                try:
                    res = _array.array(utils.get_array_typecode(cb, 1))

                # If we can't use the typecode determined by the element size, then
                # just assume that the elements are just individual bytes.
                except ValueError:
                    res = _array.array(utils.get_array_typecode(1))

            # Get the number of elements for our array, and use it to read our data
            # from the database. Then we can use the data to initialize the _array
            # that we're going to return to the user.
            data = read(ea, count * cb)
            res.fromstring(data) if sys.version_info.major < 3 else res.frombytes(data)

            # Validate the _array's length so that we can warn the user if it's wrong.
            if len(res) != count:
                logging.warning(u"{:s}.array({:#x}{:s}) : The decoded array length ({:d}) is different from the expected length ({:d}).".format('.'.join([__name__, cls.__name__]), ea, u", {:s}".format(utils.string.kwargs(length)) if length else '', len(res), count))
            return res

        # If the "type" parameter was provided, then resolve that type into the
        # flags and DT_TYPE that we will need.
        if 'type' in length:
            F, tid, total = interface.typemap.resolve(length['type'])

            # If we were given an array in the "type" parameter, then reassign
            # that back into the "length" parameter so it can be used later.
            if isinstance(length['type'], builtins.list):
                _, count = length['type']
                length.setdefault('length', count)

        # Otherwise we extract the flags and DT_TYPE directly from the address.
        else:
            F, total = type.flags(ea), idaapi.get_item_size(ea)
            tid = type.structure.id(ea) if type.flags(ea, idaapi.DT_TYPE) == FF_STRUCT else idaapi.BADADDR

        # Set the array's length if it hasn't been determined yet.
        length.setdefault('length', type.array.length(ea))

        # Now that we have the flags and the type, we can use it to determine
        # how we need to decode the array. Since there's no utilities or
        # anything for performing these conversions in minsc, we'll need to
        # handle all of the element types ourselves by explicitly handling
        # each supported case.
        T = idaapi.as_uint32(F & idaapi.DT_TYPE)
        numerics, lnumerics = numeric_lookup_tables()

        # If this is a string-literal, then we need to figure out the element
        # size in order to figure out which character width to use.
        if T in {FF_STRLIT}:
            elesize = idaapi.get_full_data_elsize(ea, F)

            # Python's "u" typecode for their _array can actually change sizes. So
            # we have no choice here other than to just use the integer typecodes
            # for both 16-bit and 32-bit wide-character strings.
            strings = { 1: 'c', 2: utils.get_array_typecode(2), 4: utils.get_array_typecode(4) }
            t = strings[elesize]

            # Now we need to fix the value for T so that it corresponds to its
            # element size by checking the lnumerics array. Afterwards we can
            # simply decode it as normal.
            T = builtins.next(ff for ff, size in lnumerics.items() if size == elesize)
            return decode_array(ea, T, length['length'], numerics, lnumerics)

        # If we found a structure at this address, then we'll simply take its
        # length and use it to create a structure for each individual element.
        elif T in {FF_STRUCT}:
            cb = _structure.size(tid)
            # FIXME: this math doesn't work with dynamically sized structures (of course)
            count = length.get('length', math.trunc(math.ceil(float(total) / cb)))
            return [ cls.structure(ea + index * cb, id=tid) for index in builtins.range(count) ]

        # If the DT_TYPE was found in our numerics dictionary, then we're able
        # to use a native _array with the decode_array closure.
        elif T in numerics:
            return decode_array(ea, T, length['length'], numerics, lnumerics)

        # If the DT_TYPE was found in our lnumerics (long) dictionary, then use
        # that to figure out the element size, and read each integer as a list
        # due there being no native _array type.
        elif T in lnumerics:
            cb, total = lnumerics[T], idaapi.get_item_size(ea)
            # FIXME: Instead of returning the signed version of an integer, we
            #        need to return IDA's signed representation of the integer
            #        so that it directly corresponds to the user's view.
            Fgetinteger = get.signed if F & idaapi.FF_SIGN == idaapi.FF_SIGN else get.unsigned
            count = length.get('length', math.trunc(math.ceil(float(total) / cb)))
            return [ Fgetinteger(ea + index * cb, cb) for index in builtins.range(count) ]

        # Otherwise the DT_TYPE is unsupported, and we don't have a clue on how
        # this should be properly decoded...
        raise E.UnsupportedCapability(u"{:s}.array({:#x}{:s}) : Unknown DT_TYPE found in flags at address {:#x}. The flags {:#x} have the `idaapi.DT_TYPE` as {:#x}.".format('.'.join([__name__, cls.__name__]), ea, u", {:s}".format(utils.string.kwargs(length)) if length else '', ea, F, T))

    @utils.multicase()
    @classmethod
    def string(cls, **length):
        '''Return the array at the current address as a string.'''
        return cls.string(ui.current.address(), **length)
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def string(cls, ea, **length):
        """Return the array at the address specified by `ea` as a string.

        If an integer `length` is provided, then use it explicitly as the string's length when reading.
        If an integer `strtype` is provided, then use it as the string's character width when reading.
        If a tuple `strtype` is specified, then the first item is the character width and the second is the size of the length prefix when reading.
        """

        # For older versions of IDA, we get the strtype from the opinfo
        if idaapi.__version__ < 7.0:
            res = address.head(ea)
            ti, F = idaapi.opinfo_t(), type.flags(res)
            strtype = ti.strtype if idaapi.get_opinfo(res, 0, F, ti) else idaapi.BADADDR

            # and cast the result from idaapi.get_str_type_code to an integer
            get_str_type_code = utils.fcompose(idaapi.get_str_type_code, six.byte2int)

        # Fetch the string type at the given address using the newer API
        else:
            strtype = idaapi.get_str_type(address.head(ea))
            get_str_type_code = idaapi.get_str_type_code

        # If a strtype was provided in the parameters, then convert it into a proper
        # string typecode so that the logic which follows will still work.
        if any(item in length for item in ['strtype', 'type']):
            widthtype = {1: idaapi.STRWIDTH_1B, 2: idaapi.STRWIDTH_2B, 4: idaapi.STRWIDTH_4B}
            lengthtype = {0: idaapi.STRLYT_TERMCHR, 1: idaapi.STRLYT_PASCAL1, 2: idaapi.STRLYT_PASCAL2, 4: idaapi.STRLYT_PASCAL4}

            # Extract the strtype that the user gave us whilst ensuring that we remove
            # the items out of the parameters since we later pass them to `get.array`.
            res = builtins.next((length.pop(item) for item in ['strtype', 'type'] if item in length))
            width_t, length_t = res if isinstance(res, (builtins.list, builtins.tuple)) else (res, 0)

            # Now that we've unpacked the string width and length prefix size from the
            # parameter, we can recombine them into a strtype code.
            strtype = (lengthtype[length_t] << idaapi.STRLYT_SHIFT) & idaapi.STRLYT_MASK
            strtype|= widthtype[width_t] & idaapi.STRWIDTH_MASK

            # Since the user gave us an explicit type, we need to update the keywords
            # which get passed to `get.array` so that each element is of the correct width.
            length['type'] = int, width_t

        # If no string was found, then try to treat it as a plain old array
        # XXX: idaapi.get_str_type() seems to return 0xffffffff on failure instead of idaapi.BADADDR
        if strtype in {idaapi.BADADDR, 0xffffffff}:
            res = cls.array(ea, **length)

            # It ended up not being an array type, and was probably a structure. So,
            # we can only complain to the user about it and let them sort it out.
            if not isinstance(res, _array.array):
                raise E.InvalidTypeOrValueError(u"{:s}.string({:#x}{:s}) : The data at address {:#x} cannot be read as an integer array and thus is unable to be converted to a string.".format('.'.join([__name__, cls.__name__]), ea, u", {:s}".format(utils.string.kwargs(length)) if length else '', ea))

            # Warn the user what we're doing before we start figuring out
            # the element size of the string.
            logging.warning(u"{:s}.string({:#x}{:s}) : Unable to automatically determine the string type code for address {:#x}. Reading it as an integer array and converting it to a string instead.".format('.'.join([__name__, cls.__name__]), ea, u", {:s}".format(utils.string.kwargs(length)) if length else '', ea))

            # We can't figure out the shift.. So, since that's a dead end we
            # have to assume that the terminator is a null byte.
            sentinels, sl = '\0', idaapi.STRLYT_TERMCHR << idaapi.STRLYT_SHIFT

            # However, we can still figure out the character width from the itemsize.
            sizelookup = {
                1: idaapi.STRWIDTH_1B,
                2: idaapi.STRWIDTH_2B,
                4: idaapi.STRWIDTH_4B,
            }

            # But we still need to make sure that the itemsize is something we support.
            if not operator.contains(sizelookup, res.itemsize):
                raise E.UnsupportedCapability(u"{:s}.string({:#x}{:s}) : Unsupported character width ({:d}) found for string in the array at address {:#x}.".format('.'.join([__name__, cls.__name__]), ea, u", {:s}".format(utils.string.kwargs(length)) if length else '', res.itemsize, ea))

            sw = sizelookup[res.itemsize]

        # Otherwise we can extract the string's characteristics directly from the strtype code.
        else:
            # Get the string encoding (not actually used)
            encoding = idaapi.get_str_encoding_idx(strtype)

            # Get the terminal characters that can terminate the string
            sentinels = idaapi.get_str_term1(strtype) + idaapi.get_str_term2(strtype)

            # Extract the fields out of the string type code
            res = get_str_type_code(strtype)
            sl, sw = res & idaapi.STRLYT_MASK, res & idaapi.STRWIDTH_MASK

        # Figure out the STRLYT field
        if sl == idaapi.STRLYT_TERMCHR << idaapi.STRLYT_SHIFT:
            shift, fterminate = 0, operator.methodcaller('rstrip', sentinels)
        elif sl == idaapi.STRLYT_PASCAL1 << idaapi.STRLYT_SHIFT:
            shift, fterminate = 1, utils.fidentity
        elif sl == idaapi.STRLYT_PASCAL2 << idaapi.STRLYT_SHIFT:
            shift, fterminate = 2, utils.fidentity
        elif sl == idaapi.STRLYT_PASCAL4 << idaapi.STRLYT_SHIFT:
            shift, fterminate = 4, utils.fidentity
        else:
            raise E.UnsupportedCapability(u"{:s}.string({:#x}{:s}) : Unsupported STRLYT({:d}) found in string at address {:#x}.".format('.'.join([__name__, cls.__name__]), ea, u", {:s}".format(utils.string.kwargs(length)) if length else '', sl, ea))

        # Figure out the STRWIDTH field
        if sw == idaapi.STRWIDTH_1B:
            fdecode = operator.methodcaller('decode', 'utf-8', 'replace')
        elif sw == idaapi.STRWIDTH_2B:
            fdecode = operator.methodcaller('decode', 'utf-16', 'replace')
        elif sw == idaapi.STRWIDTH_4B:
            fdecode = operator.methodcaller('decode', 'utf-32', 'replace')
        else:
            raise E.UnsupportedCapability(u"{:s}.string({:#x}{:s}) : Unsupported STRWIDTH({:d}) found in string at address {:#x}.".format('.'.join([__name__, cls.__name__]), ea, u", {:s}".format(utils.string.kwargs(length)) if length else '', sw, ea))

        # Read the pascal length if one was specified in the string type code
        if shift:
            res = cls.unsigned(ea, shift)
            length.setdefault('length', res)

        # Now we can read the string, and convert it to some bytes to decode
        res = cls.array(ea + shift, **length)
        data = res.tostring() if sys.version_info.major < 3 else res.tobytes()

        # ..and then process it.
        return fterminate(fdecode(data))
    @utils.multicase()
    @classmethod
    def structure(cls):
        '''Return the ``structure_t`` at the current address.'''
        return cls.structure(ui.current.address())
    @utils.multicase(ea=six.integer_types)
    @classmethod
    def structure(cls, ea, **structure):
        """Return the ``structure_t`` at address `ea` as a dict of ctypes.

        If the `structure` argument is specified, then use that specific structure type.
        """
        ea = interface.address.within(ea)

        key = builtins.next((k for k in ['structure', 'struct', 'struc', 'sid', 'id'] if k in structure), None)
        if key is None:
            sid = type.structure.id(ea)
        else:
            res = structure.get(key, None)
            sid = res.id if isinstance(res, _structure.structure_t) else res

        # FIXME: add support for string types
        # FIXME: consolidate this conversion into interface or something
        st = _structure.by_identifier(sid, offset=ea)
        typelookup = {
            (int, -1) : ctypes.c_int8,   (int, 1) : ctypes.c_uint8,
            (int, -2) : ctypes.c_int16,  (int, 2) : ctypes.c_uint16,
            (int, -4) : ctypes.c_int32,  (int, 4) : ctypes.c_uint32,
            (int, -8) : ctypes.c_int64,  (int, 8) : ctypes.c_uint64,
            (float, 4) : ctypes.c_float, (float, 8) : ctypes.c_double,
        }

        res = {}
        for m in st.members:
            t, val = m.type, read(m.offset, m.size) or ''

            # try and lookup the individual type + size
            try:
                ct = typelookup[t]

            # either we don't support it, or it's an array
            except (TypeError, KeyError):

                # if it's an array, then unpack the count. otherwise we'll use a
                # count of -1 so that we can tell ctypes to not actually create
                # the type as an array. we can't use 0 here because ctypes
                # recognizes 0-length arrays.
                ty, count = t if isinstance(t, builtins.list) else (t, -1)

                # check that we really are handling an array, and lookup its type
                # to build a ctype with its count
                if isinstance(t, builtins.list) and operator.contains(typelookup, ty):
                    t = typelookup[ty]
                    ct = t if count < 0 else (t * count)

                # if our type is a string type, then we can simply make a ctype for it
                elif ty in {chr, str}:
                    ct = ctypes.c_char if count < 0 else (ctypes.c_char * count)

                # otherwise we have no idea what ctype we can use for this, so skip it
                # by creating a buffer for it
                else:
                    logging.warning(u"{:s}.structure({:#x}, ...) : Using buffer with size {:+#x} for member #{:d} ({:s}) due to unsupported type {!s}.".format('.'.join([__name__, cls.__name__]), ea, m.size, m.index, m.fullname, ty if count < 0 else [ty, count]))
                    ct = None

            # finally we can add the member to our result by creating a buffer for it
            res[m.name] = val if any(item is None for item in [ct, val]) else ctypes.cast(ctypes.pointer(ctypes.c_buffer(val)), ctypes.POINTER(ct)).contents
        return res
    struc = struct = utils.alias(structure, 'get')

    class switch(object):
        """
        Function for fetching an instance of a ``switch_t`` from a given address.
        Despite this being a namespace, by default it is intended to be used
        as a function against any known component of a switch. It will then
        return a class that allows one to query the different attributes of
        an ``idaapi.switch_info_t``.

        This namespace can be used as in the following example::

            > sw = database.get.switch(ea)
            > print sw

        """
        @classmethod
        def __getlabel(cls, ea):
            get_switch_info = idaapi.get_switch_info_ex if idaapi.__version__ < 7.0 else idaapi.get_switch_info

            f = type.flags(ea)
            if idaapi.has_dummy_name(f) or idaapi.has_user_name(f):
                drefs = (ea for ea in xref.data_up(ea))
                refs = (ea for ea in itertools.chain(*map(xref.up, drefs)) if get_switch_info(ea) is not None)
                try:
                    ea = builtins.next(refs)
                    si = get_switch_info(ea)
                    if si:
                        return interface.switch_t(si)
                except StopIteration:
                    pass
            raise E.MissingTypeOrAttribute(u"{:s}({:#x}) : Unable to instantiate an `idaapi.switch_info_ex_t` at target label.".format('.'.join([__name__, 'type', cls.__name__]), ea))

        @classmethod
        def __getarray(cls, ea):
            get_switch_info = idaapi.get_switch_info_ex if idaapi.__version__ < 7.0 else idaapi.get_switch_info

            refs = (ea for ea in xref.up(ea) if get_switch_info(ea) is not None)
            try:
                ea = builtins.next(refs)
                si = get_switch_info(ea)
                if si:
                    return interface.switch_t(si)
            except StopIteration:
                pass
            raise E.MissingTypeOrAttribute(u"{:s}({:#x}) : Unable to instantiate an `idaapi.switch_info_ex_t` at switch array.".format('.'.join([__name__, 'type', cls.__name__]), ea))

        @classmethod
        def __getinsn(cls, ea):
            get_switch_info = idaapi.get_switch_info_ex if idaapi.__version__ < 7.0 else idaapi.get_switch_info

            # Try and get a switch from the given address. If it worked, then
            # we just need to wrap it up nicely for them to use.
            si = get_switch_info(ea)
            if si is not None:
                return interface.switch_t(si)

            # Otherwise, we iterate through all of its downrefs to see if any
            # valid candidates can be produced.
            for item in xref.down(ea):
                found = not (get_switch_info(item) is None)

                try:
                    # If this reference is pointing to data, then treat it
                    # an array that we needs to be checked.
                    if not found and type.is_data(item):
                        items = (case for case in get.array(item))
                        candidates = (label for label in itertools.chain(*map(xref.up, items)) if get_switch_info(label))
                        res = builtins.next(candidates)

                    # If the reference didn't turn up anything, then check
                    # each of its uprefs to look for candidates.
                    elif not found:
                        candidates = (label for label in xref.up(item) if get_switch_info(label))
                        res = builtins.next(candidates)

                    # Otherwise, the ref directly points to a switch and we
                    # simply need to use it.
                    else:
                        res = item

                # If no candidates for the ref were found (StopIteration),
                # then we continue onto the next available ref.
                except StopIteration:
                    pass

                # If no exception was raised, then we should've gotten an
                # address with a switch. All we need to do is get the switch_info_t
                # and wrap it up for the user before we return it.
                else:
                    si = get_switch_info(res)
                    return interface.switch_t(si)
                continue

            # If the loop went through all of the refs for the given address, then
            # we didn't find shit and we need to let the user know here.
            raise E.MissingTypeOrAttribute(u"{:s}({:#x}) : Unable to instantiate an `idaapi.switch_info_ex_t` at branch instruction.".format('.'.join([__name__, 'type', cls.__name__]), ea))

        @utils.multicase()
        def __new__(cls):
            '''Return the switch at the current address.'''
            return cls(ui.current.address())
        @utils.multicase(ea=six.integer_types)
        def __new__(cls, ea):
            '''Return the switch at the address `ea`.'''
            ea = interface.address.within(ea)
            try:
                return cls.__getinsn(ea)
            except E.MissingTypeOrAttribute:
                pass
            try:
                return cls.__getarray(ea)
            except E.MissingTypeOrAttribute:
                pass
            try:
                return cls.__getlabel(ea)
            except E.MissingTypeOrAttribute:
                pass
            raise E.MissingTypeOrAttribute(u"{:s}({:#x}) : Unable to instantiate an `idaapi.switch_info_ex_t`.".format('.'.join([__name__, 'type', cls.__name__]), ea))

