"""
Output a module into reStructuredText
"""

from __future__ import absolute_import
from __future__ import print_function
from __future__ import unicode_literals

import six, builtins
import functools, operator, itertools, types
import argparse, logging
import ast, contextlib

# global list of filters
class FILTER:
    class NAMESPACE:
        WHITELIST, BLACKLIST = set(), set()
    class FUNCTION:
        WHITELIST, BLACKLIST = set(), set()

# some global constants
class undefined(object): pass

### Namespace of idascripts-specific types that get evaluated to an internal type or a string
class evaluate(object):
    def __new__(cls, path):
        '''Use the current namespace to try and get some primitive type of some kind'''

        # walk the specified namespace resolving everything till we get a type
        def __evaluate(ns, path):
            res = cls
            for name in path:
                res = getattr(res, name)
            return res

        try:
            # try and resolve the string using our namespace
            res = __evaluate(cls, path.split('.'))
        except AttributeError:
            # otherwise, just return it unmodified
            return path
        return res

    ## Miscellaneous internal types
    import six, types, builtins

    class structure:
        structure_t = 'structure_t'
        member_t = 'member_t'
    _structure = structure

    class interface:
        symbol_t = 'symbol_t'
        namedtypedtuple = 'namedtuple'
        register_t = 'register_t'
        architecture_t = 'architecture_t'

### Namespace of internal python types and how to convert them into a string
class stringify(object):
    definitions = {
        None: 'None',
        int: 'int',
        long: 'long',
        list: 'list', builtins.list: 'list',
        str: 'str', basestring: 'str',
        unicode: 'unicode',
        chr: 'chr',
        callable: 'callable',
        tuple: 'tuple',
        set: 'set',
        None.__class__: 'None',
    }
    stringmap = {
        'types.NoneType' : 'None',
        'None.__class__' : 'None',
        'types.TupleType' : 'tuple',
        'basestring': 'str',
    }
    def __new__(cls, object):
        if isinstance(object, six.string_types):
            try:
                res = cls.stringmap[object] if object in cls.stringmap else evaluate(object)
            except AttributeError:
                res = object
            return cls(res) if isinstance(res, type) else res
        elif isinstance(object, (six.integer_types, float)):
            return "{!s}".format(object)
        if not isinstance(object, tuple):
            res = cls.definitions[object]
            return cls(res)
        return tuple(cls(res) for res in object)

### Reference types which represent the parsed tree
class Reference(object):
    def __init__(self, **attrs):
        self.__children__ = []
        self.set(**attrs)
    def add(self, object):
        if not isinstance(object, Reference):
            raise TypeError(object)
        self.__children__.append(object)
    def get(self, name, *default):
        if not isinstance(name, six.string_types):
            raise TypeError(name)
        return getattr(self, "_{:s}".format(name), *default) if default else getattr(self, "_{:s}".format(name))
    def set(self, **attrs):
        for name, _ in attrs.iteritems():
            if not isinstance(name, six.string_types):
                raise TypeError(name)
            continue
        [setattr(self, "_{:s}".format(key), value) for key, value in attrs.iteritems()]
    def has(self, name):
        if not isinstance(name, six.string_types):
            raise TypeError(name)
        return hasattr(self, "_{:s}".format(name))
    name = property(fget=operator.attrgetter('_name'))
    node = property(fget=operator.attrgetter('_node'))
    def __repr__(self):
        cls = self.__class__
        return "{:s}({:s})".format(cls.__name__, self.name)
    children = property(fget=operator.attrgetter('__children__'))
    def __iter__(self):
        for child in self.__children__:
            yield child
        return
    def __getitem__(self, index):
        return self.__children__[index]

class Commentable(Reference):
    comment = property(fget=operator.attrgetter('_docstring'))
class Module(Commentable): pass
class Namespace(Commentable):
    namespace = property(fget=operator.attrgetter('_namespace'))
class Class(Commentable):
    ns = namespace = property(fget=operator.attrgetter('_namespace'))
    bases = property(fget=operator.attrgetter('_bases'))
class Function(Commentable):
    ns = namespace = property(fget=operator.attrgetter('_namespace'))
    args = property(fget=operator.attrgetter('_arguments'))
    argtypes = mc = property(fget=operator.attrgetter('_multicase'))
    argdefaults = defaults = property(fget=operator.attrgetter('_defaults'))
    def __repr__(self):
        return "{:s}({:s})".format(super(Function, self).__repr__(), ', '.join(map("{!r}".format, self._arguments)))
class PropertyFunction(Function):
    ns = namespace = property(fget=operator.attrgetter('_namespace'))
    owner = property(fget=operator.attrgetter('_owner'))
class StaticFunction(Function): pass
class ClassFunction(Function): pass
class Param(Reference):
    owner = property(fget=operator.attrgetter('_owner'))
class ParamTuple(Reference):
    owner = property(fget=operator.attrgetter('_owner'))
    params = property(fget=operator.attrgetter('_params'))
    def members(self):
        res, = grammar.reduce(self.params)
        return tuple(map(operator.itemgetter(0), res))
    def __repr__(self):
        cls = self.__class__
        res, = grammar.reduce(self.params)
        return "{:s}({:s})".format(cls.__name__, ','.join(p for p, in res))
class ParamVariableList(Param): pass
class ParamVariableKeyword(Param): pass

### reduce parts of the ast as a tuple of strings
class grammar(object):
    def reduce_call(call):
        res = ()
        res += grammar.reduce(call.func)
        res += [arg for arg, in map(grammar.reduce, call.args)],
        res += map(grammar.reduce, call.keywords),
        res += grammar.reduce(call.starargs) if call.starargs else None,
        res += grammar.reduce(call.kwargs) if call.kwargs else None,
        return res

    def reduce_keyword(keyword):
        res = ()
        res += (keyword.arg,)
        if hasattr(keyword, 'value'):
            res += grammar.reduce(keyword.value)
        return res

    def reduce_attribute(attr):
        res = ()
        if hasattr(attr, 'value'):
            res += grammar.reduce(attr.value)
        res += (attr.attr,)
        return '.'.join(res),

    def reduce_name(name):
        return name.id,

    def reduce_number(num):
        return num.n,

    def reduce_tuple(T):
        return tuple(map(grammar.reduce, T.elts)),

    def reduce_string(str):
        def escape(string, chars):
            for ch in string:
                if ch in chars:
                    yield '\\'
                yield ch
            return
        res = ''.join(escape(str.s, r'\"'))
        return res,

    def reduce_binop(op):
        l, op, r = op.left, op.op, op.right
        operation = grammar.operation[type(op)]
        global evaluate
        l, r = (n[0] for n in map(grammar.reduce, (l, r)))
        if isinstance(l, tuple): l = reduce(operation, l)
        if isinstance(r, tuple): r = reduce(operation, r)
        if isinstance(l, six.string_types): l = evaluate(l)
        if isinstance(r, six.string_types): r = evaluate(r)
        return operation(l, r),

    def reduce_dictionary(dict):
        keys = map(grammar.reduce, dict.keys)
        values = map(grammar.reduce, dict.values)
        res = ["{:s}={:s}".format(k[0], v[0]) for k, v in zip(keys, values)]
        return "{{{:s}}}".format(', '.join(res)),

    def return_empty(yy):
        return '',

    @staticmethod
    def reduce(type):
        # check if it's a reduction that requires a transform
        for t, f in grammar.reduction.iteritems():
            if isinstance(type, t):
                return f(type)
            continue
        # its not, so try and map it directly to the operation
        if type.__class__ in grammar.operation:
            return grammar.operation[type.__class__]
        raise TypeError(type)

    reduction = {
        ast.Attribute : reduce_attribute,
        ast.Name : reduce_name,
        ast.keyword : reduce_keyword,
        ast.Call : reduce_call,
        ast.Tuple : reduce_tuple,
        ast.Str : reduce_string,
        ast.Num : reduce_number,
        ast.Dict : reduce_dictionary,
        ast.BinOp : reduce_binop,
        ast.Load : return_empty,
    }

    operation = {
        ast.Add : operator.add,
        ast.And : lambda a, b: a and b,
        ast.BitAnd : operator.and_,
        ast.BitOr : operator.or_,
        ast.Compare : cmp,
        ast.Div : operator.div,
        ast.Eq : operator.eq,
        ast.Gt : operator.gt,
        ast.GtE : operator.ge,
        ast.In : lambda a, b: a in b,
        ast.Is : operator.is_,
        ast.IsNot : operator.is_not,
        ast.LShift : operator.lshift,
        ast.Lt : operator.lt,
        ast.LtE : operator.le,
        ast.Mod : operator.mod,
        ast.Mult : operator.mul,
        ast.NotEq : operator.ne,
        ast.NotIn : lambda a, b: a not in b,
        ast.Or : lambda a, b: a or b,
        ast.Pow : operator.pow,
        ast.RShift : operator.rshift,
        ast.Sub : operator.sub,
        ast.UAdd : operator.iadd,
        ast.USub : operator.isub,
    }

class backticklexer(object):
    '''Scan for words that are double-backticked or single-backticked and replace them with some format string'''
    def __init__(self, fmtsingle, fmtdouble):
        '''Replace single-backticked strings with ``fmtsingle`` and double-backticked stringss with ``fmtdouble``.'''
        self.format_single = fmtsingle
        self.format_double = fmtdouble

    def lex(self, string):
        '''Run the instance against ``string``.'''
        res = []
        result = self.aggregate(res); next(result)
        lex = self.__scan_singletick(result); next(lex)
        self.read(iter(string), lex)
        return str().join(res)

    @staticmethod
    def read(source, ticker):
        try:
            while True:
                ch = next(source)
                ticker.send(ch)
        except StopIteration: ticker.close()

    @staticmethod
    def aggregate(result):
        try:
            while True:
                result.append( (yield) )
        except GeneratorExit: return

    def __scan_singletick(self, result):
        ch = (yield)
        try:
            while True:
                if ch == '`':
                    doubletick, singletick = [], []
                    ch = (yield)
                    c_double = self.aggregate(doubletick); next(c_double)
                    c_single = self.aggregate(singletick); next(c_single)
                    scanner = self.__scan_doubletick(c_double, c_single); next(scanner)
                    try:
                        while True:
                            scanner.send(ch)
                            ch = (yield)
                    except StopIteration: pass
                    if doubletick:
                        res = str().join(doubletick)
                        map(result.send, self.format_double(res))
                    elif singletick:
                        res = str().join(singletick)
                        map(result.send, self.format_single(res))
                    scanner.close()
                else:
                    result.send(ch)
                ch = (yield)
        except GeneratorExit: result.close()

    def __scan_doubletick(self, double, single):
        ch = (yield)
        if ch == '`':
            ch = (yield)
            while True:
                double.send(ch)
                ch = (yield)
                if ch == '`': break
            ch = (yield)
            return

        while ch != '`':
            single.send(ch)
            ch = (yield)
        return

### Converting Reference types into reStructuredText
class restructure(object):
    ## small utility functions
    @classmethod
    def escape(cls, string):
        def escape_chars(iterable, characters=u'*\\'):
            characters = set(characters)
            for ch in iterable:
                if ch in characters:
                    yield '\\'
                yield ch
            return
        return str().join(escape_chars(string))
    @classmethod
    def escapelist(cls, strings):
        return map(cls.escape, strings)
    @classmethod
    def indent(cls, string, prefix):
        res = string.split('\n') if isinstance(string, six.string_types) else string
        return '\n'.join(cls.indentlist(res, prefix))
    @classmethod
    def indentlist(cls, strings, prefix):
        return [prefix + line for line in strings]
    @classmethod
    def walk(cls, ref, field):
        '''Return every parent element whilst excluding the final module.'''
        while ref.has(field):
            yield ref
            ref = ref.get(field)
        yield ref
    @classmethod
    def __objectOrReference(cls, string, invalid='()', type='obj'):
        invalid = '()'
        idx = -1
        for ch in itertools.ifilter(functools.partial(operator.contains, string), iter(invalid)):
            res = string.find(ch)
            if idx < 0 or res > 0 and res < idx:
                idx = res
            continue

        fmt = ":py:{:s}:".format(type)
        f = (fmt + "`{:s}`").format if idx < 0 else functools.partial((fmt + "`{:s}<{ref:s}>`").format, ref=string[:idx])
        return f(string)
    @classmethod
    def moduleDocstringToList(cls, cmt):
        L = backticklexer("``{:s}``".format, cls.__objectOrReference)
        formatted = L.lex(cmt)

        res = []
        for line in formatted.strip().split('\n'):
            res.append("- {:s}".format(cls.escape(line.strip())) if line.startswith(' ') and not line.strip().startswith('>') else line if line.strip().startswith('>') else cls.escape(line.strip()))
        return res
    @classmethod
    def nsDocstringToList(cls, cmt):
        L = backticklexer("``{:s}``".format, cls.__objectOrReference)
        formatted = L.lex(cmt)

        res = []
        for line in formatted.strip().split('\n'):
            res.append("- {:s}".format(cls.escape(line.strip())) if line.startswith(' ') and not line.strip().startswith('>') else line if line.strip().startswith('>') else cls.escape(line.strip()))
        return res
    @classmethod
    def classDocstringToList(cls, cmt):
        L = backticklexer("``{:s}``".format, cls.__objectOrReference)
        formatted = L.lex(cmt)

        res = []
        for line in formatted.strip().split('\n'):
            res.append("- {:s}".format(cls.escape(line.strip())) if line.startswith(' ') and not line.strip().startswith('>') else line if line.strip().startswith('>') else cls.escape(line.strip()))
        return res
    @classmethod
    def methodDocstringToList(cls, cmt):
        L = backticklexer("``{:s}``".format, functools.partial(cls.__objectOrReference, type='class'))
        formatted = L.lex(cmt)

        res = []
        for line in formatted.strip().split('\n'):
            res.append("- {:s}".format(cls.escape(line.strip())) if line.startswith(' ') and not line.strip().startswith('>') else line if line.strip().startswith('>') else cls.escape(line.strip()))
        return res
    @classmethod
    def functionDocstringToList(cls, cmt):
        L = backticklexer("``{:s}``".format, cls.__objectOrReference)
        formatted = L.lex(cmt)

        res = []
        for line in formatted.strip().split('\n'):
            res.append("- {:s}".format(cls.escape(line.strip())) if line.startswith(' ') and not line.strip().startswith('>') else line if line.strip().startswith('>') else cls.escape(line.strip()))
        return res
    @classmethod
    def paramDescriptionToRst(cls, descr):
        L = backticklexer(cls.__objectOrReference, "``{:s}``".format)
        return cls.escape(L.lex(descr))

    ## Reference type converters
    @classmethod
    def Module(cls, ref):
        res = [".. py:module:: {name:s}".format(name=ref.name)]

        descr = ''
        if ref.comment:
            res.append('')

            iterable = iter(cls.moduleDocstringToList(ref.comment))

            # extract and procses the description
            descr = next(iterable)
            definition = "{:s} -- {:s}".format(ref.name, descr)
            res.append(definition)
            res.append('=' * len(definition))

            # remove all initial whitespace
            itertools.takewhile(lambda s: not s, iterable)
            next(iterable)

            # now we can use the comment
            res.append('')
            res.extend(iterable)
            res.append('')
        else:
            res.append('')
            res.append('=' * len(ref.name))
            res.append(ref.name)
            res.append('=' * len(ref.name))

        # split up the member into separate lists
        functions, namespaces, classes = [], [], []
        for t, iterable in itertools.groupby(ref.children, type):
            if issubclass(t, Function):
                functions.extend(iterable)
            elif issubclass(t, Namespace):
                namespaces.extend(iterable)
            elif issubclass(t, Class):
                classes.extend(iterable)
            else:
                raise TypeError(t)
            continue

        # add each type individually
        if functions:
            res.append('-------------')
            res.append('Function list')
            res.append('-------------')
            res.append('')
            res.extend(map(operator.methodcaller('strip'), """
            The functions that are available in this module use multicased
            functions and aliases. For more information on this, please see
            :ref:`multicase-aliases` and :ref:`multicase-functions`.
            """.strip().split('\n')))
            res.append('')

            for ch in sorted(functions, key=operator.attrgetter('name')):
                res.extend(cls.Function(ch).split('\n'))

        if namespaces:
            res.append('--------------')
            res.append('Namespace list')
            res.append('--------------')
            res.append('')
            res.extend(map(operator.methodcaller('strip'), """
            These are the namespaces available within this module. Namespaces
            group similar functions that can be used typically for the same
            concept. Please see :ref:`multicase-namespaces` for more
            information on namespaces. For more information on multicase
            functions or aliases, please see :ref:`multicase-functions` or
            :ref:`multicase-aliases`.
            """.strip().split('\n')))
            res.append('')

            for ch in sorted(namespaces, key=operator.attrgetter('name')):
                res.extend(cls.Namespace(ch).split('\n'))

        if classes:
            res.append('----------')
            res.append('Class list')
            res.append('----------')
            res.append('')
            res.extend(map(operator.methodcaller('strip'), """
            Classes provide the definition necessary to instantiate an object.
            In most cases, a class is returned when calling one of the prior
            listed functions and thus have no need to be manually instantiated.
            Classes may also have aliases defined for them. Please refer to the
            documentation for the class to see what is available. For more
            information on aliases, please see :ref:`multicase-aliases`.
            """.strip().split('\n')))
            res.append('')

            for ch in sorted(classes, key=operator.attrgetter('name')):
                rows = cls.Class(ch).split('\n')
                if filter(None, rows): res.extend(rows)

        return '\n'.join(res)

    @classmethod
    def Namespace(cls, ref, depth=0):
        if ref.get('skippable') and not len([ch for ch in ref.children if not isinstance(ch, Namespace)]): return ''

        ns = [r.name for r in cls.walk(ref, 'namespace')]
        name = r'.'.join(reversed(ns))

        res, sectionchar = [], '*^*'

        # namespace reference
        res.append(".. _ns-{:s}:".format(name.replace('.', '-')))
        res.append('')

        # namespace header
        if depth <= 1: res.append(sectionchar[depth] * len(name))
        res.append(cls.escape(name))
        res.append(sectionchar[depth] * len(name))
        res.append('')

        # namespace aliases
        if ref.has('aliases'):
            aliases = map(stringify, ref.get('aliases'))
            aliases = map(functools.partial("{:s}.{:s}".format, ns[-1]), aliases)
            res.append("Aliases: {:s}".format(', '.join(map(lambda s: ":ref:`{:s}<ns-{:s}>`".format(s, name.replace('.', '-')), aliases))))
            res.append('')

        # namespace documentation
        if ref.comment:
            res.extend(cls.nsDocstringToList(ref.comment))
            res.append('')

        if ref.has('details'):
            res.extend(cls.nsDocstringToList(ref.get('details')))
            res.append('')

        # namespace bases
        if ref.has('bases'):
            bases = map(stringify, ref.get('bases'))
            bases = map(functools.partial("{:s}.{:s}".format, ns[-1]), bases)
            res.append("Bases: {:s}".format(', '.join(map(lambda s: ":ref:`{:s}<ns-{:s}>`".format(s, s.replace('.', '-')), bases))))
            res.append('')

        # split up the member into separate lists
        functions, namespaces, classes = [], [], []
        for t, iterable in itertools.groupby(ref.children, type):
            if issubclass(t, Function):
                functions.extend(iterable)
            elif issubclass(t, Namespace):
                namespaces.extend(iterable)
            elif issubclass(t, Class):
                classes.extend(iterable)
            else:
                raise TypeError(t)
            continue

        # add each type individually
        for ch in sorted(functions, key=operator.attrgetter('name')):
            res.extend(cls.Function(ch).split('\n'))
        for ch in sorted(namespaces, key=operator.attrgetter('name')):
            res.extend(cls.Namespace(ch, depth=depth+1).split('\n'))
        for ch in sorted(classes, key=operator.attrgetter('name')):
            rows = cls.Class(ch, depth=depth+1).split('\n')
            if filter(None, rows): res.extend(rows)

        return '\n'.join(res)

    @classmethod
    def Class(cls, ref, depth=0):
        if ref.get('skippable') and not ref.children: return ''

        ns = [r.name for r in cls.walk(ref, 'namespace')]
        name = '.'.join(reversed(ns[:-1]))

        res, sectionchar = [], '*^*'

        # class header
        header = []

        if depth <= 1: header.append(sectionchar[depth] * len(name))
        header.append(cls.escape(name))
        header.append(sectionchar[depth] * len(name))

        header.append('')
        header.append(".. py:class:: {name:s}".format(name=name))

        # class bases
        if ref.has('bases'):
            res.append('')
            bases = map(stringify, ref.bases)
            res.append("Bases: {:s}".format(', '.join(map(":py:class:`{:s}`".format, bases))))

        # class documentation
        res.append('')
        if ref.comment:
            res.extend(cls.classDocstringToList(ref.comment))
            res.append('')

        if ref.has('details'):
            res.extend(cls.classDocstringToList(ref.get('details')))
            res.append('')

        # split up the properties from the methods
        global types
        props, children = [], []
        for t, iterable in itertools.groupby(ref.children, lambda ch: isinstance(ch, PropertyFunction)):
            if t: props.extend(iterable)
            else: children.extend(iterable)

        # group related properties together
        grouped = []
        for ch in sorted(props, key=lambda ch: ch.name.lower()):
            if ch.owner == ch:
                grouped.append(ch)
            elif ch.get('property') == 'getter':
                ch.owner.set(getter=ch)
            elif ch.get('property') == 'setter':
                ch.owner.set(setter=ch)
            if ch.has('details'):
                ch.owner.set(details=ch.get('details'))
            continue

        # process properties
        for ch in sorted(grouped, key=lambda ch: ch.name.lower()):
            if not isinstance(ch, PropertyFunction):
                raise TypeError(ch)
            res.append(cls.Property(ch))

        # process functions
        for ch in sorted(children, key=lambda ch: ch.name.lower()):
            if isinstance(ch, Function):
                res.extend(cls.Method(ch).split('\n'))
            elif isinstance(ch, Namespace):
                res.extend(cls.Namespace(ch, depth=depth+1).split('\n'))
            else:
                raise TypeError(ch)
            continue
        res = cls.indentlist(res, '   ')
        res[0:0] = header

        return '\n'.join(res)

    @classmethod
    def Arguments(cls, ref):
        global stringify, undefined
        adefs, atypes, aparams = ref.get('defaults') or {}, ref.mc, ref.get('parameters')

        # group arguments by their type
        gargs = {}
        for a in ref.args:
            gargs.setdefault(Param if isinstance(a, ParamTuple) else type(a), []).append(a)
            #gargs = dict(itertools.groupby(ref.args, type))

        # aggregate the different parameter components according to the names and their types/defaults
        args = []   # args in definition (name, defaults)
        params = [] # parameters that are listed (name, description, types)
        if Param in gargs:
            for a in gargs[Param]:
                # handle Param
                if isinstance(a, Param):
                    args.append((a.name, adefs.get(a.name, undefined())))
                    params.append((a.name, aparams.get(a.name, undefined()), atypes.get(a.name, undefined())))
                    continue
                # handle ParamTuple
                args.append(("({:s})".format(','.join(a.members())), undefined()))
                for an in a.members():
                    params.append((an, aparams.get(an, undefined()), atypes.get(an, undefined())))
                continue
        if ParamVariableList in gargs:
            for a in gargs[ParamVariableList]:
                args.append(("*{:s}".format(a.name), undefined()))
                params.append(("*{:s}".format(a.name), aparams.get(a.name, undefined()), atypes.get(a.name, undefined())))
            pass
        if ParamVariableKeyword in gargs:
            for a in gargs[ParamVariableKeyword]:
                args.append(("**{:s}".format(a.name), undefined()))
                params.append(("**{:s}".format(a.name), aparams.get(a.name, undefined()), atypes.get(a.name, undefined())))
            pass

        # transform any defaults that were specified into their string representation
        res = []
        for n, df in args:
            if isinstance(df, undefined):
                res.append((n, df))
            elif df == '':
                res.append((n, "''"))
            elif df == ():
                res.append((n, '()'))
            elif isinstance(df, tuple):
                res.append((n, '|'.join(map(stringify, df))))
            elif isinstance(df, six.integer_types):
                res.append((n, ("{!s}" if df < 0x100 else "{:#x}").format(df)))
            elif isinstance(df, float):
                res.append((n, "{!s}".format(df)))
            elif isinstance(df, six.string_types):
                res.append((n, df))
            else:
                raise TypeError('args', n, df)
            continue
        args = res[:]

        # transform any types that were specified into a string representation
        res = []
        for n, descr, ty in params:
            # skip if there's no types defined
            if isinstance(ty, undefined):
                res.append((n, descr, ty))
                continue

            # convert any suspected resolvable types to a string
            ty = stringify(evaluate(ty))
            if isinstance(ty, six.string_types):
                res.append((n, descr, ty))
            elif isinstance(ty, types.TupleType):
                t = tuple(ty)
                if all(isinstance(n, tuple) for n in t): t = tuple(map(operator.itemgetter(0), t))
                res.append((n, descr, tuple(map(stringify, t))))
            else:
                raise TypeError('params', n, ty)
            continue
        params = res[:]

        # should be good to go
        return args, params

    @classmethod
    def Property(cls, ref):
        ns = [r.name for r in cls.walk(ref, 'namespace')]
        ns = ns[1:] if ref.name == '__new__' else ns[:]
        name = '.'.join(reversed(ns)) if ref.name == '__new__' else ref.name

        definition = ".. py:attribute:: {name:s}".format(name=name)

        res = []
        res.append('')

        if ref.has('details'):
            res.extend(cls.methodDocstringToList(ref.get('details')))

        attrs = []
        if ref.has('getter'): attrs.append(('getter', ref.get('getter')))
        else: attrs.append(('getter', ref))
        if ref.has('setter'): attrs.append(('setter', ref.get('setter')))

        props = []
        for n, r in attrs:
            fmt = ":param {name:s}: {comment:s}"
            props.append(fmt.format(name=n, comment=' '.join(cls.functionDocstringToList(r.comment))))

            _, pparams = cls.Arguments(r)

            for n, descr, ty in pparams[1:]:
                fmt = ":param {name:s}:" if isinstance(ty, undefined) else ":param {type:s} {name:s}:"
                fmt += '' if isinstance(descr, undefined) else (' '+cls.escape(descr))
                props.append(fmt.format(type=ty, name=cls.escape(n)))
            continue
        res.extend(cls.indentlist(props, '   '))

        if attrs: res.append('')

        res = cls.indentlist(res, '   ')
        res[0:0] = (definition,)
        return '\n'.join(res)

    @classmethod
    def Method(cls, ref):
        ns = [r.name for r in cls.walk(ref, 'namespace')]

        aliases = ref.get('aliases') or {}
        args, params = cls.Arguments(ref)

        # now we can make the definition
        definition = ".. py:method:: {name:s}({arguments:s})".format(name=ref.name, arguments=', '.join(cls.escape(n) if isinstance(df, undefined) else "{:s}={!s}".format(cls.escape(n), df) for n, df in itertools.chain([('cls', undefined())] if ref.name == '__new__' else [], args)))

        # populate the contents of the function
        res = []
        res.append('')
        if ref.comment:
            res.extend(cls.functionDocstringToList(ref.comment) + [''])
        if aliases:
            f = functools.partial(":py:func:`{:s}.{:s}<{ref:s}>`".format, ns[-1], ref=ref.name)
            res.append("Aliases: {:s}".format(', '.join(map(f, aliases))))
            res.append('')

        for n, descr, ty in params[:] if ref.name == '__new__' else params[1:]:
            res.append(":param {name:s}:".format(name=cls.escape(n)) if isinstance(descr, undefined) else ":param {name:s}: {description:s}".format(name=cls.escape(n), description=cls.paramDescriptionToRst(descr.strip())))
            if not isinstance(ty, undefined):
                types = ' or '.join(cls.escape(item) for item in itertools.chain(*(items if isinstance(items, tuple) else [items] for items in ty))) if isinstance(ty, tuple) else cls.escape(ty)
                res.append(":type {name:s}: {types:s}".format(name=cls.escape(n), types=types))
            continue

        if params[1:]: res.append('')

        res = cls.indentlist(res, '   ')
        res[0:0] = (definition,)
        return '\n'.join(res)

    @classmethod
    def Function(cls, ref):
        ns = [r.name for r in cls.walk(ref, 'namespace')]
        ns = ns[1:] if ref.name == '__new__' else ns[:]
        name = r'\.'.join(reversed(ns[:-1]))

        aliases = ref.get('aliases') or {}
        args, params = cls.Arguments(ref)

        # now we can make the definition
        definition = ".. py:function:: {name:s}({arguments:s})".format(name=name, arguments=', '.join(cls.escape(n) if isinstance(df, undefined) else "{:s}={!s}".format(cls.escape(n), df) for n, df in args))

        # populate the contents of the function
        res = []
        res.append('')
        if ref.comment:
            res.extend(cls.functionDocstringToList(ref.comment) + [''])
        if aliases:
            f = functools.partial(":py:func:`{:s}.{:s}<{ref:s}>`".format, ns[-1], ref=name)
            res.append("Aliases: {:s}".format(', '.join(map(f, aliases))))
            res.append('')

        for n, descr, ty in params:
            res.append(":param {name:s}:".format(name=cls.escape(n)) if isinstance(descr, undefined) else ":param {name:s}: {description:s}".format(name=cls.escape(n), description=cls.paramDescriptionToRst(descr.strip())))
            if not isinstance(ty, undefined):
                types = ' or '.join(cls.escape(item) for item in itertools.chain(*(items if isinstance(items, tuple) else [items] for items in ty))) if isinstance(ty, tuple) else cls.escape(ty)
                res.append(":type {name:s}: {types:s}".format(name=cls.escape(n), types=types))
            continue

        if params: res.append('')

        res = cls.indentlist(res, '   ')
        res[0:0] = (definition,)
        return '\n'.join(res)

### Visitor Node decorator_list extraction
class decorators(object):
    @classmethod
    def attributes(cls, node):
        global grammar
        res = (d for d in node.decorator_list if isinstance(d, (ast.Attribute,ast.Name)))
        return [n for n, in map(grammar.reduce, res)]
    @classmethod
    def functions(cls, node):
        global grammar
        res = (d for d in node.decorator_list if isinstance(d, ast.Call))
        return [(n, a, k, sa, sk) for n, a, k, sa, sk in map(grammar.reduce, res)]

    @classmethod
    def check(cls, node):
        available = {
            'document.aliases',
            'document.hidden',
            'document.parameters',
            'document.namespace',
            'document.classdef',
            'document.details',
            'document.rename',
        }

        if any(n.startswith('document.') and n not in available for n in cls.attributes(node)):
            raise TypeError("Unknown document attribute: {!r}".format(cls.attributes(node)))

        for n, a, _, _, _ in cls.functions(node):
            if n.startswith('document.') and n not in available:
                raise TypeError("Unknown document decorator: {!s}".format(n))
            continue
        return

### Visitor parser mix-ins
class FullNameMixin(object):
    def fullname(self, ref, node):
        def namespace(ref, field='namespace'):
            while ref.has(field):
                yield ref.name
                ref = ref.get(field)
            yield ref.name
        res = reversed(list(namespace(ref)))
        return '.'.join(list(res) + ([node.name] if node else []))

class ConditionalVisitor(ast.NodeVisitor):
    def visit_If(self, node):
        ok = None
        if isinstance(node.test, ast.Attribute):
            idaapiversion, = grammar.reduce(node.test.left)
            ops = [grammar.reduce(o)[0] for o in node.test.ops]
            versions = [grammar.reduce(v)[0] for v in node.test.comparators]
            if idaapiversion != 'idaapi.__version__':
                raise NotImplementedError(idaapiversion, ops, versions)
            ok = True
        elif isinstance(node.test, ast.Name):
            expr = grammar.reduce(node.test)[0]
            ok = eval(expr)

        if ok is None:
            map(self.visit, node.body)
            map(self.visit, node.orelse)
            return

        if ok:
            map(self.visit, node.body)
        else:
            map(self.visit, node.orelse)
        return

class FunctionVisitor(ast.NodeVisitor, FullNameMixin):
    def match_FunctionDef(self, node):
        cls, ns, name = self.__class__, self.fullname(self._ref, None), self.fullname(self._ref, node)

        # start filtering
        global FILTER
        ok = True

        # first check that the namespace is valid
        allns = {n[0] for n in map(functools.partial(ns.rsplit, '.'), xrange(ns.count('.')+1))}
        if FILTER.NAMESPACE.WHITELIST and any(n in FILTER.NAMESPACE.WHITELIST for n in allns):
            ok = True
        if FILTER.NAMESPACE.BLACKLIST and any(n in FILTER.NAMESPACE.BLACKLIST for n in allns):
            ok = False

        # now we can check if the function is valid
        if FILTER.FUNCTION.WHITELIST:
            if name in FILTER.FUNCTION.WHITELIST:
                logging.info("{:s}.match_FunctionDef: Documenting whitelisted function {!s}".format(cls.__name__, name))
                return True
            elif all(n not in FILTER.NAMESPACE.WHITELIST for n in allns):
                logging.info("{:s}.match_FunctionDef: Skipping function not in whitelisted namespace/class {!s}".format(cls.__name__, name))
                return False

        if ok and FILTER.FUNCTION.BLACKLIST and name in FILTER.FUNCTION.BLACKLIST:
            logging.info("{:s}.match_FunctionDef: Skipping blacklisted function {!s}".format(cls.__name__, name))
            return False

        # the namespace wasn't valid, so we're done here
        if not ok:
            logging.info("{:s}.match_FunctionDef: Skipping function in blacklisted namespace/class {!s}".format(cls.__name__, name))
            return False

        # now we can check the default matches
        if node.name == '__new__':
            logging.debug("{:s}.match_FunctionDef: Documenting default function in namespace/class {!s}".format(cls.__name__, name))
            return True

        if node.name.startswith('_'):
            logging.debug("{:s}.match_FunctionDef: Skipping hidden function in namespace/class {!s}".format(cls.__name__, name))
            return False

        logging.debug("{:s}.match_FunctionDef: Documenting matched function {!s}".format(cls.__name__, name))
        return True

    def visit_FunctionDef(self, node):
        cls = self.__class__
        if not self.match_FunctionDef(node): return

        # capture fields
        name = node.name
        try:
            docstring = ast.get_docstring(node)
        except TypeError:
            docstring = ''
        arguments, defaults = node.args, node.args.defaults

        # figure out the defaults
        defs = { a.id : evaluate(grammar.reduce(df)[0]) for df, a in zip(reversed(defaults), reversed(arguments.args)) }

        # verify that all the document decorators are spelled correctly
        decorators.check(node)

        # figure things out about which decorators were applied
        methodtypes = {m for m in decorators.attributes(node)}
        multicase = (dict(kw) for n, _, kw, _, _ in decorators.functions(node) if n == u'utils.multicase')
        aliases = (a for n, a, _, _, _ in decorators.functions(node) if n == 'document.aliases')
        params = (dict(kw) for n, _, kw, _, _ in decorators.functions(node) if n == 'document.parameters')
        details = [details[0] for n, details, _, _, _ in decorators.functions(node) if n == 'document.details']

        # if it's hidden, then don't bother adding it
        if 'document.hidden' in methodtypes:
            logging.info("{:s}.visit_FunctionDef: Skipping parsing of function due to explicit hidden decorator {!s}".format(cls.__name__, self.fullname(self._ref, node)))
            return

        # figure out which type
        if node.name == '__new__' or 'classmethod' in methodtypes:
            F, args = ClassFunction, arguments.args[1:]
        elif 'staticmethod' in methodtypes:
            F, args = StaticFunction, arguments.args[:]
        elif 'property' in methodtypes or any(mt.endswith(t) for mt in methodtypes for t in {'.getter','.setter'}):
            F, args = PropertyFunction, arguments.args[:]
        else:
            F, args = Function, arguments.args[:]

        # construct the function
        res = F(node=node, name=node.name, namespace=self._ref, multicase=next(multicase, {}), docstring=docstring or '', arguments=[], defaults=defs, parameters=next(params, {}), aliases=set(next(aliases, {})))
        self._ref.add(res)

        if details: res.set(details='\n'.join(details))

        # check to see if there's a new name for it
        newnames = [a[0] for n, a, _, _, _ in decorators.functions(node) if n == 'document.rename']
        if newnames: res.set(name=newnames[0])

        # determine what type of attribute it is
        if F is PropertyFunction:
            owner = None
            if 'property' in methodtypes:
                owner = res
                res.set(property='define')
            elif any(mt.endswith('.getter') for mt in methodtypes):
                name = next(mt for mt in methodtypes if mt.endswith('.getter'))
                name, _ = name.rsplit('.', 1)
                owner = next(n for n in self._ref.children if isinstance(n, PropertyFunction) and n.name == name and n.owner == n)
                res.set(property='getter')
            elif any(mt.endswith('.setter') for mt in methodtypes):
                name = next(mt for mt in methodtypes if mt.endswith('.setter'))
                name, _ = name.rsplit('.', 1)
                owner = next(n for n in self._ref.children if isinstance(n, PropertyFunction) and n.name == name and n.owner == n)
                res.set(property='setter')
            if owner is not None:
                res.set(owner=owner)

        # add its arguments
        res.args.extend((ParamTuple(owner=res, params=a) if isinstance(a, ast.Tuple) else Param(name=a.id, owner=res) for a in args))
        if arguments.vararg:
            res.args.append(ParamVariableList(name=arguments.vararg, owner=res))
        if arguments.kwarg:
            res.args.append(ParamVariableKeyword(name=arguments.kwarg, owner=res))
        return

class NamespaceVisitor(ast.NodeVisitor, FullNameMixin):
    def match_ClassDef(self, node):
        cls, ns, name = self.__class__, self.fullname(self._ref, None), self.fullname(self._ref, node)
        allns = {n[0] for n in map(functools.partial(ns.rsplit, '.'), xrange(ns.count('.')+1))}

        global FILTER
        if FILTER.NAMESPACE.WHITELIST:
            if name in FILTER.NAMESPACE.WHITELIST:
                logging.info("{:s}.match_ClassDef: Documenting whitelisted namespace/class {!s}".format(cls.__name__, name))
                return True
            elif all(n not in FILTER.NAMESPACE.WHITELIST for n in allns):
                logging.info("{:s}.match_ClassDef: Skipping non-whitelisted namespace/class {!s}".format(cls.__name__, name))
                return False

        if FILTER.NAMESPACE.BLACKLIST and (name in FILTER.NAMESPACE.BLACKLIST or any(n in FILTER.NAMESPACE.BLACKLIST for n in allns)):
            logging.info("{:s}.match_ClassDef: Skipping blacklisted namespace/class {!s}".format(cls.__name__, name))
            return False

        # now for the default namespace matches
        if node.name.startswith('_'):
            logging.debug("{:s}.match_ClassDef: Skipping hidden namespace/class {!s}".format(cls.__name__, name))
            return False

        logging.debug("{:s}.match_ClassDef: Adding documentation for namespace/class {!s}".format(cls.__name__, name))
        return True

    def visit_ClassDef(self, node):
        '''Anything that's a class is considered a namespace'''
        cls, visible = self.__class__, self.match_ClassDef(node)

        # verify that all the document decorators are spelled correctly
        decorators.check(node)

        # figure out which type it is according to the decorators
        attributes = decorators.attributes(node)
        if 'document.classdef' in attributes:
            res = self.append_classdef(node)
        elif 'document.namespace' in attributes:
            res = self.append_namespace(node)
        else:
            logging.warn("{:s}.visit_ClassDef: Skipping parsing of undecorated node {!s}".format(cls.__name__, self.fullname(self._ref, node)))
            return

        # check to see if the definition is explicitly hidden
        if 'document.hidden' in attributes:
            logging.info("{:s}.visit_ClassDef: Skipping emitting of namespace/class due to explicit hidden decorator {!s}".format(cls.__name__, self.fullname(self._ref, node)))
            visible = False

        # check to see if there's a new name for it
        newnames = [a[0] for n, a, _, _, _ in decorators.functions(node) if n == 'document.rename']
        if newnames: res.set(name=newnames[0])

        # if this namespace can be hidden, then set a flag for the emitter
        res.set(skippable=not visible)

        # add the namespace to the parent
        self._ref.add(res)

        # continue parsing any children
        nv = NSVisitor(res)
        map(nv.visit, ast.iter_child_nodes(node))

    def append_classdef(self, node):
        attributes = decorators.attributes(node)
        details = [details[0] for n, details, _, _, _ in decorators.functions(node) if n == 'document.details']
        bases = [b[0] for b in map(grammar.reduce, node.bases) if b[0] != 'object']

        try:
            docstring = ast.get_docstring(node) or ''
        except TypeError:
            docstring = ''

        # construct the namespace
        res = Class(node=node, name=node.name, namespace=self._ref, docstring=docstring)
        if bases: res.set(bases=bases)
        if attributes: res.set(attributes=attributes)
        if details: res.set(details='\n'.join(details))
        return res

    def append_namespace(self, node):
        attributes = decorators.attributes(node)
        details = [details[0] for n, details, _, _, _ in decorators.functions(node) if n == 'document.details']
        bases = [b[0] for b in map(grammar.reduce, node.bases) if b[0] != 'object']
        aliases = [a[0] for n, a, _, _, _ in decorators.functions(node) if n == 'document.aliases']

        try:
            docstring = ast.get_docstring(node) or ''
        except TypeError:
            docstring = ''

        # construct the namespace
        res = Namespace(node=node, name=node.name, namespace=self._ref, docstring=docstring)
        if bases: res.set(bases=bases)
        if aliases: res.set(aliases=aliases)
        if attributes: res.set(attributes=attributes)
        if details: res.set(details='\n'.join(details))
        return res

### Visitor entrypoints
class NSVisitor(FunctionVisitor, NamespaceVisitor, ConditionalVisitor):
    def __init__(self, ref):
        if not isinstance(ref, Reference):
            raise TypeError(ref)
        self._ref = ref

class RootVisitor(FunctionVisitor, NamespaceVisitor, ConditionalVisitor):
    def __init__(self, ref):
        if not isinstance(ref, Reference):
            raise TypeError(ref)
        self._ref = ref

    def visit_Expr(self, node):
        '''Grab the first module docstring.'''
        if isinstance(node.value, ast.Str) and not self._ref.has('docstring'):
            docstring, = grammar.reduce(node.value)
            self._ref.set(docstring=docstring)
        return

def parse_args(args=None):
    def loglevel(value):
        try:
            res = getattr(logging, value.upper())
        except AttributeError:
            res = int(value)
        return res

    prolog='parse the specified python file and emit reStructuredText from it.'

    epilog = """
    When specifying a filter, each provided argument represents the full
    namespace/class to whitelist. To exclude a namespace/class, prefix the
    argument with a '^' character. To whitelist or blacklist a function name,
    prefix the argument with a '+' or '-'.
    """

    res = argparse.ArgumentParser(description=prolog, epilog=epilog)
    res.add_argument('--name', '-N', type=str, nargs='?', help='the name of the generated module (defaults to the input filename)')
    res.add_argument('--loglevel', type=loglevel, default=logging.ERROR, help='the level of logging (0-100)')
    res.add_argument('--outfile', '-o', type=argparse.FileType('wt'), default=sys.stdout, help='where to output the generated reStructuredText')
    res.add_argument('infile', type=str, help='path to the specified python file')
    res.add_argument('filter', type=str, nargs='*', help='a list of filters applied to the names within the module')
    return res.parse_args(args)

if __name__ == '__main__':
    import sys, os.path

    # parse the arguments
    res = parse_args() if len(sys.argv) < 1 else parse_args(sys.argv[1:])

    # apply the options that were specified at the commandline
    if res.name is None:
        # default module name if one wasn't specified
        _, filename = os.path.split(res.infile)
        res.name, _ = os.path.splitext(filename)

    # set the specified logging level
    logging.root.setLevel(res.loglevel)

    # update both the blacklist and whitelist
    for m in res.filter:
        if m.startswith('+'):
            n, ns = m[1:], m[1:].rsplit('.', 1)[0]
            logging.debug("{:s}: Adding function {!s} to whitelist.".format(__name__, n))
            FILTER.FUNCTION.WHITELIST.add(n)
        elif m.startswith('-'):
            n, ns = m[1:], m[1:].rsplit('.', 1)[0]
            logging.debug("{:s}: Adding function {!s} to blacklist.".format(__name__, n))
            FILTER.FUNCTION.BLACKLIST.add(n)
        elif m.startswith('^'):
            logging.debug("{:s}: Adding namespace {!s} to blacklist.".format(__name__, m[1:]))
            FILTER.NAMESPACE.BLACKLIST.add(m[1:])
        else:
            logging.debug("{:s}: Adding namespace {!s} to whitelist.".format(__name__, m[:]))
            FILTER.NAMESPACE.WHITELIST.add(m[:])
        continue

    # emit the current state of the filters
    if FILTER.NAMESPACE.WHITELIST: logging.info("{:s}: Namespace whitelist: {!r}".format(__name__, FILTER.NAMESPACE.WHITELIST))
    if FILTER.NAMESPACE.BLACKLIST: logging.info("{:s}: Namespace blacklist: {!r}".format(__name__, FILTER.NAMESPACE.BLACKLIST))
    if FILTER.FUNCTION.WHITELIST: logging.info("{:s}: Function whitelist: {!r}".format(__name__, FILTER.FUNCTION.WHITELIST))
    if FILTER.FUNCTION.BLACKLIST: logging.info("{:s}: Function blacklist: {!r}".format(__name__, FILTER.FUNCTION.BLACKLIST))

    # create our root module object
    M = Module(name=res.name)

    # read the file and parse everything into our root module object
    with file(res.infile, 'rt') as f:
        data = ast.parse(f.read(), res.name)

    V = RootVisitor(M)
    V.visit(data)

    # now we should have some data to format as rst
    print(restructure.Module(M), file=res.outfile)
