"""
Tags module

This module exposes tools for exporting the currently defined tags
within the database. Once exported, these tags can then be pickled
or then re-applied to the same or another database. Some options
are allowed which will let a user apply translations to the tags
before applying them to a target database.

To fetch all of the tags from the database::

    > res = custom.tags.read()

To export only specific tags from the database::

    > res = custom.tags.export('tag1', 'tag2', ...)

To apply previously read tags to the database::

    > custom.tags.apply(res)

To apply previously read tags with different names to the database::

    > custom.tags.apply(res, tag1='my_tag1', tag2='my_tag2', ...)

"""

import six, sys, logging, builtins
import functools, operator, itertools, types, string

import database as db, function as func, structure as struc, ui
import internal

output = sys.stderr

### miscellaneous tag utilities
def list():
    '''Return the tags for the all of the function contents within the database as a set.'''
    return {res for res in itertools.chain(*(res for _, res in db.selectcontents()))}

### internal utility functions and classes
def lvarNameQ(name):
    '''Determine whether a `name` is something that IDA named automatically.'''
    if any(name.startswith(item) for item in ['arg_', 'var_']):
        res = name.split('_', 1)[-1]
        return all(item in string.hexdigits for item in res)
    elif name.startswith(' '):
        return name[1:] in {'s', 'r'}
    return False

def locationToAddress(loc):
    '''Convert the function location `loc` back into an address.'''

    ## if location is a tuple, then convert it to an address
    if isinstance(loc, tuple):
        f, cid, ofs = loc
        base, _ = next(b for i, b in enumerate(func.chunks(f)) if i == cid)
        return base + ofs

    ## otherwise, it's already an address
    return loc

def addressToLocation(ea, chunks=None):
    """Convert the address `ea` to a `(function, id, offset)`.

    The fields `id` and `offset` represent the chunk index and the
    offset into the chunk for the function at `ea`. If the list
    `chunks` is specified as a parameter, then use it as a tuple
    of ranges in order to calculate the correct address.
    """
    F, chunks = func.by(ea), chunks or [ch for ch in func.chunks(ea)]
    cid, base = next((i, l) for i, (l, r) in enumerate(chunks) if l <= ea < r)
    return func.top(F), cid, ea - base

class dummy(object):
    """
    A dummy object that is guaranteed to return False whenever it is compared
    against anything.
    """
    def __eq__(self, other): return False
    def __cmp__(self, other): return -1
dummy = dummy()

### read without using the tag cache
class read(object):
    """
    This namespace contains tools that can be used to manually read
    tags out of the database without using the cache.

    If `location` is specified as true, then read each contents tag
    according to its location rather than an address. This allows one
    to perform a translation of the tags in case the function chunks
    are at different addresses than when the tags were read.
    """

    def __new__(cls, location=False):
        '''Read all of the tags defined within the database.'''
        return cls.everything(location=location)

    ## reading the content from a function
    @classmethod
    def content(cls, ea):
        '''Iterate through every tag belonging to the contents of the function at `ea`.'''
        F = func.by(ea)

        # iterate through every address in the function
        for ea in func.iterate(F):
            ui.navigation.set(ea)

            # yield the tags
            res = db.tag(ea)
            if res: yield ea, res
        return

    ## reading the tags from a frame
    @classmethod
    def frame(cls, ea):
        '''Iterate through each field within the frame belonging to the function `ea`.'''
        F = func.by(ea)

        # iterate through all of the frame's members
        try:
            res = func.frame(F)
        except internal.exceptions.MissingTypeOrAttribute:
            logging.info(u"{:s}.frame({:#x}) : Skipping function at {:#x} due to a missing frame.".format('.'.join([__name__, cls.__name__]), ea, ea))
            return

        for member in res.members:
            # if ida has named it and there's no comment, then skip
            if lvarNameQ(member.name) and not member.comment:
                continue

            # if it's a structure, then the type is the structure name
            if isinstance(member.type, struc.structure_t):
                logging.debug(u"{:s}.frame({:#x}) : Storing structure-based type as name for field {:+#x} with tne type {!s}.".format('.'.join([__name__, cls.__name__]), ea, member.offset, internal.utils.string.repr(member.type)))
                type = member.type.name

            # otherwise, the type is a tuple that we can serializer
            else:
                type = member.type

            # otherwise, it's just a regular field. so we can just save what's important.
            yield member.offset, (member.name, type, member.comment)
        return

    ## reading everything from the entire database
    @classmethod
    def everything(cls, location=False):
        """Read all of the tags defined within the database.

        Returns a tuple of the format `(Globals, Contents, Frames)`. Each field
        is a dictionary keyed by location or offset that retains the tags that
        were read. If the boolean `location` was specified then key each
        contents tag by location instead of address.
        """
        global read

        # read the globals and the contents
        six.print_(u'--> Grabbing globals...', file=output)
        Globals = { ea : res for ea, res in read.globals() }

        # read all content
        six.print_(u'--> Grabbing contents from all functions...', file=output)
        Contents = { loc : res for loc, res in read.contents(location=location) }

        # read the frames
        six.print_(u'--> Grabbing frames from all functions...', file=output)
        Frames = {ea : res for ea, res in read.frames()}

        # return everything back to the user
        return Globals, Contents, Frames

    ## reading the globals from the database
    @staticmethod
    def globals():
        '''Iterate through all of the tags defined globally witin the database.'''
        ea, sentinel = db.config.bounds()

        # loop till we hit the end of the database
        while ea < sentinel:
            ui.navigation.auto(ea)
            funcQ = func.within(ea)

            # figure out which tag function to use
            f = func.tag if funcQ else db.tag

            # grab the tag and yield it
            res = f(ea)
            if res: yield ea, res

            # if we're in a function, then seek to the next chunk
            if funcQ:
                _, ea = func.chunk(ea)
                continue

            # otherwise, try the next address till we hit a sentinel value
            try: ea = db.a.next(ea)
            except internal.exceptions.OutOfBoundsError: ea = sentinel
        return

    ## reading the contents from the entire database
    @staticmethod
    def contents(location=False):
        """Iterate through the contents tags for all the functions within the database.

        Each iteration yields a tuple of the format `(location, tags)` where
        `location` can be either an address or a chunk identifier and offset
        depending on whether `location` was specified as true or not.
        """
        global read

        # Iterate through each function in the database
        for ea in db.functions():

            # it's faster to precalculate the chunks here
            F, chunks = func.by(ea), [ch for ch in func.chunks(ea)]

            # Iterate through the function's contents yielding each tag
            for ea, res in read.content(ea):
                loc = addressToLocation(ea, chunks=chunks) if location else ea
                yield loc, res
            continue
        return

    ## reading the frames from the entire database
    @staticmethod
    def frames():
        '''Iterate through the fields of each frame for all the functions defined within the database.'''
        global read

        for ea in db.functions():
            ui.navigation.procedure(ea)
            res = dict(read.frame(ea))
            if res: yield ea, res
        return

### Applying tags to the database
class apply(object):
    """
    This namespace contains tools that can be used to apply tags that
    have been previously read back into the database.

    Various functions defined within this namespace take a variable number of
    keyword arguments which represent a mapping for the tag names. When a
    tag name was specified, this mapping will be used to rename the tags
    before actually writing them back into the database.
    """

    def __new__(cls, Globals_Contents_Frames, **tagmap):
        '''Apply the tags in the argument `(Globals, Contents, Frames)` from the `Globals_Contents_Frames` tuple back into the database.'''
        res = Globals, Contents, Frames = Globals_Contents_Frames
        return cls.everything(res, **tagmap)

    ## applying the content to a function
    @classmethod
    def content(cls, Contents, **tagmap):
        '''Apply `Contents` back into a function's contents within the database.'''
        global apply
        return apply.contents(Contents, **tagmap)

    ## applying a frame to a function
    @classmethod
    def frame(cls, ea, frame, **tagmap):
        '''Apply the fields from `frame` back into the function at `ea`.'''
        tagmap_output = u", {:s}".format(u', '.join(u"{:s}={:s}".format(internal.utils.string.escape(k), internal.utils.string.escape(v)) for k, v in tagmap.items())) if tagmap else ''

        # nothing to do here, so we gtfo
        if not frame:
            return

        # grab the function's frame
        try:
            F = func.frame(ea)

        # if no frame exists for the function, we'll need to create it
        except internal.exceptions.MissingTypeOrAttribute:

            # first we figure out the bounds of our members in order to figure out the the lvars and args sizes
            framekeys = {item for item in frame.keys()}
            minimum, maximum = min(framekeys), max(framekeys)

            # calculate the size of regs by first finding everything that begins at offset 0
            res = sorted(offset for offset in framekeys if offset >= 0)

            # now we look for anything near offset 0 that begins with a space (which should be a register)
            regs = 0
            for offset in res:
                name, type, _ = frame[offset]
                if not name.startswith(' '): break

                # if type is a string, then treat it as a structure so we can calculate a size
                if isinstance(type, six.string_types):
                    try:
                        st = struc.by(type)
                    except internal.exceptions.StructureNotFoundError:
                        logging.fatal(u"{:s}.frame({:#x}, ...{:s}): Unable to find structure \"{:s}\" for member {:+#x} in order to calculate register size for function at {:+#x}. Using register size of {:+#x}.".format('.'.join([__name__, cls.__name__]), ea, tagmap_output, internal.utils.string.escape(type, '"'), offset, ea, regs))
                        break
                    type = [(int, 1), st.size]

                # extract the size components and calculate the total number of bytes
                realtype, reallength = type if isinstance(type, builtins.list) else [type, 1]
                _, realsize = realtype
                cb = realsize * reallength

                # add it to the current aggregate of the register size
                regs += cb

            # finally we can create the frame
            logging.warning(u"{:s}.frame({:#x}, ...{:s}) : Creating a new frame for function {:#x} with the parameters lvars={:+#x} regs={:+#x} args={:+#x}.".format('.'.join([__name__, cls.__name__]), ea, tagmap_output, ea, abs(minimum), regs, abs(maximum)))
            F = func.frame.new(ea, abs(minimum), regs, abs(maximum) - regs)

        # iterate through our dictionary of members
        for offset, (name, type, comment) in frame.items():

            # first try and locate the member
            try:
                member = F.members.by_offset(offset)
            except:
                member = None

            # if we didn't find a member, then try and add it with what we currently know
            if member is None:
                logging.warning(u"{:s}.frame({:#x}, ...{:s}) : Unable to find frame member at {:+#x}. Attempting to create the member with the name (\"{:s}\"), type ({!s}), and comment (\"{:s}\").".format('.'.join([__name__, cls.__name__]), ea, tagmap_output, offset, internal.utils.string.escape(name, '"'), internal.utils.string.repr(type), internal.utils.string.escape(comment, '"')))
                try:
                    member = F.members.add(name, type, offset)
                except:
                    logging.fatal(u"{:s}.frame({:#x}, ...{:s}) : Unable to add frame member at {:+#x}. Skipping application of the name (\"{:s}\"), type ({!s}), and comment (\"{:s}\") to it.".format('.'.join([__name__, cls.__name__]), ea, tagmap_output, offset, internal.utils.string.escape(name, '"'), internal.utils.string.repr(type), internal.utils.string.escape(comment, '"')))
                    continue

            # check if the name has changed or is different in some way
            if member.name != name:
                log = logging.info if lvarNameQ(member.name) else logging.warning
                log(u"{:s}.frame({:#x}, ...{:s}) : Renaming frame member {:+#x} from the name \"{:s}\" to \"{:s}\".".format('.'.join([__name__, cls.__name__]), ea, tagmap_output, offset, internal.utils.string.escape(member.name, '"'), internal.utils.string.escape(name, '"')))
                member.name = name

            # check what's going to be overwritten with different values prior to doing it
            state, res = (internal.comment.decode(cmt) for cmt in [member.comment, comment])

            # transform the new tag state using the tagmap
            new = { tagmap.get(name, name) : value for name, value in res.items() }

            # check if the tag mapping resulted in the deletion of a tag
            if len(new) != len(res):
                reskeys, newkeys = ({item for item in items.keys()} for items in [res, new])
                for name in reskeys - newkeys:
                    logging.warning(u"{:s}.frame({:#x}, ...{:s}) : Refusing requested tag mapping as it results in the tag \"{:s}\" overwriting tag \"{:s}\" for the frame member {:+#x}. The value {!s} would be overwritten by {!s}.".format('.'.join([__name__, cls.__name__]), ea, tagmap_output, internal.utils.string.escape(name, '"'), internal.utils.string.escape(tagmap[name], '"'), offset, internal.utils.string.repr(res[name]), internal.utils.string.repr(res[tagmap[name]])))
                pass

            # warn the user about what's going to be overwritten prior to doing it
            statekeys, newkeys = ({item for item in items.keys()} for items in [state, new])
            for name in statekeys & newkeys:
                if state[name] == new[name]: continue
                logging.warning(u"{:s}.frame({:#x}, ...{:s}) : Overwriting tag \"{:s}\" for frame member {:+#x} with new value {!s}. The old value was {!s}.".format('.'.join([__name__, cls.__name__]), ea, tagmap_output, internal.utils.string.escape(name, '"'), offset, internal.utils.string.repr(new[name]), internal.utils.string.repr(state[name])))

            # now we can update the current dictionary
            mapstate = { name : value for name, value in new.items() if state.get(name, dummy) != value }
            state.update(mapstate)

            # convert it back to a multi-lined comment and assign it
            member.comment = internal.comment.encode(state)

            # if the type is a string, then figure out which structure to use
            if isinstance(type, six.string_types):
                try:
                    member.type = struc.by(type)
                except internal.exceptions.StructureNotFoundError:
                    logging.warning(u"{:s}.frame({:#x}, ...{:s}): Unable to find structure \"{:s}\" for member at {:+#x}. Skipping it.".format('.'.join([__name__, cls.__name__]), ea, tagmap_output, internal.utils.string.escape(type, '"'), offset))

            # otherwise, it's a pythonic tuple that we can just assign
            else:
                member.type = type
            continue
        return

    ## apply everything to the entire database
    @classmethod
    def everything(cls, Globals_Contents_Frames, **tagmap):
        '''Apply the tags in the argument `(Globals, Contents, Frames)` from the `Globals_Contents_Frames` tuple back into the database.'''
        global apply
        Globals, Contents, Frames = Globals_Contents_Frames

        ## convert a sorted list keyed by an address into something that updates ida's navigation pointer
        def update_navigation(xs, setter):
            '''Call `setter` on ea for each iteration of list `xs`.'''
            for x in xs:
                ea, _ = x
                setter(ea)
                yield x
            return

        ## convert a sorted list keyed by a location into something that updates ida's navigation pointer
        def update_navigation_contents(xs, setter):
            '''Call `setter` on location for each iteration of list `xs`.'''
            for x in xs:
                loc, _ = x
                ea = locationToAddress(loc)
                setter(ea)
                yield x
            return

        ## handle globals
        six.print_(u"--> Writing globals... ({:d} entr{:s})".format(len(Globals), 'y' if len(Globals) == 1 else 'ies'), file=output)
        iterable = sorted(Globals.items(), key=operator.itemgetter(0))
        res = apply.globals(update_navigation(iterable, ui.navigation.auto), **tagmap)
        # FIXME: verify that res matches number of Globals

        ## handle contents
        six.print_(u"--> Writing function contents... ({:d} entr{:s})".format(len(Contents), 'y' if len(Contents) == 1 else 'ies'), file=output)
        iterable = sorted(Contents.items(), key=operator.itemgetter(0))
        res = apply.contents(update_navigation_contents(iterable, ui.navigation.set), **tagmap)
        # FIXME: verify that res matches number of Contents

        ## update any frames
        six.print_(u"--> Applying frames to each function... ({:d} entr{:s})".format(len(Frames), 'y' if len(Frames) == 1 else 'ies'), file=output)
        iterable = sorted(Frames.items(), key=operator.itemgetter(0))
        res = apply.frames(update_navigation(iterable, ui.navigation.procedure), **tagmap)
        # FIXME: verify that res matches number of Frames

        return

    ## applying tags to the globals
    @staticmethod
    def globals(Globals, **tagmap):
        '''Apply the tags in `Globals` back into the database.'''
        global apply
        cls, tagmap_output = apply.__class__, u", {:s}".format(u', '.join(u"{:s}={:s}".format(internal.utils.string.escape(oldtag), internal.utils.string.escape(newtag)) for oldtag, newtag in tagmap.items())) if tagmap else ''

        count = 0
        for ea, res in Globals:
            ns = func if func.within(ea) else db

            # grab the current (old) tag state
            state = ns.tag(ea)

            # transform the new tag state using the tagmap
            new = { tagmap.get(name, name) : value for name, value in res.items() }

            # check if the tag mapping resulted in the deletion of a tag
            if len(new) != len(res):
                reskeys, newkeys = ({item for item in items.keys()} for items in [res, new])
                for name in reskeys - newkeys:
                    logging.warning(u"{:s}.globals(...{:s}) : Refusing requested tag mapping as it results in the tag \"{:s}\" overwriting the tag \"{:s}\" in the global {:#x}. The value {!s} would be replaced with {!s}.".format('.'.join([__name__, cls.__name__]), tagmap_output, internal.utils.string.escape(name, '"'), internal.utils.string.escape(tagmap[name], '"'), ea, internal.utils.string.repr(res[name]), internal.utils.string.repr(res[tagmap[name]])))
                pass

            # check what's going to be overwritten with different values prior to doing it
            statekeys, newkeys = ({item for item in items.keys()} for items in [state, new])
            for name in statekeys & newkeys:
                if state[name] == new[name]: continue
                logging.warning(u"{:s}.globals(...{:s}) : Overwriting tag \"{:s}\" for global at {:#x} with new value {!s}. Old value was {!s}.".format('.'.join([__name__, cls.__name__]), tagmap_output, internal.utils.string.escape(name, '"'), ea, internal.utils.string.repr(new[name]), internal.utils.string.repr(state[name])))

            # now we can apply the tags to the global address
            try:
                [ ns.tag(ea, name, value) for name, value in new.items() if state.get(name, dummy) != value ]
            except:
                logging.warning(u"{:s}.globals(...{:s}) : Unable to apply tags ({!s}) to global {:#x}.".format('.'.join([__name__, cls.__name__]), tagmap_output, internal.utils.string.repr(new), ea), exc_info=True)

            # increase our counter
            count += 1
        return count

    ## applying contents tags to all the functions
    @staticmethod
    def contents(Contents, **tagmap):
        '''Apply the tags in `Contents` back into each function within the database.'''
        global apply
        cls, tagmap_output = apply.__class__, u", {:s}".format(u', '.join(u"{:s}={:s}".format(internal.utils.string.escape(oldtag), internal.utils.string.escape(newtag)) for oldtag, newtag in tagmap.items())) if tagmap else ''

        count = 0
        for loc, res in Contents:
            ea = locationToAddress(loc)

            # warn the user if this address is not within a function
            if not func.within(ea):
                logging.warning(u"{:s}.contents(...{:s}) : Address {:#x} is not within a function. Using a global tag.".format('.'.join([__name__, cls.__name__]), tagmap_output, ea))

            # grab the current (old) tag state
            state = db.tag(ea)

            # transform the new tag state using the tagmap
            new = { tagmap.get(name, name) : value for name, value in res.items() }

            # check if the tag mapping resulted in the deletion of a tag
            if len(new) != len(res):
                reskeys, newkeys = ({item for item in items.keys()} for items in [res, new])
                for name in reskeys - newkeys:
                    logging.warning(u"{:s}.contents(...{:s}) : Refusing requested tag mapping as it results in the tag \"{:s}\" overwriting tag \"{:s}\" for the contents at {:#x}. The value {!s} would be overwritten by {!s}.".format('.'.join([__name__, cls.__name__]), tagmap_output, internal.utils.string.escape(name, '"'), internal.utils.string.escape(tagmap[name], '"'), ea, internal.utils.string.repr(res[name]), internal.utils.string.repr(res[tagmap[name]])))
                pass

            # inform the user if any tags are being overwritten with different values
            statekeys, newkeys = ({item for item in items.keys()} for items in [state, new])
            for name in statekeys & newkeys:
                if state[name] == new[name]: continue
                logging.warning(u"{:s}.contents(...{:s}) : Overwriting contents tag \"{:s}\" for address {:#x} with new value {!s}. Old value was {!s}.".format('.'.join([__name__, cls.__name__]), tagmap_output, internal.utils.string.escape(name, '"'), ea, internal.utils.string.repr(new[name]), internal.utils.string.repr(state[name])))

            # write the tags to the contents address
            try:
                [ db.tag(ea, name, value) for name, value in new.items() if state.get(name, dummy) != value ]
            except:
                logging.warning(u"{:s}.contents(...{:s}) : Unable to apply tags {!s} to location {:#x}.".format('.'.join([__name__, cls.__name__]), tagmap_output, internal.utils.string.repr(new), ea), exc_info=True)

            # increase our counter
            count += 1
        return count

    ## applying frames to all the functions
    @staticmethod
    def frames(Frames, **tagmap):
        '''Apply the fields from `Frames` back into each function's frame.'''
        global apply
        cls, tagmap_output = apply.__class__, u", {:s}".format(u', '.join(u"{:s}={:s}".format(internal.utils.string.escape(oldtag), internal.utils.string.escape(newtag)) for oldtag, newtag in tagmap.items())) if tagmap else ''

        count = 0
        for ea, res in Frames:
            try:
                apply.frame(ea, res, **tagmap)
            except:
                logging.warning(u"{:s}.frames(...{:s}) : Unable to apply tags ({!s}) to frame at {:#x}.".format('.'.join([__name__, cls.__name__]), tagmap_output, internal.utils.string.repr(res), ea), exc_info=True)

            # increase our counter
            count += 1
        return count

### Exporting tags from the database using the tag cache
class export(object):
    """
    This namespace contains tools that can be used to quickly
    export specific tags out of the database using the cache.

    If `location` is specified as true, then read each contents tag
    according to its location rather than an address. This allows one
    to perform a translation of the tags in case the function chunks
    are at different addresses than when the tags were read.
    """

    def __new__(cls, *tags, **location):
        '''Read the specified tags within the database using the cache.'''
        return cls.everything(*tags, **location)

    ## query the content from a function
    @classmethod
    def content(cls, F, *tags, **location):
        '''Iterate through the specified `tags` belonging to the contents of the function at `ea` using the cache.'''
        identity = lambda res: res
        translate = addressToLocation if location.get('location', False) else identity

        iterable = func.select(F, Or=tags) if tags else func.select(F)
        for ea, res in iterable:
            ui.navigation.set(ea)
            if res: yield translate(ea), res
        return

    ## query the frame from a function
    @classmethod
    def frame(cls, F, *tags):
        '''Iterate through each field containing the specified `tags` within the frame belonging to the function `ea`.'''
        global read, internal
        tags_ = { tag for tag in tags }

        for ofs, item in read.frame(F):
            field, type, comment = item

            # if the entire comment is in tags (like None) or no tags were specified, then save the entire member
            if not tags or comment in tags_:
                yield ofs, item
                continue

            # otherwise, decode the comment into a dictionary using only the tags the user asked for
            comment_ = internal.comment.decode(comment)
            comment_keys = {item for item in comment_.keys()}
            res = { name : comment_[name] for name in comment_keys & tags_ }

            # if anything was found, then re-encode it and yield to the user
            if res: yield ofs, (field, type, internal.comment.encode(res))
        return

    ## query the entire database for the specified tags
    @classmethod
    def everything(cls, *tags, **location):
        """Read all of the specified `tags` within the database using the cache.

        Returns a tuple of the format `(Globals, Contents, Frames)`. Each field
        is a dictionary keyed by location or offset that retains the tags that
        were read. If the boolean `location` was specified then key each
        contents tag by location instead of address.
        """
        global export

        # collect all the globals into a dictionary
        six.print_(u'--> Grabbing globals (cached)...', file=output)
        iterable = export.globals(*tags)
        Globals = {ea : res for ea, res in filter(None, iterable)}

        # grab all the contents into a dictionary
        six.print_(u'--> Grabbing contents from functions (cached)...', file=output)
        location = location.get('location', False)
        iterable = export.contents(*tags, location=location)
        Contents = {loc : res for loc, res in filter(None, iterable)}

        # grab any frames into a dictionary
        six.print_(u'--> Grabbing frames from functions (cached)...', file=output)
        iterable = export.frames(*tags)
        Frames = {ea : res for ea, res in filter(None, iterable)}

        # return it back to the user
        return Globals, Contents, Frames

    ## query all the globals matching the specified tags
    @staticmethod
    def globals(*tags):
        '''Iterate through all of the specified global `tags` within the database using the cache.'''
        iterable = db.select(Or=tags) if tags else db.select()
        for ea, res in iterable:
            ui.navigation.auto(ea)
            if res: yield ea, res
        return

    ## query all the contents in each function that match the specified tags
    @staticmethod
    def contents(*tags, **location):
        """Iterate through the specified contents `tags` within the database using the cache.

        Each iteration yields a tuple of the format `(location, tags)` where
        `location` can be either an address or a chunk identifier and offset
        depending on whether `location` was specified as true or not.
        """
        global export
        location = location.get('location', False)

        iterable = db.selectcontents(Or=tags) if tags else db.selectcontents()
        for F, res in iterable:
            for loc, res in export.content(F, *res, location=location):
                if res: yield loc, res
            continue
        return

    ## query all the frames that match the specified tags
    @staticmethod
    def frames(*tags):
        '''Iterate through the fields in each function's frame containing the specified `tags`.'''
        global export
        tags_ = {x for x in tags}

        for ea in db.functions():
            ui.navigation.procedure(ea)
            res = dict(export.frame(ea, *tags))
            if res: yield ea, res
        return

__all__ = ['list', 'read', 'export', 'apply']
