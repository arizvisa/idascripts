r"""
Comment module (internal)

This module contains the functionality for encoding and decoding
arbitrary python objects into IDA's comments and is thus a major
component of the way the tag system in this plugin works.

These encoded python objects are constrained in that they must also
double as being human readable in IDA's disassembly view. This then
allows one to essentially store a dictionary within each comment that
can be used to read/write primitive python objects.

Each comment stored at an address is a list of key-value pairs
separated by newlines. Each key represents a tag and so as a comment,
it has the following appearance.

    [key1] value1
    [key2] value2
    ...

If a comment does not follow this format, then it assumed that the
comment's value is a simple unencoded tag and can be accessed via
the '' key (empty). This means that if your comment is simply the
string "HeapHandle", then its dictionary will look similar to
`{'' : 'HeapHandle'}`.

Unfortunately IDA has a limitation on the length of comments and so
arbitrarily long data will not be able to be stored. This includes
things such as more complex types or custom objects. If one truly
needs to store a more complex type then it is suggested that the user
marshal or pickle their object, compress it in some way, and then
base64 encode it at a given address with their key. Still this is not
recommended, but who am I to stop a user from wanting to be crazy.

Some of the values are encoded in order to retain any specific
information about the value as well as still allowing the user to read
the tag's immediate contents. By default all integers are always
encoded as hexadecimal. If you can't read hex, then you should save
your database and quit your job. Or you could also practice it I guess.
It's the next power of 2 from decimal and is hence pretty important.
Strings and other types that contain any line-breaking characters also
get encoded whereas both lists and most iterable types are stored as-is.

Some examples of how tag values are encoded are as follows:

    4021 -> 0xfb5
    -100 -> -0x64
    0.5 -> float(0.5)
    'hello world\nhow\'re ya' -> hello world\nhow're ya
    {10,20,30} -> set([10, 20, 30])

With regards to string, only certain characters are escaped because
I don't know if IDA's comments support unicode. So, the characters
that have special meaning are '\n', '\r', and '\t'. Similarly if a
backslash is escaped, it will result in a single '\'. If any other
character is prefixed with a backslash, it will decode into a character
that is prefixed with a backslash.
"""

import functools, operator, itertools, types
import collections, heapq, string
import sys, six, logging

import internal, idaapi
import codecs

### cheap data structure for doing pattern matching with
class pattern(object):
    class star(tuple): pass
    class maybe(tuple): pass

class node(dict):
    id = 0
    def __missing__(self, token):
        cls = self.__class__

        res = cls()
        res.id = self.id + len(self) + 1
        return self.setdefault(token, res)

class trie(node):
    def assign(self, symbols, value):
        res = [item for item in symbols]
        head = res.pop(0)
        symbols = tuple(res)

        head = head if hasattr(head, '__iter__') or len(head) > 1 else (head,)
        if isinstance(head, pattern.star):
            if len(symbols) <= 0:
                raise ValueError('Refusing to register the STAR(*) pattern as the last symbol')

            [ self.__setitem__(item, self) for item in head ]
            self.assign(symbols, value)
            return

        elif isinstance(head, pattern.maybe):
            if len(symbols) <= 0:
                raise ValueError('Refusing to register the MAYBE(?) pattern as the last symbol')
            head, res = tuple(head), trie()
            res.assign(symbols, value)
            [ self.__setitem__(item, res) for item in head ]
            self.assign(symbols, value)
            return

        elif len(symbols) > 0:
            [ self[item].assign(symbols, value) for item in head ]

        else:
            [ self.__setitem__(item, value) for item in head ]
        return

    def descend(self, symbols):
        yield self
        for i, symbol in enumerate(symbols):
            if not isinstance(self, node) or not operator.contains(self, symbol):
                raise KeyError(i, symbol)    # raise KeyError for .get() and .find()
            self = self[symbol]
            yield self
        return

    def get(self, symbols):
        for i, symbol in enumerate(self.descend(symbols)):
            continue
        if isinstance(symbol, node):
            raise KeyError(i, symbol)    # raise KeyError for our caller if we couldn't find anything
        return symbol

    def find(self, symbols):
        for i, symbol in enumerate(self.descend(symbols)):
            if not isinstance(symbol, node):
                return symbol
            continue
        raise KeyError(i, symbol)    # raise KeyError for our caller if we couldn't find anything

    def dump(self):
        cls = self.__class__
        # FIXME: doesn't support recursion
        def stringify(layer, indent=0, tab='  '):
            data = (k for k, v in layer.items() if not isinstance(v, node))
            result = []
            for k in data:
                result.append("{:s}{!r} -> {!r}".format(tab * indent, k, layer[k]))

            branches = [k for k, v in layer.items() if isinstance(v, node)]
            for k in branches:
                result.append("{:s}{!r}".format(tab * indent, k))
                branch_data = stringify(layer[k], 1 + indent, tab=tab)
                result.extend(branch_data)
            return result
        return '\n'.join(["{!r}({:d})".format(cls, self.id), '\n'.join(stringify(self))])

### cache for looking up encoder/decoder types
class cache(object):
    state, tree = collections.defaultdict(set), trie()

    @classmethod
    def register(cls, type, *characters):
        def result(definition):
            # add definition to constant search by specified type
            cls.state[type].add(definition)

            # add definition to symbolic search
            if characters:
                cls.tree.assign(characters, definition)

            return definition
        return result

    @classmethod
    def by(cls, instance):
        type = instance.__class__
        try:
            if type not in cls.state:
                type = next(t for t in cls.state if issubclass(type, t))
            res = next(enc for enc in cls.state[type] if enc.type(instance))
        except StopIteration:
            raise internal.exceptions.SerializationError(u"{:s}.by({!s}) : Unable to find an encoder for the serialization of the specified type ({!s}).".format('.'.join([__name__, cls.__name__]), type, type))
        return res

    @classmethod
    def match(cls, string):
        return cls.tree.find(string)

class default(object):
    @classmethod
    def type(cls, instance):
        return True
    @classmethod
    def encode(cls, instance):
        return repr(instance)
    @classmethod
    def decode(cls, data):
        return eval(data)

### type encoder/decoder registration
# FIXME: maybe figure out how to parse out an int from a long (which ends in 'L')
@cache.register(object, pattern.star(' \t'), pattern.maybe('-+'), '0123456789')
class _int(default):
    @classmethod
    def type(cls, instance):
        return isinstance(instance, six.integer_types)

    @classmethod
    def encode(cls, instance):
        return "{:-#x}".format(instance)

    @classmethod
    def decode(cls, data):
        if data.startswith('0x'):
            return int(data, 16)
        elif data.startswith('0o'):
            return int(data, 8)
        elif data.startswith('0o'):
            return int(data, 8)
        elif data.startswith('0b'):
            return int(data, 2)
        elif data.startswith('0y'):
            return int(data[2:], 2)
        return int(data)

@cache.register(object, pattern.star(' \t'), *'float(')
class _float(default):
    @classmethod
    def type(cls, instance):
        return isinstance(instance, float)
    @classmethod
    def encode(cls, instance):
        return "float({:f})".format(instance)

if sys.version_info.major < 3:
    @cache.register(str)
    class _str(default):
        """
        This encoder/decoder actually supports both ``unicode`` and regular
        ``str`` due to the ``type`` method checking both string types. Also,
        we use this class as a superclass for ``_unicode`` so that any kind
        of string will be encoded into a unicode string which will be
        converted into UTF8 when written into IDA.
        """

        @classmethod
        def type(cls, instance):
            return isinstance(instance, six.string_types)

        @classmethod
        def _unescape(cls, iterable):
            '''Invert the utils.character.unescape coroutine into a generator.'''
            state = internal.interface.collect_t(list, lambda agg, ch: agg + [ch])
            unescape = internal.utils.character.unescape(state); next(unescape)

            # iterate through each character in the string
            for ch in iterable:
                unescape.send(ch)

                # iterate through the results and yield them to the caller
                for ch in state.get():
                    yield ch

                # now we can start over
                state.reset()
            return

        @classmethod
        def _escape(cls, iterable):
            '''Invert the utils.character.escape coroutine into a generator.'''
            state = internal.interface.collect_t(list, lambda agg, ch: agg + [ch])
            escape = internal.utils.character.escape(state); next(escape)

            # iterate through each character in the string
            for ch in iterable:
                escape.send(ch)

                # iterate through the results and yield them to the caller
                for ch in state.get():
                    yield ch

                # empty our state and start over
                state.reset()
            return

        @classmethod
        def decode(cls, data):
            res = data if isinstance(data, unicode) else data.decode('utf8')
            iterable = (ch for ch in res.lstrip())
            return unicode().join(cls._unescape(iterable))

        @classmethod
        def encode(cls, instance):
            iterable = (item for item in instance)
            res = cls._escape(iterable)
            return unicode().join(res)

    @cache.register(unicode, pattern.star(' \t'), 'u', "'\"")
    class _unicode(_str):
        """
        This encoder/decoder really just a wrapper around the ``_str``
        class. Its encoder will simply escape the string in the exact
        same way as ``_str``. We register a pattern for it so that we
        can decode unicode strings encoded in their older format. Due
        to the older format requiring unicode strings to begin with
        the "u'" prefix, we can simply eval it in order to decode
        back to a unicode string.
        """

        @classmethod
        def type(cls, instance):
            return isinstance(instance, unicode)

        @classmethod
        def decode(cls, data):
            logging.warning(u"{:s}.decode({!s}) : Decoding a unicode string that was encoded using the old format.".format('.'.join([__name__, cls.__name__]), internal.utils.string.repr(data)))
            return eval(data)

else:
    @cache.register(bytes, pattern.star(' \t'), 'b', "'\"")
    class _bytes(default):
        @classmethod
        def type(cls, instance):
            return isinstance(instance, bytes)

        @classmethod
        def decode(cls, data):
            return eval(data)

        @classmethod
        def encode(cls, instance):
            return repr(instance)

    @cache.register(str)
    class _str(default):
        @classmethod
        def type(cls, instance):
            return isinstance(instance, six.string_types)

        @classmethod
        def _unescape(cls, iterable):
            '''Invert the utils.character.unescape coroutine into a generator.'''
            state = internal.interface.collect_t(list, lambda agg, ch: agg + [ch])
            unescape = internal.utils.character.unescape(state); next(unescape)

            # iterate through each character in the string
            for ch in iterable:
                unescape.send(ch)

                # iterate through the results and yield them to the caller
                for ch in state.get():
                    yield ch

                # now we can start over
                state.reset()
            return

        @classmethod
        def _escape(cls, iterable):
            '''Invert the utils.character.escape coroutine into a generator.'''
            state = internal.interface.collect_t(list, lambda agg, ch: agg + [ch])
            escape = internal.utils.character.escape(state); next(escape)

            # iterate through each character in the string
            for ch in iterable:
                escape.send(ch)

                # iterate through the results and yield them to the caller
                for ch in state.get():
                    yield ch

                # empty our state and start over
                state.reset()
            return

        @classmethod
        def decode(cls, data):
            res = data if isinstance(data, six.string_types) else data.decode('utf8')
            return str().join(cls._unescape(iter(res.lstrip())))

        @classmethod
        def encode(cls, instance):
            res = cls._escape(iter(instance))
            return str().join(res)

@cache.register(dict, pattern.star(' \t'), '{')
class _dict(default):
    @classmethod
    def type(cls, instance):
        return isinstance(instance, dict)
    @classmethod
    def encode(cls, instance):
        f = lambda item: "{:-#x}".format(item) if isinstance(item, six.integer_types) else "{!r}".format(item)
        return '{' + ', '.join("{:s}: {!r}".format(f(key), instance[key]) for key in instance) + '}'

@cache.register(list, pattern.star(' \t'), '[')
class _list(default):
    @classmethod
    def type(cls, instance):
        return isinstance(instance, list)
    @classmethod
    def encode(cls, instance):
        f = lambda item: "{:-#x}".format(item) if isinstance(item, six.integer_types) else "{!r}".format(item)
        return '[' + ', '.join(map(f, instance)) + ']'

@cache.register(tuple, pattern.star(' \t'), '(')
class _tuple(default):
    @classmethod
    def type(cls, instance):
        return isinstance(instance, tuple)
    @classmethod
    def encode(cls, instance):
        f = lambda item: "{:-#x}".format(item) if isinstance(item, six.integer_types) else "{!r}".format(item)
        return '(' + ', '.join(map(f, instance)) + (', ' if len(instance) == 1 else '') + ')'

@cache.register(set, pattern.star(' \t'), *'set([')
class _set(default):
    @classmethod
    def type(cls, instance):
        return isinstance(instance, set)
    @classmethod
    def encode(cls, instance):
        f = lambda item: "{:-#x}".format(item) if isinstance(item, six.integer_types) else "{!r}".format(item)
        return 'set([' + ', '.join(map(f, instance)) + '])'

### general tag encoding/decoding
class tag(object):
    """
    Namespace for encoding and decoding a tag and it's value.
    """

    ## Tag name
    class name(object):
        """
        Namespace for encoding and decoding a tag's name.
        """

        prefix, suffix = '[]'
        backslash = '\\'

        mappings = {
            prefix : backslash + prefix,
            suffix : backslash + suffix,
            ' ' : r' ',
            backslash : backslash + backslash,
        }

        @classmethod
        def encode(cls, iterable, result):
            '''Given an `iterable` string, send each character in a printable form to `result`.'''

            # construct a transformer that writes characters to result
            escape = internal.utils.character.escape(result); next(escape)

            # send the key prefix
            result.send(cls.prefix)

            # now we can actually process the string
            for ch in iterable:

                # first check if character has an existing key mapping
                if operator.contains(cls.mappings, ch):
                    for ch in operator.getitem(cls.mappings, ch):
                        result.send(ch)

                # otherwise pass it to the regular escape function
                else:
                    escape.send(ch)

                continue

            # submit the suffix and we're good
            result.send(cls.suffix)
            return

        @classmethod
        def decode(cls, iterable, result):
            '''Given an `iterable`, decode it into a unicode string and send it to `result`.'''

            # first create our aggregate type for decoding into
            agg = internal.interface.collect_t(unicode if sys.version_info.major < 3 else str, operator.add)

            # construct a transformer that unescapes characters to result
            unescape = internal.utils.character.unescape(agg); next(unescape)

            # first we'll skip the initial whitespace
            ch = next(iterable)
            while ch != cls.prefix and internal.utils.character.whitespaceQ(ch):
                ch = next(iterable)

            # check if it matches our prefix (which it should)
            if ch != cls.prefix:
                raise internal.exceptions.InvalidFormatError(u"{:s}.decode({!s}, {!s}) : Input for tag name does not begin with the proper character ('{:s}') and instead starts with '{:s}'.".format('.'.join([__name__, 'tag', cls.__name__]), iterable, result, internal.utils.string.escape(cls.prefix, '\''), internal.utils.string.escape(ch, '\'')))

            # read each character up to the sentinel
            agg.reset()
            ch = next(iterable)

            # loop until we find our suffix
            while ch != cls.suffix:

                # submit our character to the unescape transformer while
                # it's a backslash
                while ch in u'\\':
                    unescape.send(ch)
                    ch = next(iterable)

                # otherwise, continue to unescape it and look for a suffix
                unescape.send(ch)
                ch = next(iterable)

            # the last character read should be our suffix, so fail if otherwise
            if ch != cls.suffix:
                raise internal.exceptions.InvalidFormatError(u"{:s}.decode({!s}, {!s}) : Input for tag name does not terminate with the correct character ('{:s}') and instead is terminated with '{:s}'.".format('.'.join([__name__, 'tag', cls.__name__]), iterable, result, internal.utils.string.escape(cls.suffix, '\''), internal.utils.string.escape(ch, '\'')))

            # at this point, agg should have our unescaped key that we can submit
            result.send(agg.get())

    ## Tag value
    class value(object):
        """
        Namespace for encoding and decoding a tag's value.
        """

        @classmethod
        def encode(cls, iterable, result):
            '''Read a value from `iterable` and encode it into `result`.'''
            value = next(iterable)
            t = cache.by(value)
            for ch in t.encode(value):
                result.send(ch)
            return

        @classmethod
        def decode(cls, iterable, result):
            '''Given an `iterable`, decode it into a unicode string and send it to `result`.'''
            res = []

            # first we'll skip whitespace
            ch = next(iterable, '\n')
            while ch != '\n' and internal.utils.character.whitespaceQ(ch):
                res.append(ch)
                ch = next(iterable, '\n')

            # if we were just whitespace, then decode it as
            # a unicode string to return
            if ch == '\n':
                cons = unicode if sys.version_info.major < 3 else str
                value_s = cons().join(res)
                result.send(_str.decode(value_s))
                return

            # now we'll continue reading until the sentinel character
            value_l = []
            while ch != '\n':
                value_l.append(ch)
                ch = next(iterable, '\n')
            value_s = str().join(value_l)

            # now we'll try to find out what type to decode it as
            try:
                t = cache.match(value_s)

            except KeyError:
                t = _str

            # we have a type and a value. try to decode it
            try:
                value = t.decode(value_s)

            # if we weren't able to, then fall back to a string
            except Exception as E:
                t = _str
                logging.debug(u"{:s}.decode({!s}, {!s}) : Assuming value ({!s}) is of type {!s}.".format('.'.join([__name__, 'tag', cls.__name__]), iterable, result, internal.utils.string.repr(value_s), t))
                value = t.decode(value_s)

            # now we can submit it
            result.send(value)

    @classmethod
    def encode(cls, key, value):
        '''Encode the provided `key` and `value` into a line fit for a comment.'''
        result = internal.interface.collect_t(unicode if sys.version_info.major < 3 else str, operator.add)

        # first encode the beginning of the name
        tag.name.encode(iter(key), result)

        # store some whitespace in between
        result.send(' ')

        # next encode the value component
        tag.value.encode(iter([value]), result)

        # now we can return the resulting string
        return result.get()

    @classmethod
    def decode(cls, iterable):
        '''Read the line in `iterable` and return the key and its value.'''

        # first decode the key
        key = internal.interface.collect_t(object, lambda agg, key: key)
        tag.name.decode(iterable, key)

        # next decode its value
        value = internal.interface.collect_t(object, lambda agg, value: value)
        tag.value.decode(iterable, value)

        # plain and simple...
        return key.get(), value.get()

### Encoding and decoding of a comment
def decode(data, default=u''):
    """Decode all the `(key, value)` pairs from the string `data` delimited by newlines.

    If unable to decode the key and value from a line in `data`, then use `default` as the key name.
    """

    # if data is empty, then return an empty dict
    if not data:
        return {}

    # initialize some variables to keep our state
    res = {}
    key, value = internal.interface.collect_t(object, lambda _, key: key), internal.interface.collect_t(object, lambda _, value: value)

    # iterate through each line in the data
    for line in data.split(u'\n'):
        iterable = (ch for ch in line)

        # try and decode the key and the value from the line
        try:
            k, v = tag.decode(iterable)

        # if the key wasn't terminated properly, or formatted correctly,
        # then append it to the default key separated by newlines
        except (StopIteration, internal.exceptions.InvalidFormatError) as E:
            items = filter(None, res.setdefault(default, u'').split(u'\n'))
            k, v = default, u'\n'.join(itertools.chain(items, [line]))

        # warn the user if we're overwriting a key in the tag that
        # already exists.
        else:
            if operator.contains(res, k):
                logging.warning(u"{:s}.decode(..., {!s}) : Overwriting the tag name {!s} from its old value ({!r}) with the new value ({!r}).".format('.'.join([__name__]), internal.utils.string.repr(default), internal.utils.string.repr(k), res[k], v))

        # add our item to the result dictionary
        res[k] = v

    # return the dictionary we decoded
    return res

def encode(dict):
    '''Encode a dictionary into a multi-line string encoded as a list of tags.'''
    res = []

    # walk each item in the dictionary
    for k, v in (dict or {}).items():
        # encode the key and value from the dictionary
        line = tag.encode(k, v)

        # aggregate it into our list
        res.append(line)

    # join them by newlines and return them to the caller
    return '\n'.join(res)

def check(data):
    '''Check that the string `data` has the correct format by trying to decode it.'''
    res = map(iter, (data or '').split('\n'))
    try:
        [tag.decode(item) for item in res]
    except Exception as E:
        return False
    return True

### Tag reference counting
class tagging(object):
    """
    This namespace is essentially the configuration of the tagging
    database. This configurations specifies how to marshal and
    compress reference counts that are retained by the tagging
    infrastructure.

    The keys for the dictionaries that store the reference count
    are named according to ``tagging.__tags__`` for the tag names
    and ``tagging.__address__`` for the tag addresses. In order
    to access the tagging database, the netnode is returned by
    the ``tagging.node()`` function.

    When a database has been successfully created, a hook is
    responsible for calling the ``tagging.__init_tagcache__()``
    function. This will then create a netnode with the name
    specified in ``tagging.__node__``.
    """
    __node__ = '$ tagcache'
    __tags__, __address__ = 'name', 'address'

    marshaller = __import__('marshal')
    codec = __import__('codecs').lookup('bz2_codec')

    @classmethod
    def __init_tagcache__(cls, idp_modname):
        '''Hook to create a new netnode that will contain our tag-cache.'''
        res = cls.node(cached=False)
        logging.debug(u"{:s}.init_tagcache('{:s}') : Successfully opened up the netnode \"{:s}\" for the tag cache and using the identifier ({:#x}) to reference it.".format('.'.join([__name__, cls.__name__]), internal.utils.string.escape(idp_modname, '\''), internal.utils.string.escape(cls.__node__, '"'), res))

    @classmethod
    def __nw_init_tagcache__(cls, nw_code, is_old_database):
        idp_modname = idaapi.get_idp_name()
        return cls.__init_tagcache__(idp_modname)

    @classmethod
    def node(cls, cached=True):
        '''Fetch the netnode containing the tag-cache which should be named "$ tagcache".

        If `cached` is changed to False, then always update the node's identifier.
        '''
        if cached and hasattr(cls, '__cache_id__'):
            return cls.__cache_id__

        # Explicitly try to fetch the netnode containing the tag-cache. If we were
        # unable to find it, then create it and use that instead.
        node = internal.netnode.get(cls.__node__)
        if node == idaapi.BADADDR:
            node = internal.netnode.new(cls.__node__)

        # Cache the identifier for the netnode inside a class attribute
        cls.__cache_id__ = node
        return node

class contents(tagging):
    '''Tagging for an address within a function (contents)'''
    """
    This namespace is used to update the tag state for any content tags
    associated with a function in the database. The address for the top
    of the function represents a key within the netnode that is used to
    fetch the blob and the supval which contains a marshall'd dictionary
    and a marshall'd set. These are stored within the `tagging.node()`
    netnode withn the tag `contents.btag`.

    The marshall'd dictionary that is stored in the netnode's blob is
    used to retain a dictionary of reference counts for both the tag
    names and the addresses that they reside at. Anytime a tag is
    written or removed, the reference count for both the name and the
    address is adjusted.

    Due to a size limit of a blob, the supval for the tagging node is
    used to store the tag names that are used within a function as a
    marshall'd ``set``. This ``set`` is used to verify that the tag
    names within the contents of the function correspond with the
    reference count that is stored within the marshall'd dictionary
    in the blob.
    """

    ## for each function's content
    # netnode.blob[fn.start_ea, btag] = marshal.dumps({'name', 'address'})
    # netnode.sup[fn.start_ea] = marshal.dumps({tagnames})

    #btag = idaapi.stag         # XXX: apparently 'S' is used for comments
    btag = idaapi.atag

    @classmethod
    def _key(cls, ea):
        '''Converts the address `ea` to a key that's used to store contents data for the specified function.'''
        res = idaapi.get_func(ea)
        return internal.interface.range.start(res) if res else None

    @classmethod
    def _read_header(cls, target, ea):
        """Read the contents dictionary out of the supval belonging to the function at `target`.

        If `target` is ``None``, then use the address of the function containing `ea`.
        """
        node, key = tagging.node(), cls._key(ea) if target is None else target
        if key is None:
            raise internal.exceptions.FunctionNotFoundError(u"{:s}._read_header({!r}, {:#x}) : Unable to locate a function for target ({!r}) at {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, key, ea))

        view = internal.netnode.sup.get(node, key, type=memoryview)
        if view is None:
            return None
        encdata = view.tobytes()

        try:
            data, sz = cls.codec.decode(encdata)
            if len(encdata) != sz:
                raise internal.exceptions.SizeMismatchError(u"{:s}._read_header({!r}, {:#x}) : The number of bytes that was decoded did not match the expected size ({:#x}<>{:#x}).".format('.'.join([__name__, cls.__name__]), target, ea, sz, len(encdata)))
        except Exception as E:
            logging.warning(u"{:s}._read_header({!r}, {:#x}) : An exception {!r} was raised while trying to decode the cache header for address {:#x} from the sup cache associated with key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, E, ea, key), exc_info=True)
            logging.info(u"{:s}._read_header({!r}, {:#x}) : Error occurred while decoding the following data from the sup cache: {!r}.".format('.'.join([__name__, cls.__name__]), target, ea, encdata))
            raise internal.exceptions.SerializationError(u"{:s}._read_header({!r}, {:#x}) : Unable to decode the cache header for address {:#x} from the sup cache associated with key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, ea, key))

        try:
            result = cls.marshaller.loads(data)
        except Exception as E:
            logging.info(u"{:s}._read_header({!r}, {:#x}) : Error occurred while unmarshalling the following data from the sup cache: {!r}.".format('.'.join([__name__, cls.__name__]), target, ea, data))
            raise internal.exceptions.SerializationError(u"{:s}._read_header({!r}, {:#x}) : Unable to unmarshal the cache header for address {:#x} from the sup cache associated with key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, ea, key))
        return result

    @classmethod
    def _write_header(cls, target, ea, value):
        """Write the specified `value` into the contents supval belonging to the supval of the function at `target`.

        If `target` is ``None`` then use `ea` to locate the function.
        If `value` is ``None``, then remove the supval at the specified `target`.
        """
        node, key = tagging.node(), cls._key(ea) if target is None else target
        if key is None:
            raise internal.exceptions.FunctionNotFoundError(u"{:s}._write_header({!r}, {:#x}, {!s}) : Unable to determine the key for target ({!r}) at {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), target, ea))

        # If our header is empty, then we just need to remove the supvalue
        if not value:
            return bool(internal.netnode.sup.remove(node, key))

        try:
            data = cls.marshaller.dumps(value)

        except Exception as E:
            logging.info(u"{:s}._write_header({!r}, {:#x}, {!s}) : Error occurred while marshalling the following data for the cache header: {!r}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), value))
            raise internal.exceptions.SerializationError(u"{:s}._write_header({!r}, {:#x}, {!s}) : Unable to marshal the cache header at address {:#x} for the sup cache associated with key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), ea, key))

        try:
            encdata, sz = cls.codec.encode(data)
            if sz != len(data):
                raise internal.exceptions.SizeMismatchError(u"{:s}._write_header({!r}, {:#x}, {!s}) : The number of bytes that was encoded did not match the expected size ({:#x}<>{:#x}).".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), sz, len(data)))

        except Exception as E:
            logging.warning(u"{:s}._write_header({!r}, {:#x}, {!s}) : An exception {!r} was raised while trying to encode the cache header at address {:#x} for the sup cache associated with key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), E, ea, key), exc_info=True)
            logging.info(u"{:s}._write_header({!r}, {:#x}, {!s}) : Error encoding the following data for the cache header: {!r}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), data))
            raise internal.exceptions.SerializationError(u"{:s}._write_header({!r}, {:#x}, {!s}) : Unable to encode the contents at {:#x} for the sup cache associated with key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), ea, key))

        if len(encdata) > internal.netnode.sup.MAX_SIZE:
            logging.warning(u"{:s}._write_header({!r}, {:#x}, {!s}) : Reached tag limit size ({:#x}>{:#x}) in function with key {:#x}. Possible tag-cache corruption encountered.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), len(encdata), internal.netnode.sup.MAX_SIZE, key))

        ok = internal.netnode.sup.set(node, key, encdata)
        return bool(ok)

    @classmethod
    def _read(cls, target, ea):
        """Reads the value from the contents supval for the specific `target`.

        If `target` is undefined or ``None`` then use `ea` to locate the function.
        """
        node, key = tagging.node(), cls._key(ea) if target is None else target
        if key is None:
            raise internal.exceptions.FunctionNotFoundError(u"{:s}._read({!r}, {:#x}) : Unable to determine the key for the target ({!r}) at {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, target, ea))

        encdata = internal.netnode.blob.get(key, cls.btag)
        if encdata is None:
            return None

        try:
            data, sz = cls.codec.decode(encdata)
            if len(encdata) != sz:
                raise internal.exceptions.SizeMismatchError(u"{:s}._read({!r}, {:#x}) : The number of bytes that was decoded did not match the expected size ({:#x}<>{:#x}).".format('.'.join([__name__, cls.__name__]), target, ea, sz, len(encdata)))

        except Exception as E:
            logging.warning(u"{:s}._read({!r}, {:#x}) : An exception {!r} was raised while trying to decode the contents for address {:#x} from the blob cache ({!s}) associated with key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, E, ea, cls.btag, key), exc_info=True)
            logging.info(u"{:s}._read({!r}, {:#x}) : Error while decoding the following data from the blob cache: {!r}.".format('.'.join([__name__, cls.__name__]), target, ea, encdata))
            raise internal.exceptions.SerializationError(u"{:s}._read({!r}, {:#x}) : Unable to decode the contents for address {:#x} from the blob cache ({!s}) associated with key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, ea, cls.btag, key))

        try:
            result = cls.marshaller.loads(data)

        except Exception as E:
            logging.info(u"{:s}._read({!r}, {:#x}) : Error while unmarshalling the following data from the blob cache: {!r}.".format('.'.join([__name__, cls.__name__]), target, ea, data))
            raise internal.exceptions.SerializationError(u"{:s}._read({!r}, {:#x}) : Unable to unmarshal the contents for address {:#x} from the blob cache ({!s}) associated with key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, ea, cls.btag, key))
        return result

    @classmethod
    def _write(cls, target, ea, value):
        """Writes a `value` to the contents supval for the specific `target`.

        If `target` is undefined or ``None`` then use `ea` to locate the function.
        If `value` is ``None``, then erase the value from the supval.
        """
        node, key = tagging.node(), cls._key(ea) if target is None else target
        if key is None:
            raise internal.exceptions.FunctionNotFoundError(u"{:s}._write({!r}, {:#x}, {!r}) : Unable to determine the key for target ({!r}) at {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, value, target, ea))

        # erase cache and blob if no data is specified
        if not value:
            try:
                ok = cls._write_header(target, ea, None)
                if not ok:
                    logging.debug(u"{:s}._write({!r}, {:#x}, {!s}) : Unable to remove the address {:#x} from the cache header associated with the key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), ea, key))

            finally:
                count = internal.netnode.blob.remove(key, cls.btag)
                logging.debug(u"{:s}._write({!r}, {:#x}, {!s}) : Removed {:d} blob{:s} ({!s}) associated with the key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), count, '' if count == 1 else 's', cls.btag, key))

            return True

        # update blob for given address
        res = value
        try:
            data = cls.marshaller.dumps(res)

        except Exception as E:
            logging.info(u"{:s}._write({!r}, {:#x}, {!s}) : Error while unmarshalling the following data for the blob cache: {!r}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), res))
            raise internal.exceptions.SerializationError(u"{:s}._write({!r}, {:#x}, {!s}) : Unable to marshal the contents at address {:#x} for the blob cache ({!s}) associated with key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), ea, cls.btag, key))

        try:
            encdata, sz = cls.codec.encode(data)

        except Exception as E:
            logging.info(u"{:s}._write({!r}, {:#x}, {!s}) : Error encoding the following data for the blob cache: {!r}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), data))
            raise internal.exceptions.SerializationError(u"{:s}._write({!r}, {:#x}, {!s}) : Unable to encode the contents at address {:#x} for the blob cache ({!s}) associated with key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), ea, cls.btag, key))

        if sz != len(data):
            raise internal.exceptions.SizeMismatchError(u"{:s}._write({!r}, {:#x}, {!s}) : The number of bytes that was encoded did not match the expected size ({:#x}<>{:#x}).".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), sz, len(data)))

        # write blob
        ok = internal.netnode.blob.set(key, cls.btag, encdata)
        if not ok:
            logging.info(u"{:s}._write({!r}, {:#x}, {!s}) : Error while writing the following data to the blob cache: {!r}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), encdata))
            raise internal.exceptions.DisassemblerError(u"{:s}._write({!r}, {:#x}, {!s}) : Unable to write the contents for address {:#x} to the blob cache ({!s}) associated with the key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), ea, cls.btag, key))

        # update sup cache with keys
        res = {item for item in value.keys()}
        ok = cls._write_header(target, ea, res)
        if not ok:
            raise internal.exceptions.DisassemblerError(u"{:s}._write({!r}, {:#x}, {!s}) : Unable to write the cache header for address {:#x} associated with the key {:#x}.".format('.'.join([__name__, cls.__name__]), target, ea, internal.utils.string.repr(value), ea, key))
        return ok

    @classmethod
    def iterate(cls):
        '''Yield each address and names for all of the contents tags in the database according to what is written into the tagging supval.'''
        node = tagging.node()
        for ea in internal.netnode.sup.fiter(node):
            view = internal.netnode.sup.get(node, ea, type=memoryview)
            encdata = view.tobytes()
            data, sz = cls.codec.decode(encdata)
            if len(encdata) != sz:
                logging.warning(u"{:s}.iterate() : Error while decoding the tag names out of the sup cache for address {:#x} due to the length of encoded data not matching the expected size ({:#x}<>{:#x}).".format('.'.join([__name__, cls.__name__]), ea, len(encdata), sz))
            res = cls.marshaller.loads(data)
            yield ea, res
        return

    @classmethod
    def inc(cls, address, name, **target):
        """Increase the ref count for the given `address` and `name` belonging to the function `target`.

        If `target` is undefined or ``None`` then use `address` to locate the function.
        """
        key = target.get('target', None)
        res = cls._read(key, address) or {}
        state, cache = res.get(cls.__tags__, {}), res.get(cls.__address__, {})

        state[name] = refs = state.get(name, 0) + 1
        cache[address] = cache.get(address, 0) + 1

        if state: res[cls.__tags__] = state
        else: del res[cls.__tags__]

        if cache: res[cls.__address__] = cache
        else: del res[cls.__address__]

        cls._write(key, address, res)
        return refs

    @classmethod
    def dec(cls, address, name, **target):
        """Decreate the ref count for the given `address` and `name` belonging to the function `target`.

        If `target` is undefined or ``None`` then use `address` to locate the function.
        """
        key = target.get('target', None)
        res = cls._read(key, address) or {}
        state, cache = res.get(cls.__tags__, {}), res.get(cls.__address__, {})

        refs, count = state.pop(name, 0) - 1, cache.pop(address, 0) - 1
        if refs > 0:
            state[name] = refs

        if count > 0:
            cache[address] = count

        if state: res[cls.__tags__] = state
        else: res.pop(cls.__tags__, None)

        if cache: res[cls.__address__] = cache
        else: res.pop(cls.__address__, None)

        cls._write(key, address, res)
        return refs

    @classmethod
    def name(cls, address, **target):
        """Return all the tag names (``set``) for the contents of the function `target`.

        If `target` is undefined or ``None`` then use `address` to locate the function.
        """
        key = target.get('target', None)
        res = cls._read(key, address) or {}
        res = res.get(cls.__tags__, {})
        return {item for item in res.keys()}

    @classmethod
    def address(cls, address, **target):
        """Return all the addresses (``sorted``) with tags in the contents for the function `target`.

        If `target` is undefined or ``None`` then use `address` to locate the function.
        """
        key = target.get('target', None)
        res = cls._read(key, address) or {}
        res = res.get(cls.__address__, {})
        return sorted(res.keys())

    @classmethod
    def set_name(cls, address, name, count, **target):
        """Set the contents tag count for the function `target` and `name` to `count`.

        If `target` is undefined or ``None`` then use `address` to locate the function.
        """
        key = target.get('target', None)
        state = cls._read(key, address) or {}

        res = state.get(cls.__tags__, {})
        if count > 0:
            res[name] = count
        else:
            res.pop(name, None)

        if res:
            state[cls.__tags__] = res
        else:
            state.pop(cls.__tags__, None)

        try:
            ok = cls._write(key, address, state)
            if ok:
                return state
        except Exception as E:
            logging.warning(u"{:s}.set_name({:#x}, {!r}, {:d}{:s}) : An exception {!r} was raised while trying to update the name cache for address {:#x}.".format('.'.join([__name__, cls.__name__]), address, name, count, ', {:s}'.format(internal.utils.string.kwargs(target)) if target else '', E, address), exc_info=True)
        raise internal.exceptions.ReadOrWriteError(u"{:s}.set_name({:#x}, {!r}, {:d}{:s}) : Unable to update the name cache for address {:#x}.".format('.'.join([__name__, cls.__name__]), address, name, count, ', {:s}'.format(internal.utils.string.kwargs(target)) if target else '', address))

    @classmethod
    def set_address(cls, address, count, **target):
        """Set the contents tag count for the function `target` and `address` to `count`.

        If `target` is undefined or ``None`` then use `address` to locate the function.
        """
        key = target.get('target', None)
        state = cls._read(key, address) or {}

        res = state.get(cls.__address__, {})
        if count > 0:
            res[address] = count
        else:
            res.pop(address, None)

        if res:
            state[cls.__address__] = res
        else:
            state.pop(cls.__address__, None)

        try:
            ok = cls._write(key, address, state)
            if ok:
                return state
        except Exception as E:
            logging.warning(u"{:s}.set_address({:#x}, {:d}{:s}) : An exception {!r} was raised while trying to update the cache for address {:#x}.".format('.'.join([__name__, cls.__name__]), address, count, ', {:s}'.format(internal.utils.string.kwargs(target)) if target else '', E, address), exc_info=True)
        raise internal.exceptions.ReadOrWriteError(u"{:s}.set_address({:#x}, {:d}{:s}) : Unable to write to the cache for address {:#x}.".format('.'.join([__name__, cls.__name__]), address, count, ', {:s}'.format(internal.utils.string.kwargs(target)) if target else '', address))

class globals(tagging):
    """
    This namespace is used to update the tag state for all the globals in
    the database. Each global tag has its target address and its name and
    is managed by keeping track of a reference count.

    The reference count is stored within a netnode as defined by
    `tagging.node()`. The refcount for each address containing a
    tag is stored in an altval keyed by the address. The refcount
    for each tag name is stored in a hashval keyed by the tags
    name.
    """

    ## FIXME: for each global/function
    # netnode.alt[address] = refcount
    # netnode.hash[name] = refcount

    @classmethod
    def inc(cls, address, name):
        '''Increase the global tag count for the given `address` and `name`.'''
        node, eName = tagging.node(), internal.utils.string.to(name)

        cName = (internal.netnode.hash.get(node, eName, type=int) or 0) + 1
        cAddress = (internal.netnode.alt.get(node, address) or 0) + 1

        internal.netnode.hash.set(node, eName, cName)
        internal.netnode.alt.set(node, address, cAddress)

        return cName

    @classmethod
    def dec(cls, address, name):
        '''Decrease the global tag count for the given `address` and `name`.'''
        node, eName = tagging.node(), internal.utils.string.to(name)

        cName = (internal.netnode.hash.get(node, eName, type=int) or 1) - 1
        cAddress = (internal.netnode.alt.get(node, address) or 1) - 1

        if cName < 1:
            internal.netnode.hash.remove(node, eName)
        else:
            internal.netnode.hash.set(node, eName, cName)

        if cAddress < 1:
            internal.netnode.alt.remove(node, address)
        else:
            internal.netnode.alt.set(node, address, cAddress)

        return cName

    @classmethod
    def name(cls):
        '''Return all the tag names (``set``) in the specified database (globals and func-tags)'''
        node = tagging.node()
        return { internal.utils.string.of(name) for name in internal.netnode.hash.fiter(node) }

    @classmethod
    def address(cls):
        '''Return all the tag addresses (``sorted``) in the specified database (globals and func-tags)'''
        return sorted(ea for ea, _ in internal.netnode.alt.fiter(tagging.node()))

    @classmethod
    def set_name(cls, name, count):
        '''Set the global tag count for `name` in the database to `count`.'''
        node, eName = tagging.node(), internal.utils.string.to(name)
        res = internal.netnode.hash.get(node, eName, type=int)
        internal.netnode.hash.set(node, eName, count)
        return res

    @classmethod
    def set_address(cls, address, count):
        '''Set the global tag count for `address` in the database to `count`.'''
        node = tagging.node()
        res = internal.netnode.alt.get(node, address)
        internal.netnode.alt.set(node, address, count)
        return res
