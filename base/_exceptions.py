import sys, builtins as E

class UnicodeException(E.BaseException):
    """
    A base exception that handles converting a unicode message
    into its UTF-8 form so that it can be emitted using Python's
    standard console.

    Copied from Python 2.7.15 implementation.
    """
    # tp_init
    def __init__(self, *args):
        self.__args__ = args
        self.__message__ = args[0] if len(args) == 1 else ''

    # Python2 can be emitted in more than one way which requires us
    # to implement both the Exception.__str__ and Exception.__unicode__
    # methods. If returning a regular string (bytes), then we need to
    # utf-8 encode the result because IDA's console will automatically
    # decode it.
    if sys.version_info.major < 3:

        # tp_str
        def __str__(self):
            length = len(self.args)
            if length == 0:
                return ""
            elif length == 1:
                item = self.args[0]
                return str(item.encode('utf8') if isinstance(item, unicode) else item)
            return str(self.args)

        def __unicode__(self):
            # return unicode(self.__str__())
            length = len(self.args)
            if length == 0:
                return u""
            elif length == 1:
                return unicode(self.args[0])
            return unicode(self.args)

    # Python3 really only requires us to implement this method when
    # emitting an exception. This is the same as a unicode type, so
    # we should be okay with casting the exception's arguments.
    else:

        # tp_str
        def __str__(self):
            length = len(self.args)
            if length == 0:
                return ""
            elif length == 1:
                item = self.args[0]
                return str(item)
            return str(self.args)

    # tp_repr
    def __repr__(self):
        repr_suffix = repr(self.args)
        name = type(self).__name__
        dot = name.rfind('.')
        shortname = name[1 + dot:] if dot > -1 else name
        return shortname + repr_suffix

    # tp_as_sequence
    def __iter__(self):
        for item in self.args:
            yield item
        return

    # tp_as_sequence
    def __getitem__(self, index):
        return self.args[index]
    def __getslice__(self, *indices):
        res = slice(*indices)
        return self.args[res]

    # tp_getset
    @property
    def message(self):
        return self.__message__
    @message.setter
    def message(self, message):
        # self.__message__ = "{!s}".format(message)
        self.__message__ = message
    @property
    def args(self):
        return self.__args__
    @args.setter
    def args(self, args):
        self.__args__ = tuple(item for item in args)

    # tp_methods
    def __reduce__(self):
        return self.args
    def __setstate__(self, pack):
        self.args = pack

class MissingTagError(UnicodeException, E.KeyError):
    """
    The requested tag at the specified address does not exist.
    """

class MissingFunctionTagError(MissingTagError):
    """
    The requested tag for the specified function does not exist.
    """

class MissingMethodError(UnicodeException, E.NotImplementedError):
    """
    A method belonging to a superclass that is required to be overloaded was called.
    """

class UnsupportedVersion(UnicodeException, E.NotImplementedError):
    """
    This functionality is not supported on the current version of IDA.
    """

class UnsupportedCapability(UnicodeException, E.NotImplementedError, E.EnvironmentError):
    """
    An unexpected or unsupported capability was specified.
    """

class ResultMissingError(UnicodeException, E.LookupError):
    """
    The requested item is missing from its results.
    """

class SearchResultsError(ResultMissingError):
    """
    No results were found.
    """

class DisassemblerError(UnicodeException, E.EnvironmentError):
    """
    An api call has thrown an error or was unsuccessful.
    """

class MissingTypeOrAttribute(UnicodeException, E.TypeError):
    """
    The specified location is missing some specific attribute or type.
    """

class InvalidTypeOrValueError(UnicodeException, E.TypeError, E.ValueError):
    """
    An invalid value or type was specified.
    """

class InvalidParameterError(InvalidTypeOrValueError, E.AssertionError):
    """
    An invalid parameter was specified by the user.
    """

class OutOfBoundsError(UnicodeException, E.ValueError):
    """
    The specified item is out of bounds.
    """

class AddressOutOfBoundsError(OutOfBoundsError, E.ArithmeticError):
    """
    The specified address is out of bounds.
    """

class IndexOutOfBoundsError(OutOfBoundsError, E.IndexError, E.KeyError):
    """
    The specified index is out of bounds.
    """

class ItemNotFoundError(ResultMissingError, E.KeyError):
    """
    The specified item or type was not found.
    """

class FunctionNotFoundError(ItemNotFoundError):
    """
    Unable to locate the specified function.
    """

class AddressNotFoundError(ItemNotFoundError):
    """
    Unable to locate the specified address.
    """

class SegmentNotFoundError(ItemNotFoundError):
    """
    Unable to locate the specified segment.
    """

class StructureNotFoundError(ItemNotFoundError):
    """
    Unable to locate the specified structure.
    """

class EnumerationNotFoundError(ItemNotFoundError):
    """
    Unable to locate the specified enumeration.
    """

class MemberNotFoundError(ItemNotFoundError):
    """
    Unable to locate the specified structure or enumeration member.
    """

class RegisterNotFoundError(ItemNotFoundError):
    """
    Unable to locate the specified register.
    """

class NetNodeNotFoundError(ItemNotFoundError):
    """
    Unable to locate the specified netnode.
    """

class ReadOrWriteError(UnicodeException, E.IOError, E.ValueError):
    """
    Unable to read or write the specified number of bytes .
    """

class InvalidFormatError(UnicodeException, E.KeyError, E.ValueError):
    """
    The specified data has an invalid format.
    """

class SerializationError(UnicodeException, E.ValueError, E.IOError):
    """
    There was an error while trying to serialize or deserialize the specified data.
    """

class SizeMismatchError(SerializationError):
    """
    There was an error while trying to serialize or deserialize the specified data due to its size not matching.
    """

class UnknownPrototypeError(UnicodeException, E.LookupError):
    """
    The requested prototype does not match any of the ones that are available.
    """

class DuplicateItemError(DisassemblerError, E.NameError):
    """
    The requested command has failed due to a duplicate item.
    """

#structure:742 and previous to it should output the module name, classname, and method
#comment:334 should catch whatever tree.find raises
#comment:100 (this needs some kind of error when the symbol or token component is not found)
#interface:283, interface:302, interface:620, interface:640 (this should be a NameError)
