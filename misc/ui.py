"""
User Interface module

This module exposes a number of tools and class definitions for
interacting with IDA's user interface. This includes things such
as getting the current state of user input, information about
windows that are in use as well as utilities for simplifying the
customization of the interface.

There are a few namespaces that are provided in order to get the
current state. The ``ui.current`` namespace allows for one to get
the current address, function, segment, window, as well as a number
of other things.

A number of namespaces defined within this module also allows a
user to interact with the different windows that are currently
in use. This can allow for one to automatically show or hide a
window that they wish to expose to the user.
"""

import six, builtins
import sys, os, time, functools, inspect
import logging

import idaapi, internal
import database as _database, segment as _segment

## TODO:
# locate window under current cursor position
# pop-up a menu item
# pop-up a form/messagebox
# another item menu to toolbar
# find the QAction associated with a command (or keypress)

def application():
    '''Return the current instance of the IDA Application.'''
    raise internal.exceptions.MissingMethodError

class ask(object):
    """
    This namespace contains utilities for asking the user for some
    particular type of information. These will typically require a
    user-interface of some sort and will block while waiting for the
    user to respond.

    If the `default` parameter is specified to any of the functions
    within this namespace, then its value will be used by default
    in the inbox that is displayed to the user.
    """
    @internal.utils.multicase()
    def __new__(cls, **default):
        '''Request the user choose from the options "yes", "no", or "cancel".'''
        return cls(u'', **default)
    @internal.utils.multicase(message=six.string_types)
    def __new__(cls, message, **default):
        '''Request the user choose from the options "yes", "no", or "cancel" using the specified `message` as the prompt.'''
        return cls.yn(message, **default)

    @internal.utils.multicase()
    @classmethod
    def yn(cls, **default):
        '''Request the user choose from the options "yes", "no", or "cancel".'''
        return cls.yn(u'', **default)
    @internal.utils.multicase(message=six.string_types)
    @classmethod
    @internal.utils.string.decorate_arguments('message')
    def yn(cls, message, **default):
        """Request the user choose from the options "yes", "no", or "cancel" using the specified `message` as the prompt.

        If any of the options are specified as a boolean, then it is
        assumed that this option will be the default. If the user
        chooses "cancel", then this value will be returned instead of
        the value ``None``.
        """
        state = {'no': getattr(idaapi, 'ASKBTN_NO', 0), 'yes': getattr(idaapi, 'ASKBTN_YES', 1), 'cancel': getattr(idaapi, 'ASKBTN_CANCEL', -1)}
        results = {state['no']: False, state['yes']: True}
        if default:
            keys = {item for item in default.keys()}
            keys = {item.lower() for item in keys if default.get(item, False)}
            dflt = next((item for item in keys), 'cancel')
        else:
            dflt = 'cancel'
        res = idaapi.ask_yn(state[dflt], internal.utils.string.to(message))
        return results.get(res, None)

    @internal.utils.multicase()
    @classmethod
    def address(cls, **default):
        '''Request the user provide an address.'''
        return cls.address(u'', **default)
    @internal.utils.multicase(message=six.string_types)
    @classmethod
    @internal.utils.string.decorate_arguments('message')
    def address(cls, message, **default):
        """Request the user provide an address using the specified `message` as the prompt.

        If the `valid` parameter is specified, then verify that the
        address is within the bounds of the database. If the `bounds`
        parameter is specified, then verify that the address chosen
        by the user is within the provided bounds.
        """
        dflt = next((default[k] for k in ['default', 'address', 'ea', 'addr'] if k in default), current.address())

        # Ask the user for an address...
        ea = idaapi.ask_addr(dflt, internal.utils.string.to(message))

        # If we received idaapi.BADADDR, then the user gave us a bogus
        # value that we need to return None for.
        if ea == idaapi.BADADDR:
            return None

        # Grab the bounds that we'll need to compare the address to from
        # the parameters or the database configuration.
        bounds = next((default[k] for k in ['bounds'] if k in default), _database.config.bounds())

        # If we were asked to verify the address, or we were given some
        # boundaries to check it against..then do that here.
        if default.get('verify', 'bounds' in default):
            l, r = bounds
            return ea if l <= ea < r else None

        # Otherwise, we can just return the address here.
        return ea

    @internal.utils.multicase()
    @classmethod
    def integer(cls, **default):
        '''Request the user provide an integer.'''
        return cls.integer(u'', **default)
    @internal.utils.multicase(message=six.string_types)
    @classmethod
    @internal.utils.string.decorate_arguments('message')
    def integer(cls, message, **default):
        '''Request the user provide an integer using the specified `message` as the prompt.'''
        dflt = next((default[k] for k in ['default', 'integer', 'long', 'int'] if k in default), getattr(cls, '__last_integer__', 0))

        # Ask the user for some kind of integer...
        integer = idaapi.ask_long(dflt, internal.utils.string.to(message))

        # If we actually received an integer, then cache it so that we can
        # reuse it as the default the next time this function gets called.
        if integer is not None:
            cls.__last_integer__ = integer

        return integer

    @internal.utils.multicase()
    @classmethod
    def segment(cls, **default):
        '''Request the user provide a segment.'''
        return cls.segment(u'', **default)
    @internal.utils.multicase(message=six.string_types)
    @classmethod
    @internal.utils.string.decorate_arguments('message')
    def segment(cls, message, **default):
        '''Request the user provide a segment using the specified `message` as the prompt.'''
        res = current.segment()
        dflt = next((default[k] for k in ['default', 'segment', 'seg'] if k in default), internal.interface.range.start(res) if res else idaapi.BADADDR)
        ea = idaapi.ask_seg(dflt, internal.utils.string.to(message))

        # Try and convert whatever it was that we were given into an actual segment.
        try:
            seg = _segment.by(ea)

        # If we got an exception, then just set our result to None so that we can
        # let the caller figure out how much they really want it.
        except Exception:
            return None

        # Return the segment_t back to the caller.
        return seg

    @internal.utils.multicase()
    @classmethod
    def string(cls, **default):
        '''Request the user provide a string.'''
        return cls.string(u'', **default)
    @internal.utils.multicase(message=six.string_types)
    @classmethod
    @internal.utils.string.decorate_arguments('message', 'default', 'text', 'string')
    def string(cls, message, **default):
        '''Request the user provide a string using the specified `message` as the prompt.'''
        dflt = next((default[k] for k in ['default', 'text', 'string'] if k in default), None) or u''

        # FIXME: we should totally expose the history id to the caller in some
        #        way.. but after some fiddling around with it, I can't seem to
        #        make it actually do anything.

        result = idaapi.ask_str(internal.utils.string.to(dflt), idaapi.HIST_IDENT, internal.utils.string.to(message))
        return internal.utils.string.of(result)

    @internal.utils.multicase()
    @classmethod
    def note(cls, **default):
        '''Request the user provide a multi-lined string.'''
        return cls.note(u'', **default)
    @internal.utils.multicase(message=six.string_types)
    @classmethod
    @internal.utils.string.decorate_arguments('message', 'default', 'text', 'string')
    def note(cls, message, **default):
        """Request the user provide a multi-lined string using the specified `message` as the prompt.

        If the `length` parameter is provided as an integer, then constrain
        the length of the user's input to the integer that was specified.
        """
        dflt = next((default[k] for k in ['default', 'text', 'string'] if k in default), None) or u''
        length = next((default[k] for k in ['length', 'max', 'maxlength'] if k in default), 0)
        result = idaapi.ask_text(length, internal.utils.string.to(dflt), internal.utils.string.to(message))
        return internal.utils.string.of(result)

class current(object):
    """
    This namespace contains tools for fetching information about the
    current selection state. This can be used to get the state of
    thigns that are currently selected such as the address, function,
    segment, clipboard, widget, or even the current window in use.
    """
    @classmethod
    def address(cls):
        '''Return the current address.'''
        return idaapi.get_screen_ea()
    @classmethod
    def color(cls):
        '''Return the color of the current item.'''
        ea = cls.address()
        return idaapi.get_item_color(ea)
    @classmethod
    def function(cls):
        '''Return the current function.'''
        ea = cls.address()
        res = idaapi.get_func(ea)
        if res is None:
            raise internal.exceptions.FunctionNotFoundError(u"{:s}.function() : Unable to locate the current function.".format('.'.join([__name__, cls.__name__])))
        return res
    @classmethod
    def segment(cls):
        '''Return the current segment.'''
        ea = cls.address()
        return idaapi.getseg(ea)
    @classmethod
    def status(cls):
        '''Return the IDA status.'''
        raise internal.exceptions.UnsupportedCapability(u"{:s}.status() : Unable to return the current status of IDA.".format('.'.join([__name__, cls.__name__])))
    @classmethod
    def symbol(cls):
        '''Return the current highlighted symbol name.'''
        if idaapi.__version__ < 7.0:
            return idaapi.get_highlighted_identifier()

        # IDA 7.0 way of getting the currently selected text
        viewer = idaapi.get_current_viewer()
        res = idaapi.get_highlight(viewer)
        if res and res[1]:
            return res[0]
        return res
    @classmethod
    def selection(cls):
        '''Return the current address range of whatever is selected'''
        view = idaapi.get_current_viewer()
        left, right = idaapi.twinpos_t(), idaapi.twinpos_t()
        ok = idaapi.read_selection(view, left, right)
        if not ok:
            raise internal.exceptions.DisassemblerError(u"{:s}.selection() : Unable to read the current selection.".format('.'.join([__name__, cls.__name__])))
        pl_l, pl_r = left.place(view), right.place(view)
        ea_l, ea_r = internal.interface.address.inside(pl_l.ea, pl_r.ea)
        return internal.interface.bounds_t(ea_l, ea_r)
    selected = internal.utils.alias(selection, 'current')
    @classmethod
    def opnum(cls):
        '''Return the currently selected operand number.'''
        return idaapi.get_opnum()
    @classmethod
    def widget(cls):
        '''Return the current widget that the mouse is hovering over.'''
        # XXX: there's probably a better way to do this rather than looking
        #      at the mouse cursor position
        x, y = mouse.position()
        return widget.at((x, y))
    @classmethod
    def window(cls):
        '''Return the current window that is being used.'''
        global window
        # FIXME: cast this to a QWindow somehow?
        return window.main()

class state(object):
    """
    This namespace is for fetching or interacting with the current
    state of IDA's interface. These are things such as waiting for
    IDA's analysis queue, or determining whether the function is
    being viewed in graph view or not.
    """
    @classmethod
    def graphview(cls):
        '''Returns true if the current function is being viewed in graph view mode.'''
        res = idaapi.get_inf_structure()
        if idaapi.__version__ < 7.0:
            return res.graph_view != 0
        return res.is_graph_view()

    @classmethod
    def wait(cls):
        '''Wait until IDA's autoanalysis queues are empty.'''
        return idaapi.autoWait() if idaapi.__version__ < 7.0 else idaapi.auto_wait()

    @classmethod
    def beep(cls):
        '''Beep using IDA's interface.'''
        return idaapi.beep()

    @classmethod
    def refresh(cls):
        '''Refresh all of IDA's windows.'''
        global disassembly
        ok = idaapi.refresh_lists() if idaapi.__version__ < 7.0 else idaapi.refresh_choosers()
        return ok and disassembly.refresh()

wait, beep, refresh = internal.utils.alias(state.wait, 'state'), internal.utils.alias(state.beep, 'state'), internal.utils.alias(state.refresh, 'state')

class appwindow(object):
    """
    Base namespace used for interacting with the windows provided by IDA.
    """
    @classmethod
    def open(cls, *args):
        '''Open or show the window belonging to the namespace.'''
        global widget
        res = cls.__open__(*args) if args else cls.__open__(*getattr(cls, '__open_defaults__', ()))
        return widget.form(res)

    @classmethod
    def close(cls):
        '''Close or hide the window belonging to the namespace.'''
        res = cls.open()
        return res.deleteLater()

class disassembly(appwindow):
    """
    This namespace is for interacting with the Disassembly window.
    """
    __open__ = staticmethod(idaapi.open_disasm_window)
    __open_defaults__ = ('Disassembly', )

    @classmethod
    def refresh(cls):
        '''Refresh the main IDA disassembly view.'''
        return idaapi.refresh_idaview_anyway()

class exports(appwindow):
    """
    This namespace is for interacting with the Exports window.
    """
    __open__ = staticmethod(idaapi.open_exports_window)
    __open_defaults__ = (idaapi.BADADDR, )

class imports(appwindow):
    """
    This namespace is for interacting with the Imports window.
    """
    __open__ = staticmethod(idaapi.open_imports_window)
    __open_defaults__ = (idaapi.BADADDR, )

class names(appwindow):
    """
    This namespace is for interacting with the Names window.
    """
    __open__ = staticmethod(idaapi.open_names_window)
    __open_defaults__ = (idaapi.BADADDR, )

    @classmethod
    def refresh(cls):
        '''Refresh the names list.'''
        return idaapi.refresh_lists() if idaapi.__version__ < 7.0 else idaapi.refresh_choosers()
    @classmethod
    def size(cls):
        '''Return the number of elements in the names list.'''
        return idaapi.get_nlist_size()
    @classmethod
    def contains(cls, ea):
        '''Return whether the address `ea` is referenced in the names list.'''
        return idaapi.is_in_nlist(ea)
    @classmethod
    def search(cls, ea):
        '''Return the index of the address `ea` in the names list.'''
        return idaapi.get_nlist_idx(ea)

    @classmethod
    def at(cls, index):
        '''Return the address and the symbol name of the specified `index`.'''
        ea, name = idaapi.get_nlist_ea(index), idaapi.get_nlist_name(index)
        return ea, internal.utils.string.of(name)
    @classmethod
    def name(cls, index):
        '''Return the name at the specified `index`.'''
        res = idaapi.get_nlist_name(index)
        return internal.utils.string.of(res)
    @classmethod
    def ea(cls, index):
        '''Return the address at the specified `index`.'''
        return idaapi.get_nlist_ea(index)

    @classmethod
    def iterate(cls):
        '''Iterate through all of the address and symbols in the names list.'''
        for idx in range(cls.size()):
            yield cls.at(idx)
        return

class functions(appwindow):
    """
    This namespace is for interacting with the Functions window.
    """
    __open__ = staticmethod(idaapi.open_funcs_window)
    __open_defaults__ = (idaapi.BADADDR, )

class structures(appwindow):
    """
    This namespace is for interacting with the Structures window.
    """
    __open__ = staticmethod(idaapi.open_structs_window)
    __open_defaults__ = (idaapi.BADADDR, 0)

class strings(appwindow):
    """
    This namespace is for interacting with the Strings window.
    """
    __open__ = staticmethod(idaapi.open_strings_window)
    __open_defaults__ = (idaapi.BADADDR, idaapi.BADADDR, idaapi.BADADDR)

    @classmethod
    def __on_openidb__(cls, code, is_old_database):
        if code != idaapi.NW_OPENIDB or is_old_database:
            raise internal.exceptions.InvalidParameterError(u"{:s}.__on_openidb__({:#x}, {:b}) : Hook was called with an unexpected code or an old database.".format('.'.join([__name__, cls.__name__]), code, is_old_database))
        config = idaapi.strwinsetup_t()
        config.minlen = 3
        config.ea1, config.ea2 = idaapi.cvar.inf.minEA, idaapi.cvar.inf.maxEA
        config.display_only_existing_strings = True
        config.only_7bit = True
        config.ignore_heads = False

        # aggregate all the string types for IDA 6.95x
        if idaapi.__version__ < 7.0:
            res = [idaapi.ASCSTR_TERMCHR, idaapi.ASCSTR_PASCAL, idaapi.ASCSTR_LEN2, idaapi.ASCSTR_UNICODE, idaapi.ASCSTR_LEN4, idaapi.ASCSTR_ULEN2, idaapi.ASCSTR_ULEN4]

        # otherwise use IDA 7.x's naming scheme
        else:
            res = [idaapi.STRTYPE_TERMCHR, idaapi.STRTYPE_PASCAL, idaapi.STRTYPE_LEN2, idaapi.STRTYPE_C_16, idaapi.STRTYPE_LEN4, idaapi.STRTYPE_LEN2_16, idaapi.STRTYPE_LEN4_16]

        config.strtypes = functools.reduce(lambda t, c: t | (2**c), res, 0)
        if not idaapi.set_strlist_options(config):
            raise internal.exceptions.DisassemblerError(u"{:s}.__on_openidb__({:#x}, {:b}) : Unable to set the default options for the string list.".format('.'.join([__name__, cls.__name__]), code, is_old_database))
        #assert idaapi.build_strlist(config.ea1, config.ea2), "{:#x}:{:#x}".format(config.ea1, config.ea2)

    @classmethod
    def refresh(cls):
        '''Refresh the strings list.'''
        return idaapi.refresh_lists() if idaapi.__version__ < 7.0 else idaapi.refresh_choosers()
    @classmethod
    def size(cls):
        '''Return the number of elements in the strings list.'''
        return idaapi.get_strlist_qty()
    @classmethod
    def at(cls, index):
        '''Return the string at the specified `index`.'''
        si = idaapi.string_info_t()

        # FIXME: this isn't being used correctly
        ok = idaapi.get_strlist_item(si, index)
        if not ok:
            raise internal.exceptions.DisassemblerError(u"{:s}.at({:d}) : The call to `idaapi.get_strlist_item({:d})` returned {!r}.".format('.'.join([__name__, cls.__name__]), index, index, res))
        return si
    @classmethod
    def get(cls, index):
        '''Return the address and the string at the specified `index`.'''
        si = cls.at(index)
        get_contents = idaapi.get_strlit_contents if hasattr(idaapi, 'get_strlit_contents') else idaapi.get_ascii_contents
        res = get_contents(si.ea, si.length, si.type)
        return si.ea, internal.utils.string.of(res)
    @classmethod
    def iterate(cls):
        '''Iterate through all of the address and strings in the strings list.'''
        for index in range(cls.size()):
            yield cls.get(index)
        return

class segments(appwindow):
    """
    This namespace is for interacting with the Segments window.
    """
    __open__ = staticmethod(idaapi.open_segments_window)
    __open_defaults__ = (idaapi.BADADDR, )

class notepad(appwindow):
    """
    This namespace is for interacting with the Notepad window.
    """
    __open__ = staticmethod(idaapi.open_notepad_window)
    __open_defaults__ = ()

    @classmethod
    def open(cls, *args):
        '''Open or show the notepad window and return its ``QtWidgets.QPlainTextEdit`` widget.'''
        widget = super(notepad, cls).open(*args)
        children = (item for item in widget.children() if isinstance(item, PyQt5.QtWidgets.QPlainTextEdit))
        result = builtins.next(children, None)
        if result is None:
            raise internal.exceptions.ItemNotFoundError(u"{:s}.open({!s}) : Unable to locate the QtWidgets.QPlainTextEdit widget.".format('.'.join([__name__, cls.__name__]), ', '.join(map(internal.utils.repr, args))))
        return result

    @classmethod
    def close(cls):
        '''Close or hide the notepad window.'''
        editor = cls.open()
        widget = editor.parent()
        return widget.deleteLater()

    @classmethod
    def get(cls):
        '''Return the string that is currently stored within the notepad window.'''
        editor = cls.open()
        return editor.toPlainText()

    @internal.utils.multicase(string=six.string_types)
    @classmethod
    def set(cls, string):
        '''Set the text that is currently stored within the notepad window to `string`.'''
        editor = cls.open()
        return editor.setPlainText(string)

    @internal.utils.multicase(items=(builtins.list, builtins.tuple))
    @classmethod
    def set(cls, items):
        '''Set each line that is currently stored within the notepad window to `items`.'''
        return cls.set('\n'.join(items))

    @internal.utils.multicase(string=six.string_types)
    @classmethod
    def append(cls, string):
        '''Append the provided `string` to the current text that is stored within the notepad window.'''
        editor = cls.open()
        return editor.appendPlainText(string)

    @internal.utils.multicase()
    @classmethod
    def cursor(cls):
        '''Return the ``QtGui.QTextCursor`` used by the notepad window.'''
        editor = cls.open()
        return editor.textCursor()

    @internal.utils.multicase()
    @classmethod
    def cursor(cls, cursor):
        '''Set the ``QtGui.QTextCursor`` for the notepad window to `cursor`.'''
        editor = cls.open()
        return editor.setTextCursor(cursor)

class timer(object):
    """
    This namespace is for registering a python callable to a timer in IDA.
    """
    clock = {}
    @classmethod
    def register(cls, id, interval, callable):
        '''Register the specified `callable` with the requested `id` to be called at every `interval`.'''
        if id in cls.clock:
            idaapi.unregister_timer(cls.clock[id])

        # XXX: need to create a closure that can terminate when signalled
        cls.clock[id] = res = idaapi.register_timer(interval, callable)
        return res
    @classmethod
    def unregister(cls, id):
        '''Unregister the specified `id`.'''
        raise internal.exceptions.UnsupportedCapability(u"{:s}.unregister({!s}) : A lock or a signal is needed here in order to unregister this timer safely.".format('.'.join([__name__, cls.__name__]), id))
        idaapi.unregister_timer(cls.clock[id])
        del(cls.clock[id])
    @classmethod
    def reset(cls):
        '''Remove all the registered timers.'''
        for id, clk in cls.clock.items():
            idaapi.unregister_timer(clk)
            del(cls.clock[id])
        return

### updating the state of the colored navigation band
class navigation(object):
    """
    This namespace is for updating the state of the colored navigation band.
    """
    if all(not hasattr(idaapi, name) for name in ['show_addr', 'showAddr']):
        __set__ = staticmethod(lambda ea: None)
    else:
        __set__ = staticmethod(idaapi.showAddr if idaapi.__version__ < 7.0 else idaapi.show_addr)

    if all(not hasattr(idaapi, name) for name in ['show_auto', 'showAuto']):
        __auto__ = staticmethod(lambda ea, t: None)
    else:
        __auto__ = staticmethod(idaapi.showAuto if idaapi.__version__ < 7.0 else idaapi.show_auto)

    @classmethod
    def set(cls, ea):
        '''Set the auto-analysis address on the navigation bar to `ea`.'''
        return cls.__set__(ea)

    @classmethod
    def auto(cls, ea, **type):
        """Set the auto-analysis address and type on the navigation bar to `ea`.

        If `type` is specified, then update using the specified auto-analysis type.
        """
        return cls.__auto__(ea, type.get('type', idaapi.AU_NONE))

    @classmethod
    def unknown(cls, ea): return cls.auto(ea, type=idaapi.AU_UNK)
    @classmethod
    def code(cls, ea): return cls.auto(ea, type=idaapi.AU_CODE)
    @classmethod
    def weak(cls, ea): return cls.auto(ea, type=idaapi.AU_WEAK)
    @classmethod
    def procedure(cls, ea): return cls.auto(ea, type=idaapi.AU_PROC)
    @classmethod
    def tail(cls, ea): return cls.auto(ea, type=idaapi.AU_TAIL)
    @classmethod
    def stackpointer(cls, ea): return cls.auto(ea, type=idaapi.AU_TRSP)
    @classmethod
    def analyze(cls, ea): return cls.auto(ea, type=idaapi.AU_USED)
    @classmethod
    def type(cls, ea): return cls.auto(ea, type=idaapi.AU_TYPE)
    @classmethod
    def signature(cls, ea): return cls.auto(ea, type=idaapi.AU_LIBF)
    @classmethod
    def final(cls, ea): return cls.auto(ea, type=idaapi.AU_FINAL)

### interfacing with IDA's menu system
# FIXME: add some support for actually manipulating menus
class menu(object):
    """
    This namespace is for registering items in IDA's menu system.
    """
    state = {}
    @classmethod
    def add(cls, path, name, callable, hotkey='', flags=0, args=()):
        '''Register a `callable` as a menu item at the specified `path` with the provided `name`.'''

        # check to see if our menu item is in our cache and remove it if so
        if (path, name) in cls.state:
            cls.rm(path, name)

        # now we can add the menu item since everything is ok
        # XXX: I'm not sure if the path needs to be utf8 encoded or not
        res = internal.utils.string.to(name)
        ctx = idaapi.add_menu_item(path, res, hotkey, flags, callable, args)
        cls.state[path, name] = ctx
    @classmethod
    def rm(cls, path, name):
        '''Remove the menu item at the specified `path` with the provided `name`.'''
        res = cls.state[path, name]
        idaapi.del_menu_item(res)
        del cls.state[path, name]
    @classmethod
    def reset(cls):
        '''Remove all currently registered menu items.'''
        for path, name in cls.state.keys():
            cls.rm(path, name)
        return

### Qt wrappers and namespaces
class window(object):
    """
    This namespace is for selecting a specific or particular window.
    """
    @classmethod
    def viewer(cls):
        '''Return the current viewer.'''
        return idaapi.get_current_viewer()
    @classmethod
    def main(cls):
        '''Return the active main window.'''
        global application
        q = application()
        return q.activeWindow()

class windows(object):
    """
    Interact with any or all of the top-level windows for the application.
    """
    def __new__(cls):
        '''Return all of the top-level windows.'''
        global application
        q = application()
        return q.topLevelWindows()

class widget(object):
    """
    This namespace is for selecting a specific or particular widget.
    """
    def __new__(self, xy):
        '''Return the widget at the specified (`x`, `y`) coordinate within the `xy` tuple.'''
        res = x, y = xy
        return cls.at(res)
    @classmethod
    def at(cls, xy):
        '''Return the widget at the specified (`x`, `y`) coordinate within the `xy` tuple.'''
        res = x, y = xy
        global application
        q = application()
        return q.widgetAt(x, y)
    @classmethod
    def form(cls, twidget):
        '''Return an IDA plugin form as a UI widget.'''
        raise internal.exceptions.MissingMethodError

class clipboard(object):
    """
    This namespace is for interacting with the current clipboard state.
    """
    def __new__(cls):
        '''Return the current clipboard.'''
        global application
        clp = application()
        return clp.clipboard()

class mouse(object):
    """
    Base namespace for interacting with the mouse input.
    """
    @classmethod
    def buttons(cls):
        '''Return the current mouse buttons that are being clicked.'''
        global application
        q = application()
        return q.mouseButtons()

    @classmethod
    def position(cls):
        '''Return the current `(x, y)` position of the cursor.'''
        raise internal.exceptions.MissingMethodError

class keyboard(object):
    """
    Base namespace for interacting with the keyboard input.
    """
    @classmethod
    def modifiers(cls):
        '''Return the current keyboard modifiers that are being used.'''
        global application
        q = application()
        return q.keyboardModifiers()

    @classmethod
    def __of_key__(cls, key):
        '''Convert the normalized hotkey tuple in `key` into a format that IDA can comprehend.'''
        Separators = {'-', '+'}
        Modifiers = {'ctrl', 'shift', 'alt'}

        # Validate the type of our parameter
        if not isinstance(key, tuple):
            raise internal.exceptions.InvalidParameterError(u"{:s}.of_key({!r}) : A key combination of an invalid type was provided as a parameter.".format('.'.join([__name__, cls.__name__]), key))

        # Find a separator that we can use, and use it to join our tuple into a
        # string with each element capitalized. That way it looks good for the user.
        separator = next(item for item in Separators)
        modifiers, hotkey = key

        components = [item.capitalize() for item in modifiers] + [hotkey.capitalize()]
        return separator.join(components)

    @classmethod
    def __normalize_key__(cls, hotkey):
        '''Normalize the string `key` to a tuple that can be used to lookup keymappings.'''
        Separators = {'-', '+', '_'}
        Modifiers = {'ctrl', 'shift', 'alt'}

        # First check to see if we were given a tuple or list. If so, then we might
        # have been given a valid hotkey. However, we still need to validate this.
        # So, to do that we'll concatenate each component together back into a string
        # and then recurse so we can validate using the same logic.
        if isinstance(hotkey, (tuple, list, set)):
            try:
                # If we were mistakenly given a set, then we need to reformat it.
                if isinstance(hotkey, set):
                    raise ValueError

                modifiers, key = hotkey

                # If modifiers is not of the correct type, then still need to reformat.
                if not isinstance(modifiers, (tuple, list, set)):
                    raise ValueError

            # If the tuple we received was of an invalid format, then extract the
            # modifiers that we can from it, and try again.
            except ValueError:
                modifiers = tuple(item for item in hotkey if item.lower() in Modifiers)
                key = ''.join(item for item in hotkey if item.lower() not in Modifiers)

            # Grab a separator, and join all our components together with it.
            separator = next(item for item in Separators)
            components = [item for item in modifiers] + [key]
            return cls.__normalize_key__(separator.join(components))

        # Next we need to normalize the separator used throughout the string by
        # simply converting any characters we might consider a separator into
        # a null-byte so we can split on it.
        normalized = functools.reduce(lambda agg, item: agg.replace(item, '\0'), Separators, hotkey)

        # Now we can split the normalized string so we can convert it into a
        # set. We will then iterate through this set collecting all of our known
        # key modifiers. Anything left must be a single key, so we can then
        # validate the hotkey we were given.
        components = { item.lower() for item in normalized.split('\0') }

        modifiers = { item for item in components if item in Modifiers }
        key = components ^ modifiers

        # Now we need to verify that we were given just one key. If we were
        # given any more, then this isn't a valid hotkey combination and we need
        # to bitch about it.
        if len(key) != 1:
            raise internal.exceptions.InvalidParameterError(u"{:s}.normalize_key({!s}) : An invalid hotkey combination ({!s}) was provided as a parameter.".format('.'.join([__name__, cls.__name__]), internal.utils.string.repr(hotkey), internal.utils.string.repr(hotkey)))

        res = next(item for item in key)
        if len(res) != 1:
            raise internal.exceptions.InvalidParameterError(u"{:s}.normalize_key({!s}) : The hotkey combination {!s} contains the wrong number of keys ({:d}).".format('.'.join([__name__, cls.__name__]), internal.utils.string.repr(hotkey), internal.utils.string.repr(res), len(res)))

        # That was it. Now to do the actual normalization, we need to sort our
        # modifiers into a tuple, and return the single hotkey that we extracted.
        res, = key
        return tuple(sorted(modifiers)), res

    # Create a cache to store the hotkey context, and the callable that was mapped to it
    __cache__ = {}

    @classmethod
    def list(cls):
        '''Display the current list of keyboard combinations that are mapped along with the callable each one is attached to.'''
        maxkey, maxtype, maxinfo = 0, 0, 0

        results = []
        for mapping, (capsule, closure) in cls.__cache__.items():
            key = cls.__of_key__(mapping)

            # Check if we were passed a class so we can figure out how to
            # extract the signature.
            cons = ['__init__', '__new__']
            if inspect.isclass(closure):
                available = (item for item in cons if hasattr(closure, item))
                attribute = next((item for item in available if inspect.ismethod(getattr(closure, item))), None)
                callable = getattr(closure, attribute) if attribute else None
                information = '.'.join([closure.__name__, internal.utils.multicase.prototype(callable)]) if attribute else "{:s}(...)".format(closure.__name__)
            else:
                information = internal.utils.multicase.prototype(closure)

            # Figure out the type of the callable that is mapped.
            if inspect.isclass(closure):
                ftype = 'class'
            elif inspect.ismethod(closure):
                ftype = 'method'
            elif inspect.isbuiltin(closure):
                ftype = 'builtin'
            elif inspect.isfunction(closure):
                ftype = 'anonymous' if closure.__name__ in {'<lambda>'} else 'function'
            else:
                ftype = 'callable'

            # Figure out if there's any class-information associated with the closure
            if inspect.ismethod(closure):
                klass = closure.im_self.__class__ if closure.im_self else closure.im_class
                clsinfo = klass.__name__ if getattr(klass, '__module__', '__main__') in {'__main__'} else '.'.join([klass.__module__, klass.__name__])
            elif inspect.isclass(closure) or isinstance(closure, object):
                clsinfo = '' if getattr(closure, '__module__', '__main__') in {'__main__'} else closure.__module__
            else:
                clsinfo = None if getattr(closure, '__module__', '__main__') in {'__main__'} else closure.__module__

            # Now we can figure out the documentation for the closure that was stored.
            documentation = closure.__doc__ or ''
            if documentation:
                filtered = [item.strip() for item in documentation.split('\n') if item.strip()]
                header = next((item for item in filtered), '')
                comment = "{:s}...".format(header) if header and len(filtered) > 1 else header
            else:
                comment = ''

            # Calculate our maximum column widths inline
            maxkey = max(maxkey, len(key))
            maxinfo = max(maxinfo, len('.'.join([clsinfo, information]) if clsinfo else information))
            maxtype = max(maxtype, len(ftype))

            # Append each column to our results
            results.append((key, ftype, clsinfo, information, comment))

        # If we didn't aggregate any results, then raise an exception as there's nothing to do.
        if not results:
            raise internal.exceptions.SearchResultsError(u"{:s}.list() : Found 0 key combinations mapped.".format('.'.join([__name__, cls.__name__])))

        # Now we can output what was mapped to the user.
        six.print_(u"Found the following{:s} key combination{:s}:".format(" {:d}".format(len(results)) if len(results) > 1 else '', '' if len(results) == 1 else 's'))
        for key, ftype, clsinfo, info, comment in results:
            six.print_(u"Key: {:>{:d}s} -> {:<{:d}s}{:s}".format(key, maxkey, "{:s}:{:s}".format(ftype, '.'.join([clsinfo, info]) if clsinfo else info), maxtype + 1 + maxinfo, " // {:s}".format(comment) if comment else ''))
        return

    @classmethod
    def map(cls, key, callable):
        """Map the specified `key` combination to a python `callable` in IDA.

        If the provided `key` is being re-mapped due to the mapping already existing, then return the previous callable that it was assigned to.
        """

        # First we'll normalize the hotkey that we were given, and convert it
        # back into a format that IDA can understand. This way we can prevent
        # users from giving us a sloppy hotkey combination that we won't be
        # able to search for in our cache.
        hotkey = cls.__normalize_key__(key)
        keystring = cls.__of_key__(hotkey)

        # The hotkey we normalized is now a tuple, so check to see if it's
        # already within our cache. If it is, then we need to unmap it prior to
        # re-creating the mapping.
        if hotkey in cls.__cache__:
            logging.warning(u"{:s}.map({!s}, {!r}) : Remapping the hotkey combination {!s} with the callable {!r}.".format('.'.join([__name__, cls.__name__]), internal.utils.string.repr(key), callable, internal.utils.string.repr(keystring), callable))
            ctx, _ = cls.__cache__[hotkey]

            ok = idaapi.del_hotkey(ctx)
            if not ok:
                raise internal.exceptions.DisassemblerError(u"{:s}.map({!s}, {!r}) : Unable to remove the hotkey combination {!s} from the list of current keyboard mappings.".format('.'.join([__name__, cls.__name__]), internal.utils.string.repr(key), callable, internal.utils.string.repr(keystring)))

            # Pop the callable that was mapped out of the cache so that we can
            # return it to the user.
            _, res = cls.__cache__.pop(hotkey)

        # If the user is mapping a new key, then there's no callable to return.
        else:
            res = None

        # Verify that the user gave us a callable to use to avoid mapping a
        # useless type to the specified keyboard combination.
        if not builtins.callable(callable):
            raise internal.exceptions.InvalidTypeOrValueError(u"{:s}.map({!s}, {!r}) : Unable to map the non-callable value {!r} to the hotkey combination {!s}.".format('.'.join([__name__, cls.__name__]), internal.utils.string.repr(key), callable, callable, internal.utils.string.repr(keystring)))

        # Define a closure that calls the user's callable as it seems that IDA's
        # hotkey functionality doesn't deal too well when the same callable is
        # mapped to different hotkeys.
        def closure(*args, **kwargs):
            return callable(*args, **kwargs)

        # Now we can add the hotkey to IDA using the closure that we generated.
        # XXX: I'm not sure if the key needs to be utf8 encoded or not
        ctx = idaapi.add_hotkey(keystring, closure)
        if not ctx:
            raise internal.exceptions.DisassemblerError(u"{:s}.map({!s}, {!r}) : Unable to map the callable {!r} to the hotkey combination {!s}.".format('.'.join([__name__, cls.__name__]), internal.utils.string.repr(key), callable, callable, internal.utils.string.repr(keystring)))

        # Last thing to do is to stash it in our cache with the user's callable
        # in order to keep track of it for removal.
        cls.__cache__[hotkey] = ctx, callable
        return res

    @classmethod
    def unmap(cls, key):
        '''Unmap the specified `key` from IDA and return the callable that it was assigned to.'''
        frepr = lambda hotkey: internal.utils.string.repr(cls.__of_key__(hotkey))

        # First check to see whether we were given a callable or a hotkey. If
        # we were given a callable, then we need to look through our cache for
        # the actual key that it was. Once found, then we normalize it like usual.
        if callable(key):
            try:
                hotkey = cls.__normalize_key__(next(item for item, (_, fcallback) in cls.__cache__.items() if fcallback == key))

            except StopIteration:
                raise internal.exceptions.InvalidParameterError(u"{:s}.unmap({:s}) : Unable to locate the callable {!r} in the current list of keyboard mappings.".format('.'.join([__name__, cls.__name__]), "{!r}".format(key) if callable(key) else "{!s}".format(internal.utils.string.repr(key)), key))

            else:
                logging.warning(u"{:s}.unmap({:s}) : Discovered the hotkey {!s} being currently mapped to the callable {!r}.".format('.'.join([__name__, cls.__name__]), "{!r}".format(key) if callable(key) else "{!s}".format(internal.utils.string.repr(key)), frepr(hotkey), key))

        # We need to normalize the hotkey we were given, and convert it back
        # into IDA's format. This way we can locate it in our cache, and prevent
        # sloppy user input from interfering.
        else:
            hotkey = cls.__normalize_key__(key)

        # Check to see if the hotkey is cached and warn the user if it isn't.
        if hotkey not in cls.__cache__:
            logging.warning(u"{:s}.unmap({:s}) : Refusing to unmap the hotkey {!s} as it is not currently mapped to anything.".format('.'.join([__name__, cls.__name__]), "{!r}".format(key) if callable(key) else "{!s}".format(internal.utils.string.repr(key)), frepr(hotkey)))
            return

        # Grab the keymapping context from our cache, and then ask IDA to remove
        # it for us. If we weren't successful, then raise an exception so the
        # user knows what's up.
        ctx, _ = cls.__cache__[hotkey]
        ok = idaapi.del_hotkey(ctx)
        if not ok:
            raise internal.exceptions.DisassemblerError(u"{:s}.unmap({:s}) : Unable to unmap the specified hotkey ({!s}) from the current list of keyboard mappings.".format('.'.join([__name__, cls.__name__]), "{!r}".format(key) if callable(key) else "{!s}".format(internal.utils.string.repr(key)), frepr(hotkey)))

        # Now we can pop off the callable that was mapped to the hotkey context
        # in order to return it, and remove the hotkey from our cache.
        _, res = cls.__cache__.pop(hotkey)
        return res

    add, rm = internal.utils.alias(map, 'keyboard'), internal.utils.alias(unmap, 'keyboard')

    @classmethod
    def input(cls):
        '''Return the current keyboard input context.'''
        raise internal.exceptions.MissingMethodError

### PyQt5-specific functions and namespaces
## these can overwrite any of the classes defined above
try:
    import PyQt5.Qt
    from PyQt5.Qt import QObject

    def application():
        '''Return the current instance of the IDA Application.'''
        q = PyQt5.Qt.qApp
        return q.instance()

    class mouse(mouse):
        """
        This namespace is for interacting with the mouse input.
        """
        @classmethod
        def position(cls):
            '''Return the current `(x, y)` position of the cursor.'''
            qt = PyQt5.QtGui.QCursor
            res = qt.pos()
            return res.x(), res.y()

    class keyboard(keyboard):
        """
        This namespace is for interacting with the keyboard input.
        """
        @classmethod
        def input(cls):
            '''Return the current keyboard input context.'''
            raise internal.exceptions.MissingMethodError

    class UIProgress(object):
        """
        Helper class used to simplify the showing of a progress bar in IDA's UI.
        """
        timeout = 5.0

        def __init__(self, blocking=True):
            self.object = res = PyQt5.Qt.QProgressDialog()
            res.setVisible(False)
            res.setWindowModality(blocking)
            res.setAutoClose(True)
            path = os.path.join(_database.config.path(), _database.config.filename())
            self.update(current=0, min=0, max=0, text=u'Processing...', tooltip=u'...', title=path)

        # properties
        canceled = property(fget=lambda self: self.object.wasCanceled(), fset=lambda self, value: self.object.canceled.connect(value))
        maximum = property(fget=lambda self: self.object.maximum())
        minimum = property(fget=lambda self: self.object.minimum())
        current = property(fget=lambda self: self.object.value())

        # methods
        def open(self, width=0.8, height=0.1):
            '''Open a progress bar with the specified `width` and `height` relative to the dimensions of IDA's window.'''
            global window
            cls = self.__class__

            # XXX: spin for a second until main is defined because IDA seems to be racy with this api
            ts, main = time.time(), getattr(self, '__appwindow__', None)
            while time.time() - ts < self.timeout and main is None:
                main = window.main()

            if main is None:
                logging.warning(u"{:s}.open({!s}, {!s}) : Unable to find main application window. Falling back to default screen dimensions to calculate size.".format('.'.join([__name__, cls.__name__]), width, height))

            # figure out the dimensions of the window
            if main is None:
                # if there's no window, then assume some screen dimensions
                w, h = 1024, 768
            else:
                w, h = main.width(), main.height()

            # now we can calculate the dimensions of the progress bar
            logging.info(u"{:s}.open({!s}, {!s}) : Using dimensions ({:d}, {:d}) for progress bar.".format('.'.join([__name__, cls.__name__]), width, height, int(w*width), int(h*height)))
            self.object.setFixedWidth(w * width), self.object.setFixedHeight(h * height)

            # calculate the center
            if main is None:
                # no window, so use the center of the screen
                cx, cy = w * 0.5, h * 0.5
            else:
                center = main.geometry().center()
                cx, cy = center.x(), center.y()

            # ...and center it.
            x, y = cx - (w * width * 0.5), cy - (h * height * 1.0)
            logging.info(u"{:s}.open({!s}, {!s}) : Centering progress bar at ({:d}, {:d}).".format('.'.join([__name__, cls.__name__]), width, height, int(x), int(y)))
            self.object.move(x, y)

            # now everything should look good.
            self.object.show()

        def close(self):
            '''Close the current progress bar.'''
            self.object.close()

        def update(self, **options):
            '''Update the current state of the progress bar.'''
            minimum, maximum = options.get('min', None), options.get('max', None)
            text, title, tooltip = (options.get(item, None) for item in ['text', 'title', 'tooltip'])

            if minimum is not None:
                self.object.setMinimum(minimum)
            if maximum is not None:
                self.object.setMaximum(maximum)
            if title is not None:
                self.object.setWindowTitle(internal.utils.string.to(title))
            if tooltip is not None:
                self.object.setToolTip(internal.utils.string.to(tooltip))
            if text is not None:
                self.object.setLabelText(internal.utils.string.to(text))

            res = self.object.value()
            if 'current' in options:
                self.object.setValue(options['current'])
            elif 'value' in options:
                self.object.setValue(options['value'])
            return res

    class widget(widget):
        """
        This namespace is for selecting a specific or particular widget.
        """
        @classmethod
        def form(cls, twidget):
            '''Return an IDA plugin form as a UI widget.'''
            ns = idaapi.PluginForm
            return ns.FormToPyQtWidget(twidget)

except ImportError:
    logging.info(u"{:s}:Unable to locate `PyQt5.Qt` module.".format(__name__))

### PySide-specific functions and namespaces
try:
    import PySide
    import PySide.QtCore, PySide.QtGui

    def application():
        '''Return the current instance of the IDA Application.'''
        res = PySide.QtCore.QCoreApplication
        return res.instance()

    class mouse(mouse):
        """
        This namespace is for interacting with the mouse input.
        """
        @classmethod
        def position(cls):
            '''Return the current `(x, y)` position of the cursor.'''
            qt = PySide.QtGui.QCursor
            res = qt.pos()
            return res.x(), res.y()

    class keyboard(keyboard):
        """
        PySide keyboard interface.
        """
        @classmethod
        def input(cls):
            '''Return the current keyboard input context.'''
            return q.inputContext()

    class widget(widget):
        """
        This namespace is for selecting a specific or particular widget.
        """
        @classmethod
        def form(cls, twidget):
            '''Return an IDA plugin form as a UI widget.'''
            ns = idaapi.PluginForm
            return ns.FormToPySideWidget(twidget)

except ImportError:
    logging.info(u"{:s}:Unable to locate `PySide` module.".format(__name__))

### wrapper that uses a priorityhook around IDA's hooking capabilities.
class hook(object):
    """
    This namespace exposes the ability to hook different parts of IDA.

    There are 3 different components in IDA that can be hooked. These
    are available as ``hook.idp``, ``hook.idb``, and ``hook.ui``.

    Please refer to the documentation for ``idaapi.IDP_Hooks``,
    ``idaapi.IDB_Hooks``, and ``idaapi.UI_Hooks`` for identifying what
    is available.
    """
    @classmethod
    def __start_ida__(cls):
        api = [
            ('idp', idaapi.IDP_Hooks),
            ('idb', idaapi.IDB_Hooks),
            ('ui', idaapi.UI_Hooks),
        ]

        # Create an alias so we save typing 19 chars..
        priorityhook = internal.interface.priorityhook
        for attr, hookcls in api:

            # Attach a priority hooking queue to an instance of IDA's hooks
            instance = priorityhook(hookcls)

            # Explicitly assign the priority instance into our object
            if not hasattr(cls, attr):
                setattr(cls, attr, instance)

            # Now we can enable all the hooks so the user can use them
            instance.hook()
        return

    @classmethod
    def __stop_ida__(cls):
        for api in ['idp', 'idb', 'ui']:

            # grab the invidual class that was used to hook things
            hooker = getattr(cls, api)

            # and then unhook it completely, because IDA on linux
            # seems to still dispatch to those hooks...even when
            # the language extension is unloaded.
            hooker.unhook()
        return

### Helper classes to use or inherit from
# XXX: why was this base class implemented again??
class InputBox(idaapi.PluginForm):
    """
    A class designed to be inherited from that can be used
    to interact with the user.
    """
    def OnCreate(self, form):
        '''A method to overload to be notified when the plugin form is created.'''
        self.parent = self.FormToPyQtWidget(form)

    def OnClose(self, form):
        '''A method to overload to be notified when the plugin form is destroyed.'''
        pass

    def Show(self, caption, options=0):
        '''Show the form with the specified `caption` and `options`.'''
        res = internal.utils.string.to(caption)
        return super(InputBox, self).Show(res, options)

### Console-only progress bar
class ConsoleProgress(object):
    """
    Helper class used to simplify the showing of a progress bar in IDA's console.
    """
    def __init__(self, blocking=True):
        self.__path__ = os.path.join(_database.config.path(), _database.config.filename())
        self.__value__ = 0
        self.__min__, self.__max__ = 0, 0
        return

    canceled = property(fget=lambda self: False, fset=lambda self, value: None)
    maximum = property(fget=lambda self: self.__max__)
    minimum = property(fget=lambda self: self.__min__)
    current = property(fget=lambda self: self.__value__)

    def open(self, width=0.8, height=0.1):
        '''Open a progress bar with the specified `width` and `height` relative to the dimensions of IDA's window.'''
        return

    def close(self):
        '''Close the current progress bar.'''
        return

    def update(self, **options):
        '''Update the current state of the progress bar.'''
        minimum, maximum = options.get('min', None), options.get('max', None)
        text, title, tooltip = (options.get(item, None) for item in ['text', 'title', 'tooltip'])

        if minimum is not None:
            self.__min__ = minimum
        if maximum is not None:
            self.__max__ = maximum

        res = self.__value__
        if 'current' in options:
            self.__value__ = options['current']
        if 'value' in options:
            self.__value__ = options['value']

        if text is not None:
            six.print_(internal.utils.string.of(text))

        return res

### Fake progress bar class that instantiates whichever one is available
class Progress(object):
    """
    The default progress bar in with which to show progress. This class will
    automatically determine which progress bar (Console or UI) to instantiate
    based on what is presently available.
    """

    timeout = 5.0

    def __new__(cls, *args, **kwargs):
        '''Figure out which progress bar to use and instantiate it with the provided parameters `args` and `kwargs`.'''
        if 'UIProgress' not in globals():
            logging.warning(u"{:s}(...) : Using console-only implementation of the `ui.Progress` class.".format('.'.join([__name__, cls.__name__])))
            return ConsoleProgress(*args, **kwargs)

        # XXX: spin for a bit looking for the application window as IDA seems to be racy with this for some reason
        ts, main = time.time(), getattr(cls, '__appwindow__', None)
        while time.time() - ts < cls.timeout and main is None:
            main = window.main()

        # If no main window was found, then fall back to the console-only progress bar
        if main is None:
            logging.warning(u"{:s}(...) : Unable to find main application window. Falling back to console-only implementation of the `ui.Progress` class.".format('.'.join([__name__, cls.__name__])))
            return ConsoleProgress(*args, **kwargs)

        cls.__appwindow__ = main
        return UIProgress(*args, **kwargs)

### Re-implementation of IDAPython's displayhook that doesn't tamper with classes that inherit from base classes
class DisplayHook(object):
    def __init__(self, displayhook=None):
        if displayhook:
            self.orig_displayhook = displayhook

        elif 'ida_idaapi' in sys.modules and '_IDAPython_displayhook' in sys.modules['ida_idaapi'].__dict__:
            self.orig_displayhook = __import__('ida_idaapi')._IDAPython_displayhook.orig_displayhook

        else:
            self.orig_displayhook = sys.displayhook

    def format_seq(self, num_printer, storage, item, opn, cls):
        storage.append(opn)
        for idx, el in enumerate(item):
            if idx > 0:
                storage.append(', ')
            self.format_item(num_printer, storage, el)
        storage.append(cls)

    def format_basestring(self, string):
        # FIXME: rather than automatically evaluating the string as we're
        #        currently doing, it'd be much cleaner if we just format the
        #        result from a function with some sort of wrapper object. This
        #        way we can check its type, and then choose whether to unwrap it
        #        or not. This can be done with a decorator of some sort that
        #        communicates to this implementation that it will need to
        #        distinguish between printable strings that we can output and
        #        strings that should be processed by the user.
        # XXX: maybe we can even use this wrapper object to allow this class to
        #      handle aligning columns in a table automatically such as when
        #      more than one element in a row is being returned.
        try:
            result = u"{!r}".format(string)
        except UnicodeDecodeError:
            import codecs
            encoded, _ = codecs.escape_encode(string)
            result = u"'{!s}'".format(encoded)
        return result

    def format_item(self, num_printer, storage, item):
        if item is None or isinstance(item, bool):
            storage.append("{!s}".format(item))
        elif isinstance(item, six.string_types):
            storage.append(self.format_basestring(item))
        elif isinstance(item, six.integer_types):
            storage.append(num_printer(item))
        elif isinstance(item, idaapi.tinfo_t):
            storage.append("{!s}".format(item.dstr()))
        elif item.__class__ is list:
            self.format_seq(num_printer, storage, item, '[', ']')
        elif item.__class__ is tuple:
            self.format_seq(num_printer, storage, item, '(', ')')
        elif item.__class__ is set:
            self.format_seq(num_printer, storage, item, 'set([', '])')
        elif item.__class__ is dict:
            storage.append('{')
            for idx, pair in enumerate(item.items()):
                if idx > 0:
                    storage.append(', ')
                self.format_item(num_printer, storage, pair[0])
                storage.append(": ")
                self.format_item(num_printer, storage, pair[1])
            storage.append('}')
        else:
            storage.append("{!r}".format(item))

    def _print_hex(self, x):
        return "{:#x}".format(x)

    def displayhook(self, item):
        if item is None or not hasattr(item, '__class__') or item.__class__ is bool:
            self.orig_displayhook(item)
            return
        try:
            storage = []
            if idaapi.__version__ < 7.0:
                import idaapi as ida_idp
            else:
                import ida_idp
            num_printer = self._print_hex
            dn = ida_idp.ph_get_flag() & ida_idp.PR_DEFNUM
            if dn == ida_idp.PRN_OCT:
                num_printer = oct
            elif dn == ida_idp.PRN_DEC:
                num_printer = str
            elif dn == ida_idp.PRN_BIN:
                num_printer = bin
            self.format_item(num_printer, storage, item)
            sys.stdout.write("%s\n" % "".join(storage))
        except Exception:
            import traceback
            traceback.print_exc()
            self.orig_displayhook(item)

