"""
Internal initialization script

This is an internal script that is executed when IDA starts. Things
such as meta_path hooks, replacing the namespace with the contents
of the __root__ module, and implementing a work-around for the hack
that IDAPython does with saving the contents of sys.modules. After
initializing everything, this script will then hand off execution
to the user's idapythonrc.py in their home directory.
"""

# output the IDAPython banner when IDA starts
print_banner()

# some general python modules that we use for meta_path
import sys, os
import imp, fnmatch, ctypes, types
import idaapi

library = ctypes.WinDLL if os.name == 'nt' else ctypes.CDLL

# grab ida's user directory and remove from path since we use meta_path to locate api modules
root = idaapi.get_user_idadir()
sys.path.remove(root)

class internal_api(object):
    """
    Loader base-class for any api that's based on files contained within a directory.
    """
    os, imp, fnmatch = os, imp, fnmatch
    def __init__(self, directory, **attributes):
        '''Initialize the api using the contents within the specified `directory`.'''
        self.path = self.os.path.realpath(directory)
        [ setattr(self, name, attribute) for name, attribute in attributes.items() ]

    ### Api operations
    def load_api(self, path):
        '''Load the specified `path` into a module that can be used.'''
        path, filename = self.os.path.split(path)
        name, _ = self.os.path.splitext(filename)
        return self.imp.find_module(name, [path])

    def iterate_api(self, include='*.py', exclude=None):
        """Iterate through all of the files in the directory specified when initializing the loader.

        The `include` string is a glob that specifies which files are part of the loader's api.
        If the `exclude` glob is specified, then exclude files that match it from the loader api.
        """
        result = []
        for filename in self.fnmatch.filter(self.os.listdir(self.path), include):
            if exclude and self.fnmatch.fnmatch(filename, exclude):
                continue

            path = self.os.path.join(self.path, filename)
            _, ext = self.os.path.splitext(filename)

            left, right = (None, None) if include == '*' else (include.index('*'), len(include) - include.rindex('*'))
            modulename = filename[left : -right + 1]
            yield modulename, path
        return

    def new_api(self, modulename, path):
        '''Load the file found at `path` into the specified `modulename`.'''
        file, path, description = self.load_api(path)
        try:
            return self.imp.load_module(modulename, file, path, description)
        finally: file.close()

    ### Module operations
    def new_module(self, fullname, documentation=None):
        '''Create a new module (empty) with the specified `fullname` and the provided `documentation`.'''
        res = self.imp.new_module(fullname)
        res.__package__ = fullname
        res.__doc__ = documentation or ''
        return res

    def find_module(self, fullname, path=None):
        raise NotImplementedError

    def load_module(self, fullname):
        raise NotImplementedError

class internal_path(internal_api):
    """
    Loader class which provides all api composed of all of the files within a directory
    as modules that can always be imported from anywhere.
    """
    def __init__(self, path, **attrs):
        '''Initialize the loader using the files from the directory specified by `path`.'''
        super(internal_path, self).__init__(path)
        attrs.setdefault('include', '*.py')
        self.attrs, self.cache = attrs, { name : path for name, path in self.iterate_api(**attrs) }

    def find_module(self, fullname, path=None):
        '''If the module with the name `fullname` matches one of the files handled by our api, then act as their loader.'''
        return self if path is None and fullname in self.cache else None

    def load_module(self, fullname):
        '''Iterate through all of the modules that we can handle, and then load it if we've been asked.'''
        self.cache = { name : path for name, path in self.iterate_api(**self.attrs) }
        if fullname not in self.cache:
            raise ImportError("path-loader ({:s}) was not able to find a module named `{:s}`".format(self.path, fullname))
        return self.new_api(fullname, self.cache[fullname])

class internal_submodule(internal_api):
    """
    Loader class which provides an api composed of all of the files within a
    directory, and binds them to a module which is used to access them.
    """
    sys = sys
    def __init__(self, __name__, path, **attrs):
        '''Initialize the loader using `__name__` as the name of the submodule using the files underneath the directory `path`.'''
        super(internal_submodule, self).__init__(path)
        attrs.setdefault('include', '*.py')
        self.__name__, self.attrs = __name__, attrs

    def find_module(self, fullname, path=None):
        '''If the module with the name `fullname` matches our submodule name, then act as its loader.'''
        return self if path is None and fullname == self.__name__ else None

    def new_api(self, modulename, path):
        '''Load the file found at the specified `path` as a submodule with the specified `modulename`.'''
        cls, fullname = self.__class__, '.'.join([self.__name__, modulename])
        res = super(cls, self).new_api(fullname, path)
        res.__package__ = self.__name__
        return res

    def load_module(self, fullname):
        '''Iterate through all of the modules that we can handle, load the submodule with them, and return it.'''
        module = self.sys.modules[fullname] = self.new_module(fullname)
        # FIXME: make module a lazy-loaded object for fetching module-code on-demand

        # Build a temporary cache for the module names and paths to load the api,
        # and use them to build their documentation.
        cache = { name : path for name, path in self.iterate_api(**self.attrs) }
        module.__doc__ = '\n'.join("{:s} -- {:s}".format(name, path) for name, path in sorted(cache.items()))

        # Load each submodule that composes the api, and attach it to the returned submodule.
        stack, count, result = [item for item in cache.items()], len(cache), {}
        while stack and count > 0:
            name, path = stack.pop(0)

            # Take the submodule name we popped off of the cache, and try and load it.
            # If we were able to load it successfully, then we just need to attach the
            # loaded code as a submodule of the object we're going to return.
            try:
                res = self.new_api(name, path)
                modulename = '.'.join([res.__package__, name])

            # If an exception was raised, then remember it so that we can let the user
            # know after we've completely loaded the module.
            except Exception as E:
                __import__('logging').info("{:s} : Error trying to import module `{:s}` from {!s}. Queuing it until later.".format(self.__name__, name, path), exc_info=True)

                # If we caught an exception while trying to import the module, then stash
                # our exception info state into a dictionary and decrease a counter. This
                # is strictly to deal with module recursion issues in Python3.
                result[name], count = sys.exc_info(), count - 1
                stack.append((name, path))

            # Add the submodule that we loaded into the module that we're going to return.
            else:
                setattr(module, name, res)
            continue

        # If we weren't able to load one of the submodules that should've been in our cache,
        # then go through all of our backtraces and log the exception that was raised.
        if stack:
            import logging, traceback
            for name, path in stack:
                logging.fatal("{:s} : Error trying to import module `{:s}` from {!s}.".format(self.__name__, name, path), exc_info=result[name])
            return module

        # If we caught an exception despite our stack being empty, then this is because of a
        # recursion issue. In case someone wants to track these situations down, we go through
        # our caught exceptions and create some logging events with the backtrace. These errors
        # are non-fatal because importing another sub-module helped resolve it.
        for name, exc_info in result.items():
            __import__('logging').info("{!s} : Encountered a non-fatal exception while trying to import recursive module `{:s}` from {!s}".format(self.__name__, name, cache[name]), exc_info=result[name])

        # Return the module that we just created.
        return module

class internal_object(object):
    """
    Loader class which will simply expose an object instance as the module.
    """
    sys = sys
    def __init__(self, __name__, object):
        '''Initialize the loader with the specified `__name__` and returning the provided `object` as its module.'''
        self.__name__, self.object = __name__, object

    def find_module(self, fullname, path=None):
        '''If the module being searched for matches our `fullname`, then act as its loader.'''
        return self if path is None and fullname == self.__name__ else None

    def load_module(self, fullname):
        '''Return the specific object for the module specified by `fullname`.'''
        if fullname != self.__name__:
            raise ImportError("object-loader ({:s}) was not able to find a module named `{:s}`".format(self.__name__, fullname))
        module = self.sys.modules[fullname] = self.object
        return module

class plugin_module(object):
    """
    Loader class which iterates through all of the files in a directory, and
    manually initializes each plugin similar to the way `idaapi.plugin_t` is
    supposed to be initialized.
    """
    def __init__(self, path, **attrs):
        # FIXME: go through all files in plugin/ and call PLUGIN_ENTRY() on each module
        #        this should return an idaapi.plugin_t.

        # idaapi.plugin_t will contain an init, run, and term method.
        # also, are some attributes to process:
        # 'wanted_name' which is for idc.
        # 'wanted_hotkey', which should be mapped to a keypress.
        # 'comment' self-explanatory
        # 'help' self-explanatory

        # hotkey can be done by:
        # idaapi.CompileLine('static myname() { RunPythonStateMent("CallSomePython()") }')
        # idc.AddHotKey(module.wanted_hotkey, "myname")

        # idaapi.require
        pass

## IDA's native lower-level api
if sys.platform in {'darwin'}:
    sys.meta_path.append( internal_object('ida', library(idaapi.idadir('libida.dylib'))) )

elif sys.platform in {'linux', 'linux2'}:
    sys.meta_path.append( internal_object('ida', library("libida{:s}.so".format('' if idaapi.BADADDR < 0x100000000 else '64'))) )

elif sys.platform in {'win32'}:
    if __import__('os').path.exists(idaapi.idadir('ida.wll')):
        sys.meta_path.append( internal_object('ida', library(idaapi.idadir('ida.wll'))) )
    else:
        sys.meta_path.append( internal_object('ida', library(idaapi.idadir("ida{:s}.dll".format('' if idaapi.BADADDR < 0x100000000 else '64')))) )

else:
    __import__('logging').warning("{:s} : Unable to successfully load IDA's native api with ctypes.".format(__name__))

## private (internal) api
sys.meta_path.append( internal_submodule('internal', os.path.join(root, 'base'), include='_*.py') )

## public api
sys.meta_path.append( internal_path(os.path.join(root, 'base'), exclude='_*.py') )
sys.meta_path.append( internal_path(os.path.join(root, 'misc')) )

# user and application api's
for subdir in ('custom', 'app'):
    sys.meta_path.append( internal_submodule(subdir, os.path.join(root, subdir)) )
del(subdir)

# temporarily load the root namespace
__root__ = imp.load_source('__root__', os.path.join(root, '__root__.py'))

# empty out IDAPython's namespace so that we can replace it
map(globals().pop, {symbol for symbol in globals().copy() if not symbol.startswith('__')})

# re-populate with a default namespace and remove our variable that contained it
globals().update({symbol : value for symbol, value in __root__.__dict__.items() if not symbol.startswith('__')})
del(__root__)

# try and execute our user's idapythonrc.py
try:
    import os
    path, filename = None, '.idapythonrc.py'

    try:
        # execute user's .pythonrc and .idapythonrc in one go
        if os.path.expanduser("~"):
            path = os.path.expanduser("~")
            exec(open(os.path.join(path, filename)).read())

    except ImportError:
        # otherwise try to figure it out without tainting the namespace
        if __import__('os').getenv('HOME', default=None) is not None:
            path = os.getenv('HOME')
            exec(open(os.path.join(path, filename)).read())
        elif __import__('os').getenv('USERPROFILE', default=None) is not None:
            path = os.getenv('USERPROFILE')
            exec(open(os.path.join(path, filename)).read())
        else:
            raise OSError("unable to determine the user's home directory.")
        pass

except IOError:
    __import__('logging').warning("No {:s} file found in the user's home directory ({!s}).".format(filename, path))

except Exception:
    __import__('logging').warning("Unexpected exception raised while trying to execute `{!s}`.".format(os.path.join(path or '~', filename)), exc_info=True)

finally:
    del(filename)
    del(path)
    del(os)

## stupid fucking idapython hax
# prevent idapython from trying to write its banner to the message window since we called it up above.
print_banner = lambda: None

# find the frame that fucks with our sys.modules, and save it for later
frame = __import__('sys')._getframe()
while frame.f_code.co_name != 'IDAPython_ExecScript':
    frame = frame.f_back

# inject our current sys.modules state into IDAPython_ExecScript's state if it's the broken version
if 'basemodules' in frame.f_locals:
    frame.f_locals['basemodules'].update(__import__('sys').modules)
del(frame)
