
"""
Python dot expression completion using Pymacs.

This almost certainly needs work, but if you add

    (require 'pycomplete)

to your .xemacs/init.el file (untried w/ GNU Emacs so far) and have Pymacs
installed, when you hit M-TAB it will try to complete the dot expression
before point.  For example, given this import at the top of the file:

    import time

typing "time.cl" then hitting M-TAB should complete "time.clock".

This is unlikely to be done the way Emacs completion ought to be done, but
it's a start.  Perhaps someone with more Emacs mojo can take this stuff and
do it right.

See pycomplete.el for the Emacs Lisp side of things.
"""

# Author:     Skip Montanaro
# Maintainer: skip@pobox.com
# Created:    Oct 2004
# Keywords:   python pymacs emacs

# This software is provided as-is, without express or implied warranty.
# Permission to use, copy, modify, distribute or sell this software, without
# fee, for any purpose and by any individual or organization, is hereby
# granted, provided that the above copyright notice and this paragraph
# appear in all copies.

# Along with pycomplete.el this file allows programmers to complete Python
# symbols within the current buffer.
# import pdb
# pdb.set_trace()

import sys
import os.path

try:
    x = set
except NameError:
    from sets import Set as set
else:
    del x

def get_all_completions(s, imports=None):
    """Return contextual completion of s (string of >= zero chars).

    If given, imports is a list of import statements to be executed first.
    """
    locald = {}
    if imports is not None:
        for stmt in imports:
            try:
                exec stmt in globals(), locald
            except TypeError:
                raise TypeError, "invalid type: %s" % stmt

    dots = s.split(".")
    if not s or len(dots) == 1:
        keys = set()
        keys.update(locald.keys())
        keys.update(globals().keys())
        import __builtin__
        keys.update(dir(__builtin__))
        keys = list(keys)
        keys.sort()
        if s:
            return [k for k in keys if k.startswith(s)]
        else:
            return keys

    sym = None
    for i in range(1, len(dots)):
        s = ".".join(dots[:i])
        try:
            sym = eval(s, globals(), locald)
        except NameError:
            try:
                sym = __import__(s, globals(), locald, [])
            except ImportError:
                return []
    if sym is not None:
        s = dots[-1]
        return [k for k in dir(sym) if k.startswith(s)]

def pycomplete(s, imports=None):
    completions = get_all_completions(s, imports)
    if len(completions) == 0:
        return None
    else:
        dots = s.split(".")
        prefix = os.path.commonprefix([k for k in completions])
        if len(completions)==1 or len(prefix)>len(dots[-1]):
            return [prefix[len(dots[-1]):]]
        
        return completions

        # return os.path.commonprefix([k[len(dots[-1]):] for k in completions])

if __name__ == "__main__":
    print "<empty> ->", pycomplete("")
    print "sys.get ->", pycomplete("sys.get")
    print "sy ->", pycomplete("sy")
    print "sy (sys in context) ->", pycomplete("sy", imports=["import sys"])
    print "foo. ->", pycomplete("foo.")
    print "Enc (email * imported) ->",
    print pycomplete("Enc", imports=["from email import *"])
    print "E (email * imported) ->",
    print pycomplete("E", imports=["from email import *"])

    print "Enc ->", pycomplete("Enc")
    print "E ->", pycomplete("E")

# Local Variables :
# pymacs-auto-reload : t
# End :
