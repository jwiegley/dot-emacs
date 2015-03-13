"""
Run 'python getstamps.py' from the directory that contains your
unpublished blog entries.

You may need to make some modification for your situation. This
assumes your blog entries use a .txt extension and that you generate
them from "source" files in a different directory (with an optional
.muse extension).

History:

1.1

* Michael Olson <http://www.mwolson.org/> adapted this for Emacs Muse
  and added a few more exluded patterns for other version control
  systems.

1.0

* Original version

License:

   Copyright (c) 2006 Nathan Kent Bullock
   Copyright (c) 2006, 2007, 2008, 2009, 2010 Michael Olson

   Permission is hereby granted, free of charge, to any person obtaining
   a copy of this software and associated documentation files (the
   "Software"), to deal in the Software without restriction, including
   without limitation the rights to use, copy, modify, merge, publish,
   distribute, sublicense, and/or sell copies of the Software, and to
   permit persons to whom the Software is furnished to do so, subject to
   the following conditions:

   The above copyright notice and this permission notice shall be
   included in all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
   EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
   MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
   NONINFRINGEMENT.  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
   BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
   ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
   CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
"""
__author__ = 'Nathan Kent Bullock'
__homepage__ = 'http://bullock.moo.com/nathan/'
__email__ = 'nathan_kent_bullock -at- yahoo.ca'
__version__ = '1.1'

import re, sys, os, types

OutFile=None

# The format of the date line in each blog entry
DateRegexp = re.compile (r'^#date\s+(.+)$')

# The part of the filename of the blog entry to write to the
# timestamps file.  Only the first grouping will be used.
FileNameRegexp = re.compile (r'^(.+?)(\.muse)?$')

def getdate(f):
    for line in f:
        matched = DateRegexp.search(line)
        if matched:
            return matched.group(1)

def recurse(so_far):
    global OutFile

    for filename in os.listdir(so_far):
        filepath = so_far + "/" + filename

        # just makes output prettier.
        if filename == ".svn": continue
        if filename == ".arch-ids": continue
        if filename == "{arch}": continue
        if filename == ".bzr": continue
        if filename == "_darcs": continue

        if os.path.isdir(filepath):
            print "dir %s" % (filepath,)
            recurse(filepath)

        # You may need to modify the extension test
        if os.path.isfile(filepath) and filepath != "timestamps":
            thisfile = open(filepath,'r')
            thisdate = getdate (thisfile)
            matched = FileNameRegexp.search(filepath[2:])
            if thisdate and matched:
                thisname = matched.group(1) + ".txt"
                OutFile.write("%s %s\n" % (thisdate, thisname))
                continue

if __name__ == "__main__":
    OutFile = open("timestamps", "w+")
    recurse(".")
