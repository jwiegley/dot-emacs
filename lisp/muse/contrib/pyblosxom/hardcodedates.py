"""
This allows the user to create a file "timestamps" in their top-level
blog entries directory, that will override the timestamp of any given
blog entry.

Each line in this file should be in one of the following forms.

"YYYY-MM-DD-hh-mm file-name"
"YYYY-MM-DD file-name"

Then for any entry that one of these lines exist the system will use
that timestamp instead of the actual files modification time.

Note: the filename is relative to your data-dir.  An example follows
of a line for the file /var/data-dir/school/abc.txt, where the
top-level blog entries directory is "/var/data-dir/" and the date is
Aug 9, 2004.

2004-08-09-00-00 school/abc.txt

History:

1.3

* Michael Olson <http://www.mwolson.org/> made it optional to include
  the hours and minutes.

1.2

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
__version__ = '1.3'

from Pyblosxom import tools
import os, re, time, sys

FILETIME = re.compile('^([0-9]{4})-([0-1][0-9])-([0-3][0-9])(-([0-2][0-9])-([0-5][0-9]))? +(.*)$')

all_timestamps = None

def get_all_timestamps(datadir):
    f = open(datadir + "/timestamps")
    t = []
    while True:
        str = f.readline()
        if str == "": break
        m = FILETIME.search(str.strip())
        if m:
            year = int(m.group(1))
            mo = int(m.group(2))
            day = int(m.group(3))
            if m.group(4):
                hr = int(m.group(5))
                minute = int(m.group(6))
            else:
                hr = 0
                minute = 0
            mtime = time.mktime((year,mo,day,hr,minute,0,0,0,-1))
            
            t.append( (datadir + "/" + m.group(7), mtime) )

    f.close()
    return t

def cb_filestat(args):
    global all_timestamps

    filename = args["filename"]
    stattuple = args["mtime"]

    for fname,mtime in all_timestamps:
        if fname == filename:
            args["mtime"] = tuple(list(stattuple[:8]) + [mtime] + list(stattuple[9:]))
            break

    return args

def cb_start(args):
    global all_timestamps
    all_timestamps = get_all_timestamps(args["request"].getConfiguration()['datadir'])
