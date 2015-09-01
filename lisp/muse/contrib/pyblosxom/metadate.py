"""
Purpose:

  If an entry contains a #postdate metatag, metadate.py makes
  pyblosxom use that as the entry's date instead of the file's mtime.

To use:

  Place this file in your pyblosxom plugins directory.

  If you have previously assigned a value to py['load_plugins'] in
  your config.py file, add this module to that list.

  Tag an entry with a metadata line like so:
    #postdate YYYY-MM-DD HH-MM

Developer Info:

  There really isn't a clean way to implement this (as far as I can
  tell).  The cb_filestat callback isn't passed the entry, and none of
  the other callbacks are passed the mtime, and we really need them
  both to do this properly.

  The ugly--but functional--solution to this problem is to go into the
  file and dig the metadata out directly.  That is what I have done
  here.

  Since the entries are now being opened twice each, this could result
  in decently-sized (relatively speaking) performance hit.  Consider
  yourself warned.

License:

  Permission is hereby granted, free of charge, to any person
  obtaining a copy of this software and associated documentation files
  (the"Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge,
  publish, distribute, sublicense, and/or sell copies of the Software,
  and to permit persons to whom the Software is furnished to do so,
  subject to the following conditions:

  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.

Copyright 2005 Cameron Desautels
"""

import os, re, time

__author__ = 'Cameron Desautels <cam@apt2324.com>'
__version__ = 'metadate.py, v 0.1'
__description__ = 'Implements overriding of mtime with #postdate metadata.'

DATEFORMAT = re.compile('([0-9]{4})-([0-1][0-9])-([0-3][0-9]) ([0-2][0-9]):([0-5][0-9])')

def cb_filestat(args):
    stattuple = args['mtime']

    try:
        story = open(args['filename']).readlines()
    except IOError:
        raise IOError

    if story:
        story.pop(0) #throw away the title

        while story:
            metamatch = re.match(r'#(\w+)\s+(.*)', story[0])
            if metamatch:
                if metamatch.groups()[0] == 'postdate':
                    datematch = DATEFORMAT.match(metamatch.groups()[1].strip())
                    if datematch:
                        # year, month, day, hour, minute
                        mtime = time.mktime((int(datematch.groups()[0]),int(datematch.groups()[1]), \
                                             int(datematch.groups()[2]),int(datematch.groups()[3]), \
                                             int(datematch.groups()[4]),0,0,0,-1))

                        args['mtime'] = tuple(list(stattuple[:8]) + [mtime] + list(stattuple[9:]))

                    # whether the postdate line was correct or malformed, we found it, so quit
                    break
                else:
                    # that wasn't the right metadata line, so chuck it and keep going
                    story.pop(0)
            else:
                # quit when all metadata has been examined
                break

    return args
