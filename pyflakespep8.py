#!/usr/bin/env python

# Author: Keegan Carruthers-Smith
# https://bitbucket.org/keegancsmith/dotfiles/raw/tip/misc/pyflakespep8.py

import commands
import re
import sys

def make_re(*msgs):
    return re.compile('(%s)' % '|'.join(msgs))

pyflakes_ignore = make_re('unable to detect undefined names')
pyflakes_warning = make_re(
    'imported but unused',
    'is assigned to but never used',
    'redefinition of unused',
)
pep8_ignore = ['E501']
pep8_warning = make_re('.')

def pyflakespep8(cmd, ignore_re, warning_re):
    output = commands.getoutput(cmd)
    for line in output.splitlines():
        if ignore_re and ignore_re.search(line):
            continue
        elif ': ' in line and warning_re.search(line):
            line = '%s: WARNING %s' % tuple(line.split(': ', 1))
        print line

pyflakespep8('pyflakes %s' % sys.argv[1], pyflakes_ignore, pyflakes_warning)
print '## pyflakes above, pep8 below ##'
pep8_ignore = ' '.join('--ignore=%s' % i for i in pep8_ignore)
pyflakespep8('pep8 %s --repeat %s' % (pep8_ignore, sys.argv[1]), None, pep8_warning)
