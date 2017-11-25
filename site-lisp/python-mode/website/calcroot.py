#! /usr/bin/env python
#
# simple script to calculate HTROOT from ROOT_OFFSET.  Pass ROOT_OFFSET in on
# the command line

import sys
import os
import string

if sys.argv[1] == '.':
    print '.'
else:
    print string.join(['..'] * len(string.split(sys.argv[1], os.sep)), os.sep)
