#!/bin/sh
### autogen.sh - tool to help build BBDB from a git checkout

## Copyright (C) 2013 Christian Egli <christian.egli@sbs.ch>
## Copyright (C) 2013-2014 Roland Winkler <winkler@gnu.org>
##
## This file is part of the Insidious Big Brother Database (aka BBDB),
##
## BBDB is free software: you can redistribute it and/or modify
## it under the terms of the GNU General Public License as published by
## the Free Software Foundation, either version 3 of the License, or
## (at your option) any later version.
##
## BBDB is distributed in the hope that it will be useful,
## but WITHOUT ANY WARRANTY; without even the implied warranty of
## MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
## GNU General Public License for more details.
##
## You should have received a copy of the GNU General Public License
## along with BBDB.  If not, see <http://www.gnu.org/licenses/>.

### Commentary:

## The BBDB git repository does not include the configure script
## (and associated helpers).  The first time you fetch BBDB from git,
## run this script to generate the necessary files.

### Code:

set -e

# Refresh GNU autotools toolchain.
autoreconf --verbose --force --install --warnings=all

echo "You can now run \`./configure'."

exit 0
