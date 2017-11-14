### package_date.m4

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

# Figure out timestamp information, for substitution.
# If we are in a git repo, use the timestamp of the
# most recent commit.  Otherwise, use the current time.
AC_DEFUN([AC_PACKAGE_DATE],
[
if git log -1 > /dev/null 2>&1; then
    PACKAGE_DATE="$(git log -1 --format=format:'%ci')"
elif date --rfc-3339=seconds > /dev/null 2>&1; then
    PACKAGE_DATE="$(date --rfc-3339=seconds)"
elif date -u > /dev/null 2>&1; then
    PACKAGE_DATE="$(date -u)"
else
    PACKAGE_DATE="$(date)"
fi
AC_SUBST([PACKAGE_DATE])
])
