# main Makefile.am for BBDB
#
# Copyright (C) 2013 Christian Egli <christian.egli@sbs.ch>
# Copyright (C) 2013-2014 Roland Winkler <winkler@gnu.org>
#
# This file is part of the Insidious Big Brother Database (aka BBDB),
#
# BBDB is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# BBDB is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with BBDB.  If not, see <http://www.gnu.org/licenses/>.

SUBDIRS = lisp doc tex

doc_DATA = COPYING ChangeLog AUTHORS NEWS README TODO

EXTRA_DIST = autogen.sh

BBDB_ELPA_FILES = README COPYING lisp/*.el doc/bbdb.info doc/dir tex/*.tex
BBDB_ELPA_PACKAGE = bbdb-$(PACKAGE_VERSION).tar

# doc/dir is needed for the ELPA package
doc/dir: doc/bbdb.info
	install-info $< $@

CLEANFILES = doc/dir

# Package everything in a form suitable for ELPA.
elpa: $(BBDB_ELPA_FILES)
	$(AMTAR) --transform='s:\(lisp\|doc\|tex\)/::' \
		--transform='s::bbdb-$(PACKAGE_VERSION)/:' \
		--exclude=bbdb-loaddefs.el \
		-cf $(BBDB_ELPA_PACKAGE) $(BBDB_ELPA_FILES)
	@echo "Created $(BBDB_ELPA_PACKAGE)"
