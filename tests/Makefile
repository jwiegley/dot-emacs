# Copyright (C) 2010-2014 Free Software Foundation, Inc.

# This file is part of AUCTeX.

# GNU Emacs is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# GNU Emacs is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

### Commentary:

## Some targets:
## check: re-run all tests, writing to .log files.
## check-maybe: run all tests whose .log file needs updating
## filename.log: run tests from filename.el if .log file needs updating
## filename: re-run tests from filename.el, with no logging

## Adapted from test/automated/Makefile.in of GNU Emacs.

### Code:

SHELL = /bin/sh

EMACS = emacs
# AUCTeX source directory.
SRCDIR = ".."

# Command line flags for Emacs.
EMACSOPT = -batch -L $(SRCDIR)

# Prevent any settings in the user environment causing problems.
unexport EMACSDATA EMACSDOC EMACSPATH

## To run tests under a debugger, set this to eg: "gdb --args".
GDB =

# The actual Emacs command run in the targets below.
# Prevent any setting of EMACSLOADPATH in user environment causing problems.
emacs = EMACSLOADPATH= LC_ALL=C $(GDB) "$(EMACS)" $(EMACSOPT)

.PHONY: all check

all: check

# In GNU Emacs there is a bashism here to direct output to file and to standard
# output at the same time.
WRITE_LOG = 2>&1 | tee $@

%.log: %.el
	$(emacs) -l ert -l $< -f ert-run-tests-batch-and-exit ${WRITE_LOG}

ELFILES = $(wildcard */*.el)
LOGFILES = $(patsubst %.el,%.log, ${ELFILES})
TESTS = ${LOGFILES:.log=}

## If we have to interrupt a hanging test, preserve the log so we can
## see what the problem was.
.PRECIOUS: %.log

.PHONY: ${TESTS}

## The short aliases that always re-run the tests, with no logging.
define test_template
$(1):
	@test ! -f $(1).log || mv $(1).log $(1).log~
	@${MAKE} $(1).log WRITE_LOG=
endef

$(foreach test,${TESTS},$(eval $(call test_template,${test})))

## Re-run all the tests every time.
check:
	-@for f in */*.log; do test ! -f $$f || mv $$f $$f~; done
	@${MAKE} ${LOGFILES}

.PHONY: clean

clean:
	-rm -f */*.log */*.log~

# Makefile ends here.
