## -*- mode: makefile-gmake -*-

EMACS	    = emacs
EMACS_BATCH = $(EMACS) -batch

TARGET = $(patsubst %.el,%.elc,init.el)

DIRS    = lisp
SUBDIRS = $(shell find $(DIRS) -maxdepth 2	\
		       ! -name .git		\
		       ! -name doc		\
		       ! -name test		\
		       ! -name tests		\
		       ! -name obsolete		\
		       ! -name scripts		\
		       ! -name tools		\
		       -type d -print)

MY_LOADPATH = -L . $(patsubst %,-L %, $(SUBDIRS))
BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

.PHONY: test build clean check-litter test-xdg audit-xdg

# Main rule
all: init.el

init.org: ~/org/init.org
	@if test ~/org/init.org -nt $@; then	        \
	    rm -f $@;					\
	    cp -p ~/org/init.org $@;		        \
	    chmod 444 $@;				\
	fi

# Generate lisp and compile it
init.el: init.org
	@rm -f $@
	@$(BATCH_LOAD)						\
		--eval "(require 'org)"				\
		--eval "(org-babel-do-load-languages		\
                          'org-babel-load-languages		\
	                  '((emacs-lisp . t) (shell . t)))"	\
		--eval "(setq org-confirm-babel-evaluate nil)"	\
		--eval "(org-babel-load-file \"init.org\")"
	@chmod 444 $@

%.elc: %.el
	@echo Compiling file $<
	@$(BATCH_LOAD) -f batch-byte-compile $<

speed: init.elc
	time $(BATCH_LOAD) -Q -L . -l init		\
	    --eval "(message \"Hello, world\!\")"

slow: init.el
	time $(BATCH_LOAD) -Q -L . -l init --debug-init	\
	    --eval "(message \"Hello, world\!\")"

open: init.el
	@open $$(dirname $$(which emacs))/../Applications/*.app

open-quick: init.el
	@open $$(dirname $$(which emacs))/../Applications/*.app

clean:
	rm -f init.el *.elc *~ settings.el

# Data, state and caches live outside this checkout; see lisp/user-paths.el.

# Report runtime state that has come back into the checkout.
check-litter:
	@xdg/check-litter.sh

# Unit tests for the path library and the migration tools.
test-xdg:
	@$(EMACS_BATCH) -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit
	@$(EMACS_BATCH) -Q -l xdg/apply-init-edits-test.el -f ert-run-tests-batch-and-exit
	@xdg/migrate-test.sh
	@xdg/check-litter-test.sh

# Load the whole init in a sealed copy and report paths that still point here.
audit-xdg:
	@xdg/audit/run.sh

### Makefile ends here
