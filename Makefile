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
		       -type d -print)

MY_LOADPATH = -L . $(patsubst %,-L %, $(SUBDIRS))
BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

.PHONY: test build clean

# Main rule
all: init.el

init.org: ~/org/area/emacs/init.org
	@if test ~/org/area/emacs/init.org -nt $@; then	\
	    rm -f $@;					\
	    cp -p ~/org/area/emacs/init.org $@;		\
	    chmod 444 $@;				\
	fi

# Generate lisp and compile it
init.el: init.org
	@rm -f $@
	@$(BATCH_LOAD)						\
		--eval "(require 'org)"				\
		--eval "(org-babel-load-file \"init.org\")"
	@chmod 444 $@

compile:
	@BATCH_LOAD="$(BATCH_LOAD)" ./compile-all $(DIRS)
	@echo All Emacs Lisp files have been compiled.

init.elc: init.el

%.elc: %.el
	@echo Compiling file $<
	@$(BATCH_LOAD) -f batch-byte-compile $<

speed: init.elc
	time $(BATCH_LOAD) -Q -L . -l init		\
	    --eval "(message \"Hello, world\!\")"

slow: init.elc
	time $(BATCH_LOAD) -Q -L . -l init --debug-init	\
	    --eval "(message \"Hello, world\!\")"

open: init.el
	@open $$(dirname $$(which emacs))/../Applications/*.app

open-quick: init.el
	@open $$(dirname $$(which emacs))/../Applications/*.app

clean:
	rm -f init.el *.elc *~ settings.el

### Makefile ends here
