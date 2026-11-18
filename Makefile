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

# An init.org that does not call the guard of lisp/user-paths.el dates from
# before state moved out of this directory.  Emacs would start from it on
# empty histories, and keep its state here again.  Such a file is neither
# copied here nor tangled, and init.el stays as it was.  It can come back
# from the ~/org repository or from another host.  The check reads the text:
# the call counts wherever it stands on a line that is not a Lisp comment.
# Whether it is tangled shows in init.el, which is checked once it is built.
GUARD = ^[^;]*(user-paths-check-migrated

init.org: ~/org/init.org
	@if test ~/org/init.org -nt $@; then				\
	    grep -q '$(GUARD)' ~/org/init.org; found=$$?;		\
	    if test $$found -eq 1; then					\
		echo '~/org/init.org does not call'			\
		     '(user-paths-check-migrated).' >&2;		\
		echo 'An init.org without that call predates the move'	\
		     'of state out of this directory, so it is not'	\
		     'copied here and init.el is left as it was.'	\
		     'Restore ~/org/init.org; its versions are'		\
		     'listed by "git -C ~/org log -- init.org".' >&2;	\
		exit 1;							\
	    fi;								\
	    test $$found -eq 0 || exit $$found;				\
	    rm -f $@;							\
	    cp -p ~/org/init.org $@;					\
	    chmod 444 $@;						\
	fi

# An init.el from before the move can arrive from another host as well,
# newer than init.org, and make would call it up to date.  One that does
# not call the guard is built again.
ifneq ($(wildcard init.el),)
ifneq ($(shell grep -q '$(GUARD)' init.el; echo $$?),0)
.PHONY: stale-init
init.el: stale-init
endif
endif

# Generate lisp and compile it.  The copy of init.org here can be stale
# while ~/org/init.org is not (an old init.org checked out from git, or a
# copy from another host), so it is checked again before it is tangled.
# A compiled init.elc would be loaded in place of the init.el built here,
# so it goes as well; `make speed' builds it again.
init.el: init.org
	@grep -q '$(GUARD)' init.org; found=$$?;			\
	if test $$found -eq 1; then					\
	    echo 'init.org does not call'				\
		 '(user-paths-check-migrated).' >&2;			\
	    echo 'An init.org without that call predates the move of'	\
		 'state out of this directory, so it is not built and'	\
		 'init.el is left as it was.  Run'			\
		 '"touch ~/org/init.org" to have the current one'	\
		 'copied here.' >&2;					\
	    exit 1;							\
	fi;								\
	test $$found -eq 0
	@rm -f $@ $@c
	@$(BATCH_LOAD)						\
		--eval "(require 'org)"				\
		--eval "(org-babel-do-load-languages		\
                          'org-babel-load-languages		\
	                  '((emacs-lisp . t) (shell . t)))"	\
		--eval "(setq org-confirm-babel-evaluate nil)"	\
		--eval "(org-babel-load-file \"init.org\")"
	@grep -q '$(GUARD)' $@ || {					\
	    echo 'init.el was built and does not call'			\
		 '(user-paths-check-migrated): in init.org the call'	\
		 'is not in a source block that is tangled.' >&2;	\
	    exit 1;							\
	}
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

# Unit tests for the path library, the migration tools and this Makefile.
test-xdg:
	@$(EMACS_BATCH) -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit
	@$(EMACS_BATCH) -Q -l xdg/apply-init-edits-test.el -f ert-run-tests-batch-and-exit
	@xdg/migrate-test.sh
	@xdg/check-litter-test.sh
	@xdg/make-init-test.sh

# Load the whole init in a sealed copy and report paths that still point here.
audit-xdg:
	@xdg/audit/run.sh

### Makefile ends here
