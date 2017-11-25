## -*- mode: makefile-gmake -*-

DIRS	    = lib lisp site-lisp

LIB_SOURCE  = $(wildcard lib/*.el)		\
	      $(wildcard lisp/*.el)		\
	      $(wildcard site-lisp/*.el)

TARGET	    = $(patsubst %.el,%.elc, $(LIB_SOURCE))			\
              $(patsubst %.el,%.elc, dot-gnus.el dot-org.el init.el)

SUBDIRS     = $(shell find $(DIRS) -maxdepth 2	\
		    ! -name .git		\
		    ! -name doc			\
		    ! -name dev			\
		    ! -name test		\
		    ! -name tests		\
		    ! -name testing		\
		    ! -name shimbun		\
		    ! -name obsolete		\
		    ! -name examples		\
		    ! -name samples		\
		    ! -name support		\
		    ! -name targets		\
		    ! -name style		\
		    ! -path '*/slime/lib'	\
		    -type d -print)
EMACS	    = emacs
EMACS_BATCH = $(EMACS) -Q -batch
MY_LOADPATH = -L . $(patsubst %,-L %, $(SUBDIRS))
BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

all: $(TARGET)

compile-packages:
	for i in				\
	    site-lisp/ProofGeneral		\
	    site-lisp/auctex			\
	    site-lisp/avy			\
	    site-lisp/company-mode		\
	    site-lisp/deft			\
	    site-lisp/ebdb			\
	    site-lisp/evil			\
	    site-lisp/flycheck			\
	    site-lisp/haskell-mode		\
	    site-lisp/helm			\
	    site-lisp/hyperbole			\
	    site-lisp/lusty-emacs		\
	    site-lisp/org-mode			\
	    site-lisp/slime			\
	    site-lisp/swiper			\
	    ; do (cd $$i && make ASYNC_ELPA_DIR=$HOME/emacs/lisp/emacs-async) ; done

compile:
	@BATCH_LOAD="$(BATCH_LOAD)" ./compile-all $(DIRS)
	@echo All Emacs Lisp files have been compiled.

init.elc: init.el dot-org.elc dot-gnus.elc
	@rm -f $@
	@echo Compiling file init.el
	@$(BATCH_LOAD) -f batch-byte-compile init.el

dot-org.elc: dot-org.el
	@rm -f $@
	@echo Compiling file dot-org.el
	@$(BATCH_LOAD) -f batch-byte-compile dot-org.el

dot-gnus.elc: dot-gnus.el
	@rm -f $@
	@echo Compiling file dot-gnus.el
	@$(BATCH_LOAD) -f batch-byte-compile dot-gnus.el

%.elc: %.el
	@echo Compiling file $<
	@$(BATCH_LOAD) -f batch-byte-compile $<

clean:
	find . -name '*.elc' -delete

### Makefile ends here
