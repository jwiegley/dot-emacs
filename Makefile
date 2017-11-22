## -*- mode: makefile-gmake -*-

DIRS	    = lib				\
	      lisp				\
	      site-lisp				\
	      site-lisp/site-dired		\
	      site-lisp/site-git		\
	      site-lisp/site-lang		\
	      site-lisp/site-company		\
	      site-lisp/site-emacs-lisp		\
	      site-lisp/site-gnus		\
	      site-lisp/site-ivy		\
	      site-lisp/site-org

LIB_SOURCE  = $(wildcard lib/*.el)				\
	      $(wildcard lisp/*.el)				\
	      $(wildcard site-lisp/*.el)			\
	      $(wildcard site-lisp/site-dired/*.el)		\
	      $(wildcard site-lisp/site-git/*.el)		\
	      $(wildcard site-lisp/site-lang/*.el)		\
	      $(wildcard site-lisp/site-company/*.el)		\
	      $(wildcard site-lisp/site-emacs-lisp/*.el)	\
	      $(wildcard site-lisp/site-gnus/*.el)		\
	      $(wildcard site-lisp/site-ivy/*.el)		\
	      $(wildcard site-lisp/site-org/*.el)

TARGET	    = $(patsubst %.el,%.elc, $(LIB_SOURCE)) \
              $(patsubst %.el,%.elc, dot-gnus.el dot-org.el init.el)

SUBDIRS     = $(shell find $(DIRS) -maxdepth 2	\
		    ! -name .git		\
		    ! -name doc			\
		    ! -name dev			\
		    ! -name test		\
		    ! -name tests		\
		    ! -name shimbun		\
		    ! -name obsolete		\
		    ! -name examples		\
		    ! -name support		\
		    ! -name style		\
		    ! -path '*/slime/lib'	\
		    -type d -print)
EMACS	    = emacs
EMACS_BATCH = $(EMACS) -Q -batch
MY_LOADPATH = -L . $(patsubst %,-L %, $(SUBDIRS))
BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

all: $(TARGET)

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
	rm -f *.elc
	find . -name '*.elc' | while read file ; do \
	    if ! test -f $$(echo $$file | sed 's/\.elc$$/.el/'); then \
		echo Removing old file: $$file ; \
		rm $$file ; \
	    fi ; \
	done

### Makefile ends here
