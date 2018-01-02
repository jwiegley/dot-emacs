## -*- mode: makefile-gmake -*-

EMACS	    = emacs
EMACS_BATCH = $(EMACS) -Q -batch

TARGET = $(patsubst %.el,%.elc, dot-gnus.el dot-org.el init.el)

DIRS    = lib lisp site-lisp
SUBDIRS = $(shell find $(DIRS) -maxdepth 2	\
		       ! -name .git		\
		       ! -name doc		\
		       ! -name dev		\
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

MY_LOADPATH = -L . $(patsubst %,-L %, $(SUBDIRS))
BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

all: $(TARGET) compile-packages compile info/dir

info/dir:
	find info				\
	     \! -name '*-[0-9]*.gz'		\
	     \! -name dir			\
	     -type f				\
	     -exec install-info {} $@ \;
	install-info							 \
	    --entry='* HyperSpec: (gcl).     The Common Lisp HyperSpec.' \
	    info/gcl.info $@

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
	    ; do (cd $$i && make ASYNC_ELPA_DIR=$(HOME)/emacs/lisp/emacs-async) \
	    ; done
	(cd site-lisp/hyperbole && make elc)

compile:
	@BATCH_LOAD="$(BATCH_LOAD)" ./compile-all $(DIRS)
	@echo All Emacs Lisp files have been compiled.

init.elc: init.el dot-org.elc dot-gnus.elc

dot-org.elc: dot-org.el

dot-gnus.elc: dot-gnus.el

%.elc: %.el
	@echo Compiling file $<
	@$(BATCH_LOAD) -f batch-byte-compile $<

pull:
	for i in release master ; do	\
	    (cd $$i ; git pull) ;	\
	done

speed:
	time emacs -L . -l init --batch --eval "(message \"Hello, world\!\")"

clean:
	rm -f info/dir
	find . -name '*.elc' -delete

### Makefile ends here
