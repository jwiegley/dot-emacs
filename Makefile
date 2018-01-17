## -*- mode: makefile-gmake -*-

EMACS	    = emacs
EMACS_BATCH = $(EMACS) -Q -batch

TARGET = $(patsubst %.el,%.elc, dot-gnus.el dot-org.el init.el)

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
