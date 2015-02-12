## -*- mode: makefile-gmake -*-

DIRS	    = override lib lisp site-lisp \
	      $(HOME)/src/ledger/lisp
#SPECIAL	    = cus-dirs.el autoloads.el
SPECIAL	    = cus-dirs.el
LIB_SOURCE  = $(wildcard override/*.el) $(wildcard lib/*.el) \
	      $(wildcard lisp/*.el) $(wildcard site-lisp/*.el)
#TARGET	    = autoloads.elc \
#              $(patsubst %.el,%.elc, $(LIB_SOURCE) $(INIT_SOURCE))
TARGET	    = $(patsubst %.el,%.elc, $(LIB_SOURCE)) \
              $(patsubst %.el,%.elc, \
                 load-path.el cus-dirs.el gnus-settings.el org-settings.el \
                 settings.el dot-gnus.el dot-org.el init.el)
EMACS	    = emacs
EMACS_BATCH = $(EMACS) -Q -batch
MY_LOADPATH = -L . $(patsubst %,-L %,$(DIRS))
BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

all: $(SPECIAL) $(TARGET)

compile:
	for dir in $(DIRS); do \
	    ($(BATCH_LOAD) --eval '(batch-byte-recompile-directory 0)' $$dir); \
	done

cus-dirs.el: Makefile $(LIB_SOURCE)
	$(EMACS_BATCH) -l cus-dep -f custom-make-dependencies $(DIRS)
	mv cus-load.el cus-dirs.el

autoloads.el: Makefile autoloads.in $(LIB_SOURCE)
	cp -p autoloads.in autoloads.el
	-rm -f autoloads.elc
	$(EMACS_BATCH) -l $(shell pwd)/autoloads -l easy-mmode \
	    -f generate-autoloads $(shell pwd)/autoloads.el $(DIRS) \
	    $(shell find $(DIRS) -maxdepth 1 -type d -print)

autoloads.elc: autoloads.el

settings.elc: settings.el
	@rm -f $@
	$(BATCH_LOAD) -l init -f batch-byte-compile $<

init.elc: init.el
	@rm -f $@
	$(BATCH_LOAD) -l init -f batch-byte-compile $<

org-settings.elc: org-settings.el
	@rm -f $@
	$(BATCH_LOAD) -l init -f batch-byte-compile $<

dot-org.elc: dot-org.el
	@rm -f $@
	$(BATCH_LOAD) -l init -f batch-byte-compile $<

gnus-settings.elc: gnus-settings.el
	@rm -f $@
	$(BATCH_LOAD) -l init -f batch-byte-compile $<

dot-gnus.elc: dot-gnus.el
	@rm -f $@
	$(BATCH_LOAD) -l init -f batch-byte-compile $<

%.elc: %.el
	$(BATCH_LOAD) -l load-path -f batch-byte-compile $<

clean:
	rm -f autoloads.el* cus-dirs.el *.elc

fullclean: clean
	rm -f $(TARGET)

### Makefile ends here
