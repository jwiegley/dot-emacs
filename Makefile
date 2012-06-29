### -*- mode: makefile-gmake -*-

DIRS	    = override lib lisp site-lisp
SPECIAL	    = cus-dirs.el autoloads.el
INIT_SOURCE = $(wildcard *.el)
LIB_SOURCE  = $(wildcard override/*.el) $(wildcard lib/*.el) \
	      $(wildcard lisp/*.el) $(wildcard site-lisp/*.el)
TARGET	    = autoloads.elc $(patsubst %.el,%.elc, $(LIB_SOURCE))
EMACS	    = emacs
EMACS_BATCH = $(EMACS) -Q -batch
MY_LOADPATH = -L . $(patsubst %,-L %,$(DIRS))
BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

all: $(SPECIAL) $(TARGET)
	for dir in $(DIRS); do \
	    $(BATCH_LOAD) -f batch-byte-recompile-directory $$dir; \
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

%.elc: %.el
	$(BATCH_LOAD) -l load-path -f batch-byte-compile $<

init.elc: init.el
	@rm -f $@
	$(BATCH_LOAD) -l init -f batch-byte-compile $<

clean:
	rm -f autoloads.el* cus-dirs.el *.elc

fullclean: clean
	rm -f $(TARGET)

### Makefile ends here
