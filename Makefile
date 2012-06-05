### -*- mode: makefile-gmake -*-

DIRS	    = lisp lib site-lisp override
SPECIAL	    = autoloads.el cus-dirs.el
SOURCE	    = $(filter-out $(SPECIAL),$(wildcard *.el) \
		$(wildcard lib/*.el) $(wildcard site-lisp/*.el))
TARGET	    = $(patsubst %.el,%.elc,autoloads.el $(SOURCE))
EMACS	    = emacs
EMACS_BATCH = $(EMACS) --no-init-file --no-site-file -batch
MY_LOADPATH = -L . $(patsubst %,-L %,$(DIRS))
BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

all: load-path.elc autoloads.el autoloads.elc cus-dirs.el $(TARGET)
	for dir in $(DIRS); do \
	    $(BATCH_LOAD) -f batch-byte-recompile-directory $$dir; \
	done

cus-dirs.el: Makefile $(SOURCE)
	$(EMACS_BATCH) -l cus-dep -f custom-make-dependencies $(DIRS)
	mv cus-load.el cus-dirs.el

autoloads.el: Makefile autoloads.in $(SOURCE)
	cp -p autoloads.in autoloads.el
	-rm -f autoloads.elc
	$(EMACS_BATCH) -l $(shell pwd)/autoloads -l easy-mmode \
	    -f generate-autoloads $(shell pwd)/autoloads.el $(DIRS) \
	    $(shell find $(DIRS) -maxdepth 1 -type d -print)

cus-dirs.elc: cus-dirs.el
	@echo Not compiling cus-dirs.el

settings.elc: settings.el
	@echo Not compiling settings.el

load-path.elc: load-path.el
	$(BATCH_LOAD) -f batch-byte-compile $<

%.elc: %.el
	$(BATCH_LOAD) -l load-path -f batch-byte-compile $<

clean:
	rm -f autoloads.el* cus-dirs.el *.elc

fullclean: clean
	find . -name '*.elc' -type f -delete

### Makefile ends here
