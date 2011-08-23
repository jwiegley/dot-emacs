### -*- mode: makefile-gmake -*-

DIRS	    = lisp site-lisp override el-get
SPECIAL	    = cus-dirs.el autoloads.el
ORGSRC	    = $(patsubst %.org,%.el,$(wildcard *.org))
SOURCE	    = $(filter-out $(SPECIAL),$(wildcard *.el) $(wildcard site-lisp/*.el))
TARGET	    = $(patsubst %.el,%.elc,autoloads.el $(SOURCE))
EMACS	    = emacs
EMACS_BATCH = $(EMACS) --no-init-file --no-site-file -batch
MY_LOADPATH = -L . $(patsubst %,-L %,$(DIRS))
BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

all: load-path.elc $(SPECIAL) $(ORGSRC) $(TARGET)
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

%.el: %.org
	$(BATCH_LOAD) -l load-path -l override/org-mode/lisp/ob-tangle \
	    --eval '(org-babel-load-file "$<")'

load-path.elc: load-path.el
	$(BATCH_LOAD) -f batch-byte-compile $<

emacs.elc: emacs.el
	$(BATCH_LOAD) -l load-path -f batch-byte-compile $<

cus-dirs.elc:

%.elc: %.el
	$(BATCH_LOAD) -l load-path -f batch-byte-compile $<

clean:
	rm -f autoloads.el* cus-dirs.el $(ORGSRC) *.elc

fullclean: clean
	rm -f *.elc site-lisp/*.elc

### Makefile ends here
