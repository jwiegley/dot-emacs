### -*- mode: makefile-gmake -*-

DIRS	    = . site-lisp
SPECIAL	    = cus-dirs.el autoloads.el
ORGSRC	    = $(patsubst %.org,%.el,$(wildcard *.org))
SOURCE	    = $(filter-out $(SPECIAL),$(wildcard *.el) $(wildcard site-lisp/*.el))
TARGET	    = $(patsubst %.el,%.elc,autoloads.el $(SOURCE))
EMACS	    = emacs
EMACS_BATCH = $(EMACS) --no-init-file --no-site-file -batch
MY_LOADPATH = -L $(HOME)/.emacs.d -L . -L site-lisp
BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

all: $(ORGSRC) $(SPECIAL) $(TARGET)

cus-dirs.el: $(SOURCE)
	$(EMACS_BATCH) -l cus-dep -f custom-make-dependencies $(DIRS)
	mv cus-load.el cus-dirs.el

autoloads.el: autoloads.in $(SOURCE)
	cp -p autoloads.in autoloads.el
	-rm -f autoloads.elc
	$(EMACS_BATCH) -l $(shell pwd)/autoloads -l easy-mmode \
	    -f generate-autoloads $(shell pwd)/autoloads.el $(DIRS)

%.el: %.org
	$(BATCH_LOAD) -l load-path --eval '(org-babel-load-file "$<")'

emacs.elc: emacs.el
	$(BATCH_LOAD) -l load-path -f batch-byte-compile $<

cus-dirs.elc:

%.elc: %.el
	$(BATCH_LOAD) -l load-path -l $< -f batch-byte-compile $<

clean:
	rm -f autoloads.el* cus-dirs.el

fullclean: clean
	rm -f *.elc site-lisp/*.elc

### Makefile ends here
