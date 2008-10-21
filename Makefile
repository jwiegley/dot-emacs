DIRS	= . site-lisp $(shell find site-lisp -type d -maxdepth 1 | egrep -v '(org-|.hg)')
SPECIAL = cus-dirs.el autoloads.el
SOURCE	= $(filter-out $(SPECIAL),$(wildcard *.el) \
	  $(wildcard site-lisp/*.el))
TARGET	= $(patsubst %.el,%.elc,$(SPECIAL) $(SOURCE))
EMACS   = emacs

all: $(TARGET)

cus-dirs.el: $(SOURCE)
	$(EMACS) --no-init-file --no-site-file -batch \
		-l cus-dep \
		-f custom-make-dependencies $(DIRS)
	mv cus-load.el cus-dirs.el

autoloads.el: autoloads.in $(SOURCE)
	cp autoloads.in autoloads.el
	-rm autoloads.elc
	$(EMACS) --no-init-file --no-site-file -batch \
		-l $(shell pwd)/autoloads \
		-f generate-autoloads \
		$(shell pwd)/autoloads.el $(DIRS)

%.elc: %.el
	$(EMACS) --no-init-file --no-site-file \
		-L . -L site-lisp -L site-lisp/muse/lisp \
		-L site-lisp/epg -L site-lisp/pydb/emacs \
		-batch -f batch-byte-compile $<

clean:
	rm -f $(TARGET) *~

fullclean: clean
	-rm *.elc cus-dirs.el autoloads.el
