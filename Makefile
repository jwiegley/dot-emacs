DIRS		 = . site-lisp $(shell find site-lisp -type d -maxdepth 1 | egrep -v '(org-|.hg)')
SPECIAL		 = cus-dirs.el autoloads.el
SOURCE		 = $(filter-out $(SPECIAL),$(wildcard *.el) $(wildcard site-lisp/*.el))
TARGET		 = $(patsubst %.el,%.elc,$(SPECIAL) $(SOURCE))
EMACS		 = emacs

EMACS_BATCH      = $(EMACS) --no-init-file --no-site-file -batch
MY_LOADPATH      = -L .					\
		   -L site-lisp				\
		   -L site-lisp/ess/lisp		\
		   -L site-lisp/muse/lisp		\
		   -L site-lisp/epg			\
		   -L site-lisp/sunrise-commander	\
		   -L site-lisp/anything		\
		   -L site-lisp/apel
EMACS_BATCH_LOAD = $(EMACS_BATCH) $(MY_LOADPATH)

all: $(TARGET)
	$(EMACS_BATCH_LOAD) -f batch-byte-recompile-directory .

cus-dirs.el: $(SOURCE)
	$(EMACS_BATCH) \
		-l cus-dep \
		-f custom-make-dependencies $(DIRS)
	mv cus-load.el cus-dirs.el

autoloads.el: autoloads.in $(SOURCE)
	cp autoloads.in autoloads.el
	-rm autoloads.elc
	$(EMACS_BATCH) \
		-l $(shell pwd)/autoloads \
		-l easy-mmode \
		-f generate-autoloads \
		$(shell pwd)/autoloads.el $(DIRS)

%.elc: %.el
	$(EMACS_BATCH_LOAD) -l $< -f batch-byte-compile $<

clean:
	rm -f $(TARGET) *~

fullclean: clean
	-rm *.elc cus-dirs.el autoloads.el
