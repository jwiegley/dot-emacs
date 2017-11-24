EMACS ?= emacs

all: pcre2el.elc

clean:
	rm -f *.elc

%.elc: %.el
	$(EMACS) --batch -L . --funcall batch-byte-compile "$<"

test: clean all
	$(EMACS) --batch -L . -l pcre2el-tests --funcall rxt-run-tests

test-interactive: clean all
	$(EMACS) -Q -nw -L . -l pcre2el-tests --funcall rxt-run-tests

sandbox: all
	$(EMACS) -Q -L . -l pcre2el

.PHONY: all test test-interactive sandbox
