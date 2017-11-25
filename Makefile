EMACS ?= emacs

all: macrostep.elc macrostep-c.elc

clean:
	rm -f *.elc

test: clean all
	$(EMACS) --batch -L . --load macrostep-test.el

sandbox: all
	$(EMACS) -Q -L . --load macrostep --load macrostep-c

%.elc: %.el
	$(EMACS) --batch -L . --funcall batch-byte-compile "$<"

.PHONY: test all clean
