EMACS ?= emacs
CASK = env --unset INSIDE_EMACS EMACS=$(EMACS) cask

.PHONY: example

default: elc pkg-file

pkg-file:
	$(CASK) pkg-file

clean: clean-elc

clean-elc:
	$(CASK) clean-elc

elc: clean-elc
	$(CASK) build

test:
	make -C tests

reference:
	make -C example reference
