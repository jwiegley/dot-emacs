EMACS = emacs

check: compile

compile:
	$(EMACS) --version
	$(EMACS) -q -batch -f batch-byte-compile yagist.el
