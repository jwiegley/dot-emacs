EMACS = emacs

check: compile
	$(EMACS) -q -batch -l erefactor.el -l erefactor-test.el \
		-f ert-run-tests-batch-and-exit
	$(EMACS) -q -batch -l erefactor.elc -l erefactor-test.el \
		-f ert-run-tests-batch-and-exit

compile:
	$(EMACS) --version
	$(EMACS) -q -batch -f batch-byte-compile erefactor.el
