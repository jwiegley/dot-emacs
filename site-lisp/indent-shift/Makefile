EMACS = emacs
EFLAGS = -L .

test:
	$(EMACS) $(EFLAGS) -batch -l ert -l ert-tests/indent-shift-test.el \
		-f ert-run-tests-batch-and-exit
