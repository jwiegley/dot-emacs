.PHONY : test resolv clean

EMACS ?= emacs

test:	resolv
	$(EMACS) -Q -batch \
		-L . \
		-L emacs-deferred \
		-L emacs-ctable \
		-l deferred \
		-l concurrent \
		-l epc \
		-l epcs \
		-l test-epc \
		-f ert-run-tests-batch-and-exit

resolv:	clean
	git clone https://github.com/kiwanami/emacs-deferred.git \
	&& git clone https://github.com/kiwanami/emacs-ctable.git

clean:
	rm -rf ./emacs-deferred ./emacs-ctable
