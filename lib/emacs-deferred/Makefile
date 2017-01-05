EMACS ?= emacs
CASK ?= cask

.PHONY: test test-deferred test-concurrent compile clean print-deps travis-ci

test: test-deferred test-deferred-compiled test-concurrent
# test-concurrent-compiled

test-deferred:
	$(CASK) exec ert-runner test/deferred-test.el

test-deferred-compiled: deferred.elc
	$(CASK) exec ert-runner test/deferred-test.el -l deferred.elc

test-concurrent:
	$(CASK) exec ert-runner test/concurrent-test.el

test-concurrent-compiled: concurrent.elc
	$(CASK) exec ert-runner test/concurrent-test.el -l concurrent.elc

compile: deferred.elc concurrent.elc

%.elc: %.el
	$(EMACS) -batch -L . -f batch-byte-compile $<

clean:
	rm -rfv *.elc

print-deps:
	@echo "----------------------- Dependencies -----------------------"
	$(EMACS) --version
	@echo "------------------------------------------------------------"

travis-ci: print-deps
	$(MAKE) clean test
	$(MAKE) compile test
