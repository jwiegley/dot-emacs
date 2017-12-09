EMACS=emacs

EMACS_CLEAN=-Q
EMACS_BATCH=$(EMACS_CLEAN) --batch -L "auctex-11.87.7/" -L "tests/auctex-11.87.7/" -l "auctex-autoloads.el" -L "elnode/" -L "tests/elnode/" 
TESTS=

CURL=curl --silent
WORK_DIR=$(shell pwd)
PACKAGE_NAME=$(shell basename $(WORK_DIR))
AUTOLOADS_FILE=$(PACKAGE_NAME)-autoloads.el
TRAVIS_FILE=.travis.yml
TEST_DIR=tests
TEST_DEP_1=ert
TEST_DEP_2=cl-lib
TEST_DEP_1_STABLE_URL=http://git.savannah.gnu.org/cgit/emacs.git/plain/lisp/emacs-lisp/ert.el?h=emacs-24.3
TEST_DEP_2_STABLE_URL=http://elpa.gnu.org/packages/cl-lib-0.5.el
TEST_DEP_1_LATEST_URL=http://git.savannah.gnu.org/cgit/emacs.git/plain/lisp/emacs-lisp/ert.el?h=master
TEST_DEP_2_LATEST_URL=http://elpa.gnu.org/packages/cl-lib-0.5.el

.PHONY : build downloads downloads-latest autoloads test-autoloads test-travis \
         test test-interactive clean edit test-dep-1 test-dep-2 test-dep-3     \
         test-dep-4 test-dep-5 test-dep-6 test-dep-7 test-dep-8 test-dep-9

build :
	echo "hi " $(shell pwd) && \
	$(EMACS) $(EMACS_BATCH)   -L . -L .. -L tests/ --eval \
	    "(progn                                \
	      (unless (fboundp 'function-put) (defalias 'function-put #'(lambda (f prop value) (put f prop value)))) \
	      (defun define-error (name message &optional parent) (unless parent (setq parent 'error)) (let ((conditions (if (consp parent) (apply #'nconc (mapcar (lambda (parent) (cons parent (or (get parent 'error-conditions) (error \"Unknown signal %s\" parent)))) parent)) (cons parent (get parent 'error-conditions))))) (put name 'error-conditions (delete-dups (copy-sequence (cons name conditions)))) (when message (put name 'error-message message)))) \
	      (setq byte-compile-error-on-warn t)  \
	      (batch-byte-compile))" *.el

test-dep-1 :
	@cd $(TEST_DIR)                                      && \
	$(EMACS) $(EMACS_BATCH)  -L . -L .. -l $(TEST_DEP_1) || \
	(echo "Can't load test dependency $(TEST_DEP_1).el, run 'make downloads' to fetch it" ; exit 1)

test-dep-2 :
	@cd $(TEST_DIR)                                      && \
	$(EMACS) $(EMACS_BATCH)  -L . -L .. -l $(TEST_DEP_2) || \
	(echo "Can't load test dependency $(TEST_DEP_2).el, run 'make downloads' to fetch it" ; exit 1)

downloads :
	$(CURL) '$(TEST_DEP_1_STABLE_URL)' > $(TEST_DIR)/$(TEST_DEP_1).el && \
	$(CURL) '$(TEST_DEP_2_STABLE_URL)' > $(TEST_DIR)/$(TEST_DEP_2).el

downloads-latest :
	$(CURL) '$(TEST_DEP_1_LATEST_URL)' > $(TEST_DIR)/$(TEST_DEP_1).el && \
	$(CURL) '$(TEST_DEP_2_LATEST_URL)' > $(TEST_DIR)/$(TEST_DEP_2).el

autoloads :
	$(EMACS) $(EMACS_BATCH) --eval                       \
	    "(progn                                          \
	      (setq generated-autoload-file \"$(WORK_DIR)/$(AUTOLOADS_FILE)\") \
	      (update-directory-autoloads \"$(WORK_DIR)\"))"

test-autoloads : autoloads
	@$(EMACS) $(EMACS_BATCH) -L . -l "./$(AUTOLOADS_FILE)"      || \
	 ( echo "failed to load autoloads: $(AUTOLOADS_FILE)" && false )

test-travis :
	@if test -z "$$TRAVIS" && test -e $(TRAVIS_FILE); then travis-lint $(TRAVIS_FILE); fi

test : build test-dep-1 test-dep-2
	@cd $(TEST_DIR)                                   && \
	echo "hi " $(pwd) && \
	(for test_lib in *-test.el; do                       \
	    $(EMACS) $(EMACS_BATCH) -L . -L .. -l cl -l cl-lib -l $$test_lib --eval \
	    "(progn                                          \
	      (unless (fboundp 'function-put) (defalias 'function-put #'(lambda (f prop value) (put f prop value)))) \
	      (defun define-error (name message &optional parent) (unless parent (setq parent 'error)) (let ((conditions (if (consp parent) (apply #'nconc (mapcar (lambda (parent) (cons parent (or (get parent 'error-conditions) (error \"Unknown signal %s\" parent)))) parent)) (cons parent (get parent 'error-conditions))))) (put name 'error-conditions (delete-dups (copy-sequence (cons name conditions)))) (when message (put name 'error-message message)))) \
	      (fset 'ert--print-backtrace 'ignore)           \
	      (ert-run-tests-batch-and-exit '(and \"$(TESTS)\" (not (tag :interactive)))))" || exit 1; \
	done)

clean :
	@rm -f $(AUTOLOADS_FILE) *.elc *~ */*.elc */*~ $(TEST_DIR)/$(TEST_DEP_1).el            \
        $(TEST_DIR)/$(TEST_DEP_2).el $(TEST_DIR)/$(TEST_DEP_3).el $(TEST_DIR)/$(TEST_DEP_4).el \
        $(TEST_DIR)/$(TEST_DEP_5).el $(TEST_DIR)/$(TEST_DEP_6).el $(TEST_DIR)/$(TEST_DEP_7).el \
        $(TEST_DIR)/$(TEST_DEP_8).el $(TEST_DIR)/$(TEST_DEP_9).el
