.POSIX :
EMACS = emacs
BATCH = $(EMACS) -batch -Q -L .

compile : simple-httpd.elc simple-httpd-test.elc

test : simple-httpd-test.elc simple-httpd.elc
	$(BATCH) -l simple-httpd-test.elc -f ert-run-tests-batch

clean :
	rm -f simple-httpd.elc simple-httpd-test.elc

simple-httpd.elc : simple-httpd.el
simple-httpd-test.elc : simple-httpd-test.el

.PHONY : compile test clean
.SUFFIXES : .el .elc

.el.elc :
	$(BATCH) -f batch-byte-compile $<
