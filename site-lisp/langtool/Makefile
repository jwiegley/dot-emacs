EMACS = emacs

check: compile print-encoding
	$(EMACS) -q -batch -l langtool.el -l .test-init.el -l langtool-test.el \
		-f ert-run-tests-batch-and-exit
	$(EMACS) -q -batch -l langtool.elc -l .test-init.el -l langtool-test.el \
		-f ert-run-tests-batch-and-exit

compile:
	$(EMACS) -q -batch -f batch-byte-compile \
		langtool.el

# print encoding conversion
print-encoding:
	@$(EMACS) -batch -l "./langtool.el" -eval "(mapc (lambda (cs) (let ((jcs (langtool--java-coding-system cs))) (princ (format \"%s -> %s\n\" cs jcs)))) (sort (coding-system-list) 'string-lessp))" 

save-encoding:
	@$(MAKE) -s print-encoding > ./encodings/`date +%Y%m%dT%H%M%S`.txt
