byte-compile:
	emacs -Q -L . -batch -f batch-byte-compile *.el

clean:
	rm -f *.elc
