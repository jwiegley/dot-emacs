elsrc=git-annex.el

all: $(elsrc:.el=.elc)

%.elc: %.el
	emacs -batch -q -no-site-file -eval '(byte-compile-file "$<")'

clean:
	-rm -f --verbose $(elsrc:.el=.elc)

.PHONY: all clean
