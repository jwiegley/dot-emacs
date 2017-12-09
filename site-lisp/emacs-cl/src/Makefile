# Copyright (C) 2003, 2004 Lars Brinkhoff.

#EMACS = emacs19
EMACS = emacs20
#EMACS = emacs21
#EMACS = xemacs20
#EMACS = xemacs21

EMACSEN = emacs20 emacs21 xemacs21 # ../emacs-19.34/src/emacs

all:
	$(EMACS) -batch -l load-cl.el -f compile-cl

#install:

TESTFILES = -l load-cl.el -l batch.el -l tests.el

check:
	mv check.log previous.log 2> /dev/null
	for e in $(EMACSEN); do						\
		echo CHECKING $$e;					\
		make clean > /dev/null;					\
		echo Interpreting...;					\
		$$e -batch $(TESTFILES) -f test-cl 2> /dev/null;	\
		echo Compiling...;					\
		make EMACS=$$e > /dev/null 2>&1;			\
		$$e -batch $(TESTFILES) -f test-cl 2> /dev/null;	\
	done | tee check.log
	make clean

clean:
	rm -f *.elc
