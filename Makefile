##
## Makefile for Proof General.
## 
## Author:  David Aspinall <da@dcs.ed.ac.uk>
##
##  make compile	- make .elc's in a single session
##  make all		- make .elc's in separate sessions
##
## $Id$
## 
###########################################################################


ELISP_DIRS = generic lego coq isa isar plastic demoisa hol98
# FIXME: automate the emacs choice to be xemacs if it can be
# found, otherwise emacs.
EMACS = xemacs

PWD=$(shell pwd)

# FIXME: would rather set load path in Elisp,
# but seems tricky to do only during compilation.
# Another idea: put a function in proof-site to
# output the compile-time load path and
# ELISP_DIRS so these are set just in that one
# place.
BYTECOMP = $(EMACS) -batch -q -no-site-file -eval '(setq load-path (append (list "$(PWD)/generic" "$(PWD)/lego" "$(PWD)/coq" "$(PWD)/isa" "$(PWD)/isar" "$(PWD)/plastic") load-path))' -f batch-byte-compile

EL=$(shell for f in $(ELISP_DIRS); do ls $$f/*.el; done)
ELC=$(EL:.el=.elc)

.SUFFIXES:	.el .elc

## 
## compile : byte compile files in working directory:
##           Clearout old .elc's and re-compile in a
##           single Emacs process.  This is faster than make all,
##	     but can have artefacts because of context between
##	     compiles.
##
compile:
	@echo "*************************************************"
	@echo " Byte compiling..."
	@echo "*************************************************"
	(rm -f $(ELC); $(BYTECOMP) $(EL))
	@echo "*************************************************"
	@echo " Finished."
	@echo "*************************************************"

all:	$(ELC)

.el.elc:
	$(BYTECOMP) $*.el

##
##
##	
clean:
	rm -f $(ELC) *~ 
	(cd doc; $(MAKE) clean)


##
## This special target lets us use targets defined 
## in developer's makefile Makefile.devel conveniently,
## via make devel.<target>
##

devel.%:
	make -f Makefile.devel $*

##
## Similarly for xemacs Makefile.
##

xemacs.%:
	make -f Makefile.xemacs $*




