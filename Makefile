##
## Makefile for Proof General.
## 
## Author:  David Aspinall <da@dcs.ed.ac.uk>
##
## Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
##
##
##  make compile
##


ELISP_DIRS = generic lego coq isa
EMACS = xemacs

PWD=$(shell pwd)

# FIXME: would rather set load path in Elisp,
# but seems tricky to do only during compilation.
# Another idea: put a function in proof-site to
# output the compile-time load path and
# ELISP_DIRS so these are set just in that one
# place.
BYTECOMP = $(EMACS) -batch -q -no-site-file -eval '(setq load-path (append (list "$(PWD)/generic" "$(PWD)/lego" "$(PWD)/coq" "$(PWD)/isa") load-path))' -f batch-byte-compile

EL=$(shell for f in $(ELISP_DIRS); do ls $$f/*.el; done)
ELC=$(shell for f in $(ELISP_DIRS); do ls $$f/*.elc 2>/dev/null; done)

.SUFFIXES:	.el .elc

## 
## compile : byte compile files in working directory:
##           Clearout old .elc's and re-compile in a
##           single Emacs process.
##
compile:
	@echo "*************************************************"
	@echo " Byte compiling..."
	@echo "*************************************************"
	(rm -f $(ELC); $(BYTECOMP) $(EL))
	@echo "*************************************************"
	@echo " Finished."
	@echo "*************************************************"


.el.elc:
	$(BYTECOMP) $*.el

##
##
##	
clean:
	rm -f $(ELC)	


