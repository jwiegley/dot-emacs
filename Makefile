##
## Makefile for Proof General.
## 
## Author:  David Aspinall <da@dcs.ed.ac.uk>
##
##  make		- do "compile" and "scripts" targets
##  make compile	- make .elc's in a single session
##  make all		- make .elc's in separate sessions
##  make scripts	- edit paths in isabelle interface scripts,
##			  legotags and coqtags
##
## $Id$
## 
###########################################################################


ELISP_DIRS = generic lego coq isa isar plastic demoisa hol98 phox twelf acl2
# FIXME: automate the emacs choice to be xemacs if it can be
# found, otherwise emacs.
BATCHEMACS=xemacs -batch -q -no-site-file

PWD=$(shell pwd)
BASH_SCRIPTS = isa/interface isar/interface
PERL_SCRIPTS = lego/legotags coq/coqtags

# FIXME: would rather set load path in Elisp,
# but seems tricky to do only during compilation.
# Another idea: put a function in proof-site to
# output the compile-time load path and
# ELISP_DIRS so these are set just in that one
# place.
BYTECOMP = $(BATCHEMACS) -eval '(setq load-path (append (mapcar (lambda (d) (concat "${PWD}/" (symbol-name d))) (quote (${ELISP_DIRS}))) load-path))' -f batch-byte-compile
EL=$(shell for f in $(ELISP_DIRS); do ls $$f/*.el; done)
ELC=$(EL:.el=.elc)

# These files may work now, but BC is not yet guaranteed in 3.4.
# [currently broken for prover instances]
# proof-toolbar.elc proof-menu.elc proof-indent.elc proof-x-symbol.elc
BROKENELC=proof-menu.elc # easy-menu-define expanded too early.
# NB: calls to proof-defshortcut also broken, evaluates define-key.

.SUFFIXES:	.el .elc

default: compile scripts

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
	rm -f $(ELC) 
	$(BYTECOMP) $(EL)
	rm -f $(BROKENELC)
	@echo "*************************************************"
	@echo " Finished."
	@echo "*************************************************"

all:	$(ELC)

.el.elc:
	$(BYTECOMP) $*.el
	rm -f $(BROKENELC)

##
## scripts: try to patch bash and perl scripts with correct paths
##
scripts: bashscripts perlscripts

bashscripts:
	@(bash="`which bash`"; \
	 if [ -z "$$bash" ]; then \
	   echo "Could not find bash - bash paths not checked" >&2; \
	   exit 0; \
	 fi; \
	 for i in $(BASH_SCRIPTS); do \
	   sed "s|^#.*!.*/bin/bash.*$$|#!$$bash|" < $$i > .tmp \
	   && cat .tmp > $$i; \
	 done; \
	 rm -f .tmp)

perlscripts:
	@(perl="`which perl`"; \
	 if [ -z "$$perl" ]; then \
	   echo "Could not find perl - perl paths not checked" >&2; \
	   exit 0; \
	 fi; \
	 for i in $(PERL_SCRIPTS); do \
	   sed "s|^#.*!.*/bin/perl.*$$|#!$$perl|" < $$i > .tmp \
	   && cat .tmp > $$i; \
	 done; \
	 rm -f .tmp)

clean:
	rm -f $(ELC) *~ */*~ .\#* */.\#*
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




