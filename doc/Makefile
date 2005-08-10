##
## Makefile for Proof General doc directory.
##
## Author:  David Aspinall <da@dcs.ed.ac.uk>
##
## Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
##
## $Id$
## 
###########################################################################
##
## Use:
##	make info,dvi,pdf,html    - build respective docs from texi source.
##	make doc		  - make default kinds of doc (dvi, info).
##
###########################################################################

default:
	$(MAKE) doc

%:
	$(MAKE) -f Makefile.doc DOCNAME=PG-adapting MAKE="$(MAKE) -f Makefile.doc" $@
	$(MAKE) -f Makefile.doc DOCNAME=ProofGeneral MAKE="$(MAKE) -f Makefile.doc" $@ 

##
## man page for proofgeneral script
##
# man: proofgeneral.1
#
proofgeneral.1: ../bin/proofgeneral
	help2man --output=$@  ../bin/proofgeneral
