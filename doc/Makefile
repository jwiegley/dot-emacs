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
##	make doc		  - make all kinds of doc.
##
###########################################################################

DOCNAME = ProofGeneral

MAKEINFO = makeinfo
TEXI2DVI = texi2dvi
DVI2PS = dvips
TEXI2PDF = texi2pdf
TEXI2HTML = texi2html 

.SUFFIXES:  .texi .info .dvi .html .pdf .ps

.texi.info:
	$(MAKEINFO) $< 

.texi.dvi:
	$(TEXI2DVI) $< 


.texi.pdf:
	$(TEXI2PDF) $< 

.dvi.ps:
	$(DVI2PS) $< 

.texi.html:	
	$(TEXI2HTML) $< 



## 
## doc : build info and dvi files from $(DOCNAME).texi
##
doc:	dvi info

## 
## all : build dvi, html, info
##
all:    dvi html info

dvi:    $(DOCNAME).dvi
pdf:    $(DOCNAME).pdf
html:   $(DOCNAME).html
info:   $(DOCNAME).info

# NB: for info, could make localdir automatically from
# START-INFO-DIR-ENTRY / END-INFO-DIR-ENTRY.
# Does some utility do this?

##
## clean: Remove subsidiary documentation files
##
clean:
	rm -f $(DOCNAME).?? $(DOCNAME).fns $(DOCNAME).vrs $(DOCNAME).cps 
	rm -f $(DOCNAME).aux $(DOCNAME).log $(DOCNAME).toc $(DOCNAME).cp0
	rm -f *~

##
## distclean: Remove documentation targets
##
distclean:   clean
	rm -f $(DOCNAME).info* $(DOCNAME).dvi $(DOCNAME).pdf $(DOCNAME)*.html






