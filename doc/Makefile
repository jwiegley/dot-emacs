##
## Makefile for Proof General doc directory.
##
## Author:  David Aspinall <da@dcs.ed.ac.uk>
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

# program to make info files from .texi
MAKEINFO = makeinfo
# program to make dvi files from .texi
TEXI2DVI = texi2dvi
# program to make pdf files from .texi
TEXI2PDF = texi2pdf
# program to make html files from .texi
TEXI2HTML = texi2html 

.SUFFIXES:  .texi .info .dvi .html .pdf

.texi.info:
	$(MAKEINFO) $< 

.texi.dvi:
	$(TEXI2DVI) $< 

.texi.pdf:
	$(TEXI2PDF) $< 

.texi.html:	
	$(TEXI2HTML) $< 



## 
## doc : build info and dvi files from $(DOCNAME).texi
##
doc:	dvi info

## 
## doc : build dvi, pdf, html, info
##
all:    dvi pdf html info

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
	rm -f $(DOCNAME).?? $(DOCNAME).cps $(DOCNAME).cp0
	rm -f $(DOCNAME).aux $(DOCNAME).log $(DOCNAME).toc
	rm -f *~

##
## distclean: Remove documentation targets
##
distclean:   clean
	rm -f $(DOCNAME).info* $(DOCNAME).dvi $(DOCNAME).pdf $(DOCNAME)*.html





