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

DVICONCAT = dviconcat
DVISELECT = dviselect

# Assumes actual first two pages belong to titlepage
TITLERANGE = =1,=2

# Assumes that main document starts on third actual page
MAINRANGE = =3,=4,3:

TOC = :_1

DVI2PS = dvips
TEXI2PDF = texi2pdf
TEXI2HTML = texi2html
EMACS = xemacs -batch

.SUFFIXES:  .texi .info .dvi .html .pdf .ps

.texi.info:
	$(MAKEINFO) $< 

.texi.dvi:
	$(TEXI2DVI) $<
	$(DVISELECT) -i $*.dvi -o $*.tmp1 $(TITLERANGE)
	$(DVISELECT) -i $*.dvi -o $*.tmp2 $(MAINRANGE)
	$(DVISELECT) -i $*.dvi -o $*.tmp3 $(TOC)
	$(DVICONCAT) -o $*.dvi $*.tmp1 $*.tmp3 $*.tmp2 
	rm -f $*.tmp1 $*.tmp2 $*.tmp3


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
## all : build dvi, ps, html, info
##
all:    dvi ps html info

dvi:    $(DOCNAME).dvi
ps:	$(DOCNAME).ps
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
	rm -f $(DOCNAME).kys
	rm -f *~

##
## distclean: Remove documentation targets
##
distclean:   clean
	rm -f $(DOCNAME).info* $(DOCNAME).dvi $(DOCNAME)*.ps $(DOCNAME).pdf $(DOCNAME)*.html 

##
## texi: update magic comments in texi from docstrings in code.
##	  (developer use only!)
##
$(DOCNAME).texi: ../*/*.el 
	$(MAKE) magic
magic:
	$(EMACS) -l docstring-magic.el $(DOCNAME).texi -f texi-docstring-magic -f save-buffer






