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

.SUFFIXES:  .texi .info .dvi .html .pdf .ps .eps .tiff .gz

.texi.info:
	$(MAKEINFO) $< 

.texi.dvi:
	$(TEXI2DVI) $<
	$(DVISELECT) -i $*.dvi -o $*.tmp1 $(TITLERANGE)
	$(DVISELECT) -i $*.dvi -o $*.tmp2 $(MAINRANGE)
	$(DVISELECT) -i $*.dvi -o $*.tmp3 $(TOC)
	$(DVICONCAT) -o $*.dvi $*.tmp1 $*.tmp3 $*.tmp2 
	rm -f $*.tmp1 $*.tmp2 $*.tmp3

.tiff.eps:
	tiff2ps -e -w 3.48 -h 5 $*.tiff > $*.eps

.texi.pdf:
	$(TEXI2PDF) $< 

.dvi.ps:
	$(DVI2PS) $< -o $*.ps

.texi.html:	
	$(TEXI2HTML) -expandinfo -split_chapter $< 

default: doc

ProofGeneral.txt:
	echo > ProofGeneral.txt

ProofGeneral.eps:
	gunzip -c ProofGeneral.eps.gz > ProofGeneral.eps

%.gz : %
	gzip -f -9 $*

## 
## doc : build info and dvi files from $(DOCNAME).texi
##
doc:	dvi info

## 
## all : build all documentation targets
##
all:    dvi ps html info pdf

##
## dist: build distribution targets
##
dist:   html psz

dvi:    ProofGeneral.eps $(DOCNAME).dvi
ps:	dvi $(DOCNAME).ps
psz:	ps $(DOCNAME).ps.gz
pdf:    $(DOCNAME).pdf
html:   $(DOCNAME).html
info:   ProofGeneral.txt $(DOCNAME).info

# NB: for info, could make localdir automatically from
# START-INFO-DIR-ENTRY / END-INFO-DIR-ENTRY.
# Does some utility do this?

##
## clean: Remove subsidiary documentation files
##
clean:
	rm -f ProofGeneral.txt ProofGeneral.eps
	rm -f $(DOCNAME).{cp,fn,vr,tp,ky,pg} 
	rm -f $(DOCNAME).{fns,vrs,cps,aux,log,toc,kys,cp0}
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






