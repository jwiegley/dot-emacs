##
## Makefile for Proof General images directory.
## 
## Author:   David Aspinall <da@dcs.ed.ac.uk>
##
## Developer use only, not part of distribution.
##
## $Id$
##
##  make buttons   make *.xpm, *.xbm from gimp xcf files
##  make webpix    make *.jpg from gimp xcf files
##  make install   copy *.jpg to ../html directory
##  make clean	   remove dummy targets
##  make cvsclean  remove non-cvs files
##
##  make dist	   ready for distribution
##		   (make buttons, move jpegs to html)
## 
###########################################################################

BUTTONS=goal.xcf next.xcf qed.xcf restart.xcf retract.xcf undo.xcf use.xcf
WEBPIX=ProofGeneral.xcf text_general.xcf text_proof.xcf
WEBPIX_ONLY=text_general.jpg text_proof.jpg
WEBPIX_TARGETS=$(WEBPIX_ONLY) ProofGeneral.jpg

CWD=$(shell pwd)
GIMP_DIRECTORY=$(CWD)/gimp

# Command to run gimp in batch mode.
GIMP=export GIMP_DIRECTORY=$(GIMP_DIRECTORY); gimp --no-interface --no-data  --console-messages --batch

default: all

all: buttons webpix

dist:   all install clean
	rm -f $(WEBPIX_ONLY)

buttons: $(BUTTONS)
	$(GIMP) '(script-fu-proofgeneral-make-all-buttons 1)' '(gimp-quit 0)'
	touch buttons

webpix: $(WEBPIX)
	$(GIMP) '(script-fu-proofgeneral-save-all-jpegs 1)' '(gimp-quit 0)'
	touch webpix

cvsclean: clean
# For the time being we keep all this junk under CVS too, for convenience.
#	rm -f *.xpm *.xbm *.jpg gimp/pluginrc
#	rm -f *.jpg gimp/pluginrc

# Remove all the generated targets and other junk.
wellclean: clean
	rm -f *.xpm *.xbm *.jpg *.gif 

clean:
	rm -f buttons webpix gimp/pluginrc

install: webpix
	cp -pf $(WEBPIX_TARGETS) ../html
##
## Batch mode is a bit broken on The Gimp at the moment (v 1.0)
## For script fu, at least, it seems tricky to pass arguments to
## scripts.
## With '1' as first argument to indicate "non-interactive", things
## don't work.  With '0', we get popup menus and args are ignored!

# NB: .xbm used as target, but also generates .xpm's.
#%.xbm: %.xcf
#	$(GIMP) '(script-fu-proofgeneral-make-buttons "$(CWD)/$*")' '(gimp-quit 0)'

#%.jpg: %.xcf
#	$(GIMP) '(script-fu-proofgeneral-save-jpg 0 "$(CWD)/$*")' '(gimp-quit 0)'
#	cp -pf $*.jpg ../html

