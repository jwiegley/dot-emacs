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

# Sources
BUTTONS=goal.xcf next.xcf qed.xcf restart.xcf retract.xcf undo.xcf use.xcf state.xcf context.xcf info.xcf command.xcf help.xcf find.xcf interrupt.xcf goto.xcf
WEBPIX=isabelle_transparent.xcf ProofGeneral.xcf pg-text.xcf

# Targets for html directory
WEBPIX_ONLY=
WEBPIX_TARGETS=$(WEBPIX_ONLY) ProofGeneral.jpg pg-text.gif
# Targets for doc directory
DOCPIX_TARGETS=ProofGeneral.jpg

# Junk not wanted
UNWANTED=text_general.jpg text_proof.jpg

CWD=$(shell pwd)
GIMP_DIRECTORY=$(CWD)/gimp

# Command to run gimp in batch mode.
GIMP=export GIMP_DIRECTORY=$(GIMP_DIRECTORY); gimp --no-interface --no-data  --console-messages --batch

default: all

images: all

all: buttons backgroundize-xpm webpix

dist:   all install distclean

# Edit xpm files to add a substitution background colour for
# the XEmacs toolbar background -- a hack that almost works
# (only almost because the images have anti-aliasing with
#  a different background colour, and xpm files only allow
#  one-bit alpha).
backgroundize-xpm: $(BUTTONS)
	for f in *.xpm; do sed 's/#BCBCBC"/#BCBCBC s backgroundToolBarColor"/g' $$f > $$f.new; mv $$f.new $$f; done

# NB: gimp sometimes fails with this argument, in case it is built
# without support for one of the image formats, e.g. xbm.
# (Happens with gimp from Mandrake 6.0, for example)
buttons: $(BUTTONS)
	$(GIMP) '(script-fu-proofgeneral-make-all-buttons 1)' '(gimp-quit 0)'
	$(MAKE) backgroundize-xpm
	touch buttons

webpix: $(WEBPIX)
	$(GIMP) '(script-fu-proofgeneral-save-all-pix 1)' '(gimp-quit 0)'
	touch webpix

cvsclean: clean
# For the time being we keep all this junk under CVS too, for convenience.
#	rm -f *.xpm *.xbm *.jpg gimp/pluginrc
#	rm -f *.jpg gimp/pluginrc

# Remove all the generated targets and other junk.
wellclean: clean
	rm -f *.xpm *.xbm *.jpg *.gif

distclean: clean

clean:
	rm -f buttons webpix gimp/pluginrc
	rm -f $(WEBPIX_ONLY) $(UNWANTED)

install: webpix
	cp -pf $(WEBPIX_TARGETS) ../html/images
	cp -pf $(DOCPIX_TARGETS) ../doc

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

