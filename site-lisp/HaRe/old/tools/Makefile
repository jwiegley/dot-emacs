
#PREFIX=/usr/local
PREFIX=/home/projects/pacsoft/tools
PROGRAMATICA=$(PREFIX)/lib/Programatica
PLOVER=../Plogic/Plover

#OPT=-O2
OPT=-O
#OPT=-O -prof -auto-all

SUBDIRS=evman hs2alfa pfe pfe/Browser          # for make all
ALLSUBDIRS=$(SUBDIRS) base property hs2html    # for make clean

ADJUST=scripts/adjustscript PROGRAMATICA $(PROGRAMATICA)

#SCRIPTS=bin/pfesetup bin/cert bin/pfebrowser

#MAKEFLAGS=-no-print-directory
################################################################################

all: config
	@for dir in $(SUBDIRS) ; do $(MAKE) -C $$dir OPT="$(OPT)" ; done
	@$(MAKE) template

## Make directories holding a template structure of things to install:
template:: bin lib


install::
	rsync -aLHvC bin lib $(PREFIX)

tar::
	@$(MAKE) PREFIX=/usr/local template
	tar -czh --exclude CVS --exclude objs --exclude '*.hi' -f pfe-`date +%y%m%d`.tar.gz lib bin

bin::
	@echo Creating the bin directory
	@rm -rf bin && mkdir -p bin
	@cd bin; ln -s ../hs2alfa/apfe pfe
	@cd bin; ln -s ../pfe/pfeclient pfeclient
	@cd bin; if [ -x "../$(PLOVER)" ] ; then ln -s ../$(PLOVER) Plover ; fi
#	-[ -x hs2alfa/apfe ] && { cd bin; ln -s ../hs2alfa/apfe apfe; }
	@$(ADJUST) <pfe/pfesetup >bin/pfesetup
	@$(ADJUST) <evman/cert.sh >bin/cert
	@$(ADJUST) <pfe/Browser/pfebrowser.sh >bin/pfebrowser
	@chmod +x bin/pfesetup bin/cert bin/pfebrowser

L=lib/Programatica
C=types/certificate

lib::
	@echo Creating the lib directory
	@rm -rf lib
	@cd evman; $(MAKE) icons lib
	@mkdir -p $L/bin $L/libs $L/icons
	@ln LICENSE $L
	@cd $L/libs; ln -s ../../../base/tests/*Libraries .
#	@cd $L/libs/Monads; ln -s ../../../../base/lib/Monads/*.hs .
	@cd $L/icons; ln -s ../../../evman/icons/smiley.sad.gif .
	@cd $L/bin; ln -s ../../../pfe/Browser/pfebrowser .


################################################################################

html:: config
	$(MAKE) hi/srclist.txt
	-[ -d hi/html ] && cd hi/html && gunzip *.gz
	pfe noplogic htmlfiles
	cd hi/html && gzip -9 *.html

hi/srclist.txt:
	@$(MAKE) -C property propparser
	@$(MAKE) -C pfe baseparser
	@sh scripts/updateNow.sh pfe/Now.hs
	TARGET=apfe pfesetup +h noplogic cpp pfe/pfe.hs pfe/pfeclient.hs property/ppfe.hs hs2alfa/apfe.hs


################################################################################

config: scripts/hsmake.sh scripts/hsfudmake.sh pfe/Browser/InternetLib

scripts/hsmake.sh scripts/hsfudmake.sh pfe/Browser/InternetLib:
	./configure

unconfig:
	cd scripts && rm -f hsmake.sh hsfudmake.sh
	cd pfe/Browser && rm -f InternetLib

################################################################################

clean: unconfig
	rm -rf bin lib hi
	for dir in $(ALLSUBDIRS) ; do $(MAKE) -C $$dir clean ; done
	find . '(' -name '*.o' -o -name '*.hi' ')' -exec rm '{}' ';'
