##
## Makefile for Proof General.
## 
## Author:  David Aspinall <David.Aspinall@ed.ac.uk>
##
##  make		- do "compile" and "scripts" targets
##  make compile	- make .elc's in a single session
##  make all		- make .elc's in separate sessions
##  make scripts	- edit paths to bash/perl in scripts
##  make install	- install into system directories
##
## $Id$
## 
###########################################################################

# Set this to "emacs" or "xemacs" according to your version of Emacs.
# NB: this is also used to set default install path names below.
EMACS=xemacs

# We default to /usr rather than /usr/local because installs of
# desktop and doc files under /usr/local are unlikely to work with
# rest of the system.  If that's no good for you, edit the paths
# individually before the install section.
PREFIX=/usr

PWD=$(shell pwd)

ELISP_DIRS = generic lego coq isa isar plastic demoisa hol98 phox twelf acl2 mmm

BATCHEMACS=${EMACS} -batch -q -no-site-file

BASH_SCRIPTS = isa/interface isar/interface bin/proofgeneral
PERL_SCRIPTS = lego/legotags coq/coqtags
BIN_SCRIPTS = bin/proofgeneral
PG_SCRIPTS = bin/proofgeneral

# FIXME: would rather set load path in Elisp,
# but seems tricky to do only during compilation.
# Another idea: put a function in proof-site to
# output the compile-time load path and
# ELISP_DIRS so these are set just in that one
# place.
BYTECOMP = $(BATCHEMACS) -eval '(setq load-path (append (mapcar (lambda (d) (concat "${PWD}/" (symbol-name d))) (quote (${ELISP_DIRS}))) load-path))' -f batch-byte-compile
EL=$(shell for f in $(ELISP_DIRS); do ls $$f/*.el; done)
ELC=$(EL:.el=.elc)

# Some parts of code were not compile safe, because of macros
# being expanded too early (e.g. proof-defshortcut, easy-menu-define)
# This should be fixed for 3.5, although careful testing is required.
BROKENELC=

.SUFFIXES:	.el .elc

default: all

## 
## compile : byte compile files in working directory:
##           Clearout old .elc's and re-compile in a
##           single Emacs process.  This is faster than "make elc",
##	     but can have artefacts because of context between
##	     compiles.
##
compile: .byte-compile
	lastemacs=`cat .byte-compile`; if [ "$$lastemacs" != "$(EMACS)" ]; then rm -f .byte-compile; make .byte-compile; fi


.byte-compile: $(EL) x-symbol/lisp/*.el
	@echo "*************************************************"
	@echo " Byte compiling..."
	@echo "*************************************************"
	rm -f $(ELC) 
## ignore errors for now: some files still have probs [x-symbol induced]
	-$(BYTECOMP) $(EL)
	rm -f $(BROKENELC)
	@echo " Byte compiling X-Symbol..."
	(cd x-symbol/lisp; rm -f *.elc; $(MAKE))
	echo $(EMACS) > $(@)
	@echo "*************************************************"
	@echo " Finished."
	@echo "*************************************************"


##
## Make .elc's individually.  For testing only: it's a nuisance to
## set compiling context properly in each .el file.
##

.el.elc:
	$(BYTECOMP) $*.el
	rm -f $(BROKENELC)

elc:	$(ELC)


##
## Default targets
##

default: compile scripts

all:	compile scripts


##
## Remove generated targets
##
clean:	cleanpgscripts
	rm -f $(ELC) *~ */*~ .\#* */.\#* .byte-compile
	(cd doc; $(MAKE) clean)
	(cd x-symbol/lisp; $(MAKE) distclean)

##
## Install files 
##
DESKTOP_PREFIX=${PREFIX}
ELISP=${PREFIX}/share/${EMACS}/site-lisp/ProofGeneral
BINDIR=${PREFIX}/bin
DESKTOP=${PREFIX}/share
DOCDIR=${PREFIX}/share/doc/ProofGeneral

install: install-desktop install-elisp install-bin

install-desktop:
	mkdir -p ${DESKTOP}/icons/hicolor/16x16
	cp etc/desktop/icons/16x16/proofgeneral.png ${DESKTOP}/icons/hicolor/16x16
	mkdir -p ${DESKTOP}/icons/hicolor/32x32
	cp etc/desktop/icons/32x32/proofgeneral.png ${DESKTOP}/icons/hicolor/32x32
	mkdir -p ${DESKTOP}/icons/hicolor/48x48
	cp etc/desktop/icons/48x48/proofgeneral.png ${DESKTOP}/icons/hicolor/48x48
	mkdir -p ${DESKTOP}/pixmaps
	cp etc/desktop/icons/48x48/proofgeneral.png ${DESKTOP}/pixmaps
	mkdir -p ${DESKTOP}/applications
	cp etc/desktop/proofgeneral.desktop ${DESKTOP}/applications
	mkdir -p ${DESKTOP}/mime-info
	cp etc/desktop/mime-info/proofgeneral.mime ${DESKTOP}/mime-info
	cp etc/desktop/mime-info/proofgeneral.keys ${DESKTOP}/mime-info

# NB: .el files are not strictly necessary, but we package/install them
# for the time being to help with debugging.
install-elisp: compile
	mkdir -p ${ELISP}
	for f in ${ELISP_DIRS}; do mkdir -p ${ELISP}/$$f; done
	for f in ${ELISP_DIRS}; do cp -pf $$f/*.el ${ELISP}/$$f; done
	for f in ${ELISP_DIRS}; do cp -pf $$f/*.elc ${ELISP}/$$f; done

install-bin: scripts
	mkdir -p ${BINDIR}
	cp -pf ${BIN_SCRIPTS} ${BINDIR}

# FIXME: add install-doc to install info/man pages


##
## scripts: try to patch bash and perl scripts with correct paths
##
scripts: bashscripts perlscripts pgscripts

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

pgscripts:
	@(pghome=${ELISP}; \
	 for i in $(PG_SCRIPTS); do \
	   sed "s|PGHOME=.*$$|PGHOME=$$pghome|" < $$i > .tmp \
	   && cat .tmp > $$i; \
	 done; \
	 rm -f .tmp)

# Set PGHOME path in scripts back to default location.
cleanpgscripts:
	make pgscripts ELISP=..


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




