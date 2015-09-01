### See also README.html

TARGETS=tstModules tstTI

HMAKE=ghumake -batch
HFLAGS=

### Optimization?
OPT=
#OPT=-O2

RM=rm -f

################################################################################
### Rules for compiling the programs

nothing:

all: $(TARGETS)

tstTI::
	cd parse2; make
	$(HMAKE) $(OPT) $(HFLAGS) tstTI

tstModules::
	cd parse2; make
	$(HMAKE) $(OPT) $(HFLAGS) tstModules

################################################################################
### Rule for creating the cross ref info and HTML version of the base sources.
### These assume that tstModules and hs2html have already been compiled and
### installed.

xrefs:: hi/ModuleSourceFiles.txt

hi/ModuleSourceFiles.txt:: tstTI.srclist
	tstModules xrefs `cat tstTI.srclist`

tstTI.srclist:
	echo "$@ has to be created manually (for the time being)."

html: hi/modules
	hs2html all2html

hi/modules: hi/ModuleSourceFiles.txt
	hs2html modules >hi/modules

################################################################################
### Rules for cleaning up

clean:
	cd parse2; make clean
	$(RM) -r $(TARGETS) hi
	find . '(' -name '*.o' -o -name '*.hi' ')' -exec $(RM) '{}' ';'

cleanrefs:
	$(RM) -f hi/*.refs
