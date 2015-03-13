TARGETS=apfe tstHs2Alfa tstProp2Alfa

### Optimization and other compiler options:
#OPT=
OPT=-O
HFLAGS=

#Tools:
RM=rm -f
#HMAKE=sh ../scripts/hsfudmake.sh
HMAKE=sh ../scripts/hsmake.sh

################################################################################
### Rules for compiling the programs

apfe::
	@$(MAKE) -s AlfaSource
	@sh ../scripts/updateNow.sh ../pfe/Now.hs
	@$(MAKE) -C ../property propparser
	TARGET=$@ $(HMAKE) $(OPT) $(HFLAGS) $@ -o $@

all:: $(TARGETS)

tstHs2Alfa::
	@$(MAKE) -C ../pfe baseparser
	TARGET=$@ $(HMAKE) $(OPT) $(HFLAGS) $@ -o $@

tstProp2Alfa::
	@$(MAKE) -C ../property propparser
	TARGET=$@ $(HMAKE) $(OPT) $(HFLAGS) $@ -o $@


AlfaSource:
	@echo "You need to unpack alfaforpfe.tar.gz first."
	@echo "Get it from http://www.cse.ogi.edu/~hallgren/Programatica/download/"
	@exit 1

################################################################################
### Rules for generating HTML

hi/srclist.txt:
	PFE_LIBS=../base/tests pfesetup hs2alfa.hs

html:: hi/srclist.txt
	pfe htmlfiles

################################################################################
### Rules for cleaning up

clean:
	$(RM) -r $(TARGETS) hi
	find . '(' -name '*.o' -o -name '*.hi' ')' -exec $(RM) '{}' ';'
