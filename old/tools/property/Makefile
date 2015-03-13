TARGETS=ppfe

### Optimization and other compiler options:
#OPT=
#OPT=-O2
OPT=-O
HFLAGS=

### Tools:
RM=rm -f
HMAKE=sh ../scripts/hsmake.sh

################################################################################
### Rules for compiling the programs

all: $(TARGETS)

ppfe:: propparser
	@sh ../scripts/updateNow.sh ../pfe/Now.hs
	$(HMAKE) $(OPT) $(HFLAGS) ppfe -o ppfe

propparser::
	@$(MAKE) -C parse2

################################################################################
### Rules for generating HTML (using previously installed pfe)

hi/srclist.txt:
	@$(MAKE) propparser
	PFE_LIBS=../base/tests pfesetup noplogic cpp ppfe.hs

html:: hi/srclist.txt
	-[ -d hi/html ] && cd hi/html && gunzip *.gz
	pfe noplogic htmlfiles
	cd hi/html && gzip -9 *.html

################################################################################
### Rules for cleaning up

clean:
	@$(MAKE) -C parse2 clean
	$(RM) -r $(TARGETS) hi
	find . '(' -name '*.o' -o -name '*.hi' ')' -exec $(RM) '{}' ';'
