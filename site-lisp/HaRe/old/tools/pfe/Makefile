TARGETS=pfeclient

### Optimization and other compiler options:
OPT=
#OPT=-O2
HFLAGS=

### Tools:
RM=rm -f
HMAKE=sh ../scripts/hsmake.sh

################################################################################
### Rules for compiling the programs

all: $(TARGETS)

pfe:: baseparser
	@sh ../scripts/updateNow.sh Now.hs
	$(HMAKE) $(OPT) $(HFLAGS) pfe -o pfe

pfeclient::
	$(HMAKE) $(OPT) $(HFLAGS) pfeclient -o pfeclient

baseparser::
	@$(MAKE) -C ../base/parse2

################################################################################
### Rules for generating HTML

hi/srclist.txt:
	$(MAKE) baseparser
	PFE_LIBS=../base/tests pfesetup cpp pfe.hs

html:: hi/srclist.txt
	-[ -d hi/html ] && cd hi/html && gunzip *.gz
	pfe htmlfiles
	cd hi/html && gzip -9 *.html

################################################################################
### Rules for cleaning up

clean:
	$(RM) -r $(TARGETS) hi
	find . '(' -name '*.o' -o -name '*.hi' ')' -exec $(RM) '{}' ';'
