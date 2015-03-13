TARGETS=spfe

MYGHC=../scripts/myghc--make

#HMAKE=ghumake -batch
HMAKE=sh $(MYGHC)

HFLAGS=

### Optimization?
OPT=
#OPT=-O2

RM=rm -f

################################################################################
### Rules for compiling the programs

all: $(TARGETS)

spfe::
	cd ../property/parse2; make HMAKE="sh ../$(MYGHC)"
	$(HMAKE) $(OPT) $(HFLAGS) spfe -o spfe


################################################################################
### Rules for generating HTML

hi/srclist.txt:
	PFE_LIBS=../base/tests pfesetup noplogic cpp spfe.hs

html:: hi/srclist.txt
	-[ -d hi/html ] && cd hi/html && gunzip *.gz
	pfe htmlfiles
	cd hi/html && gzip -9 *.html

################################################################################
### Rules for cleaning up

clean:
	$(RM) -r $(TARGETS) hi
	find . '(' -name '*.o' -o -name '*.hi' ')' -exec $(RM) '{}' ';'
