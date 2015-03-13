TARGETS=hs2html hslex2html


#Optimization and other compiler options:
#OPT=
OPT=-O
HFLAGS=

#Tools:
RM=rm -f
HMAKE=sh ../scripts/hsmake.sh

################################################################################
### Rules for compiling the programs

nothing:

all: $(TARGETS)

hs2html::
	$(HMAKE) $(OPT) $(HFLAGS) hs2html

hslex2html::
	$(HMAKE) $(OPT) $(HFLAGS) hslex2html

################################################################################
### Rules for cleaning up

clean:
	$(RM) -r $(TARGETS) hi
	find . '(' -name '*.o' -o -name '*.hi' ')' -exec $(RM) '{}' ';'
