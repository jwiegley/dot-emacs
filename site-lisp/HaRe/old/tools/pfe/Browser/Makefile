
TARGETS=pfebrowser

### Optimization and other compiler options:
#OPT=-O2
OPT=-O
#OPT=
ILIB=-package-conf InternetLib/package.conf -package internetlib -iInternetLib
#ILIB=-iInternetLib -ld InternetLib/libInternetLib.a
#ILIB=-package internetlib
HFLAGS=

### Tools:
RM=rm -f
HMAKE=sh ../../scripts/hsfudmake.sh -contrib

################################################################################
### Rules for compiling the programs

all: $(TARGETS)

pfebrowser::
	@$(MAKE) InternetLib
	@sh ../../scripts/updateNow.sh ../Now.hs
	@$(MAKE) -C ../../property/parse2
	$(HMAKE) $(OPT) $(HFLAGS) $(ILIB) $@ -o $@

InternetLib:
	@echo "You need to create a link to where InternetLib is installed:"
	@echo "   ln -s .../InternetLib InternetLib"
	@exit 1

################################################################################
### Rules for cleaning up

clean:
	rm -rf $(TARGETS)
	find . '(' -name '*.o' -o -name '*.hi' ')' -exec $(RM) '{}' ';'
