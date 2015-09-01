.PHONY: all contrib clean realclean distclean fullclean install
.PRECIOUS: %.elc

DEFS = $(shell test -f ../Makefile.defs && echo ../Makefile.defs \
	|| echo ../Makefile.defs.default)

include $(DEFS)

EL  = $(wildcard *.el)
EL_NOT_BYTE_COMPILED = htmlize-hack.el
ELC = $(patsubst %.el,%.elc,$(filter-out $(EL_NOT_BYTE_COMPILED),$(EL)))

all: contrib

contrib: $(ELC)

$(PROJECT)-build.elc: ../scripts/$(PROJECT)-build.el
	@echo $(PROJECT)-build.el is not byte-compiled

%.elc: %.el
	@$(EMACS) -q $(SITEFLAG) -batch -l ../scripts/$(PROJECT)-build.el \
	    -f batch-byte-compile $<

clean realclean distclean fullclean:
	-rm -f *.elc *~

install: $(ELC)
	install -d $(ELISPDIR)/contrib
	install -m 0644 $(EL) $(ELC) $(ELISPDIR)/contrib
