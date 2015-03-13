.PHONY: all examples clean realclean distclean fullclean
.PRECIOUS: %.html %.pdf %.info

DEFS = $(shell test -f ../Makefile.defs && echo ../Makefile.defs \
	|| echo ../Makefile.defs.default)

include $(DEFS)

EXAMPLES = QuickStart.html QuickStart.pdf QuickStart.info

all: examples

examples: $(EXAMPLES)

%.html: %.muse
	@echo Generating HTML for $<...
	EMACS=$(EMACS) SITEFLAG=$(SITEFLAG) ../scripts/publish html $<

%.pdf: %.muse
	@echo Generating PDF for $< ...
	EMACS=$(EMACS) SITEFLAG=$(SITEFLAG) ../scripts/publish pdf $<

%.info: %.muse
	@echo Generating Info for $< ...
	EMACS=$(EMACS) SITEFLAG=$(SITEFLAG) ../scripts/publish info $<

clean:
	rm -f missfont.log QuickStart.texi *~

realclean distclean fullclean: clean
	rm -f $(EXAMPLES)
	rm -f QuickStart.aux QuickStart.log QuickStart.out QuickStart.tex
	rm -f QuickStart.cp QuickStart.fn QuickStart.ky QuickStart.pg
	rm -f QuickStart.tp QuickStart.vr
