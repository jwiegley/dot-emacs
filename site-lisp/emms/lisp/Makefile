EMACS=emacs
SITEFLAG=--no-site-file
ALLSOURCE=$(wildcard *.el)
ALLCOMPILED=$(wildcard *.elc)
SPECIAL=emms-auto.el emms-maint.el
SOURCE=$(filter-out $(SPECIAL),$(ALLSOURCE))
TARGET=$(patsubst %.el,%.elc,$(SOURCE))

.PHONY: all clean
.PRECIOUS: %.elc
all: emms-auto.el $(TARGET)

emms-auto.el: emms-auto.in $(SOURCE)
	cp emms-auto.in emms-auto.el
	-rm -f emms-auto.elc
	@$(EMACS) -q $(SITEFLAG) -batch \
		-l emms-maint.el \
		-l emms-auto.el \
		-f emms-generate-autoloads \
		$(shell pwd)/emms-auto.el .

%.elc: %.el
	@$(EMACS) -q $(SITEFLAG) -batch \
		-l emms-maint.el \
		-f batch-byte-compile $<

clean:
	-rm -f *~ *.elc emms-auto.el
