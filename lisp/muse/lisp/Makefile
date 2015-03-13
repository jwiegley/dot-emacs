.PHONY: all lisp autoloads clean realclean distclean fullclean install test
.PRECIOUS: %.elc

DEFS = $(shell test -f ../Makefile.defs && echo ../Makefile.defs \
	|| echo ../Makefile.defs.default)

include $(DEFS)

EL  = $(filter-out $(PROJECT)-autoloads.el,$(wildcard *.el))
ELC = $(patsubst %.el,%.elc,$(EL))

all: lisp

lisp: autoloads $(ELC)

$(PROJECT)-build.elc: ../scripts/$(PROJECT)-build.el
	@echo $(PROJECT)-build.el is not byte-compiled

autoloads: $(PROJECT)-autoloads.el

$(PROJECT)-autoloads.el: $(EL)
	@$(EMACS) -q $(SITEFLAG) -batch -l ../scripts/$(PROJECT)-build.el \
		-f $(PROJECT)-generate-autoloads . ../contrib ../experimental

%.elc: %.el
	@$(EMACS) -q $(SITEFLAG) -batch -l ../scripts/$(PROJECT)-build.el \
		-f batch-byte-compile $<

clean distclean:
	-rm -f *.elc *~

realclean fullclean: clean
	-rm -f $(PROJECT)-autoloads.el

install: autoloads $(ELC)
	install -d $(ELISPDIR)
	install -m 0644 $(PROJECT)-autoloads.el $(EL) $(ELC) $(ELISPDIR)

test: $(ELC)
	$(EMACS) -q $(SITEFLAG) -batch -l ../scripts/$(PROJECT)-build.el \
		-f $(PROJECT)-elint-files $(EL)

# Dependencies
#
# This allows us to recompile Muse safely after an update.

muse-backlink.elc: muse-mode.elc muse-publish.elc muse.elc

muse-blosxom.elc: muse-html.elc muse-project.elc muse-publish.elc

muse-book.elc: muse-latex.elc muse-project.elc muse-publish.elc
muse-book.elc: muse-regexps.elc

muse-colors.elc: muse-mode.elc muse-regexps.elc

muse-context.elc: muse-publish.elc

muse-docbook.elc: muse-publish.elc muse-regexps.elc muse-xml-common.elc

muse-groff.elc: muse-publish.elc

muse-html.elc: muse-publish.elc muse-regexps.elc muse-xml-common.elc

muse-http.elc: muse-html.elc muse-project.elc

muse-ikiwiki.elc: muse-html.elc muse-ipc.elc muse-publish.elc muse.elc

muse-import-docbook.elc: muse-import-xml.elc

muse-import-latex.elc: muse-regexps.elc muse.elc

muse-ipc.elc: muse-publish.elc muse.elc

muse-journal.elc: muse-book.elc muse-html.elc muse-latex.elc
muse-journal.elc: muse-publish.elc

muse-latex.elc: muse-publish.elc

muse-latex2png.elc: muse-publish.elc

muse-mode.elc: muse-regexps.elc muse-project.elc

muse-poem.elc: muse-latex.elc muse-project.elc

muse-project.elc: muse-publish.elc muse.elc

muse-protocols.elc: muse-regexps.elc

muse-publish.elc: muse-regexps.elc muse.elc

muse-texinfo.elc: muse-latex.elc muse-publish.elc

muse-wiki.elc: muse-colors.elc muse-regexps.elc muse-mode.elc

muse-xml-common.elc: muse-publish.elc muse-regexps.elc

muse-xml.elc: muse-publish.elc muse-regexps.elc muse-xml-common.elc

muse.elc: muse-protocols.elc muse-regexps.elc
