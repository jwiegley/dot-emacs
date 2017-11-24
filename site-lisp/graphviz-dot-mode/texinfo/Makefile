BASENAME := graphviz-dot-mode
SOURCE	:= $(BASENAME).texi
INCLUDE	:= fdl.texi gpl-2.0.texi gpl.texi

INFODIR := ~/info

TEXINFODIR := /usr/local/Cellar/texinfo/6.4/bin
TEXI2ANY := $(TEXINFODIR)/texi2any
TEXI2PDF := $(TEXINFODIR)/texi2pdf
TEXI2DVI := $(TEXINFODIR)/texi2dvi
INSTALLINFO := $(TEXINFODIR)/install-info
SMARTYPANTS := /usr/local/bin/smartypants
PANDOC := /usr/local/bin/pandoc
GZIP := /usr/bin/gzip
INSTALL := /usr/bin/install

help:
	# Options:
	# make info
	# make install
	#
	# make html
	# make pdf
	# make ps
	# make txt
	# make docbook
	# make adoc
	# make epub	# lacks index
	# make md	# lacks index
	#
	# make clean
	#
	# This Makefile uses TexInfo and Pandoc
	# Check the file locations at top of this Makefile.

info: $(BASENAME).info.gz

html: $(BASENAME).html

pdf: $(BASENAME).pdf

ps: $(BASENAME).ps

txt: $(BASENAME).txt

docbook: $(BASENAME).xml

adoc: $(BASENAME).adoc

epub: $(BASENAME).epub

md: $(BASENAME).md

$(BASENAME).info: ${SOURCE} ${INCLUDE}
	$(TEXI2ANY) --info $<

$(BASENAME).info.gz: $(BASENAME).info
	$(GZIP) $<

install: $(BASENAME).info.gz
	$(INSTALL) $< $(INFODIR)
	$(INSTALLINFO) $(INFODIR)/$< $(INFODIR)/dir

$(BASENAME).html: ${SOURCE} ${INCLUDE}
	$(TEXI2ANY) --HTML --no-split --no-headers ${SOURCE} | ${SMARTYPANTS}

$(BASENAME).pdf: ${SOURCE} ${INCLUDE} $(BASENAME).info
	$(TEXI2PDF) $<

$(BASENAME).ps: ${SOURCE} ${INCLUDE} $(BASENAME).info
	$(TEXI2DVI) --ps  $<

$(BASENAME).txt: ${SOURCE} ${INCLUDE}
	$(TEXI2ANY) --plaintext $< >$@

# texi2any --docbook handles @Xindex entries poorly. Remove them first.
$(BASENAME).xml: ${SOURCE} ${INCLUDE} $(BASENAME).info
	grep -v "^@[cfkptv]index " $< >$(BASENAME)._texi
	$(TEXI2ANY) --docbook $(BASENAME)._texi

$(BASENAME).adoc: $(BASENAME).xml
	$(PANDOC) -t asciidoc -o $@ -f docbook $<

$(BASENAME).epub: $(BASENAME).xml
	$(PANDOC) -t epub -o $@ -f docbook $<

$(BASENAME).md: $(BASENAME).xml
	$(PANDOC) -t markdown_strict -o $@ -f docbook $<

clean:
	rm *.aux *.toc *.log || true
	rm *.cp *.cps *.vr *.vrs *.fn *.fns *.ky *.kys *.pg *.pgs || true
	rm $(BASENAME).dvi $(BASENAME).ps $(BASENAME).adoc || true
	rm $(BASENAME).xml $(BASENAME).epub $(BASENAME).md || true
	rm $(BASENAME).html $(BASENAME).txt $(BASENAME).pdf || true
	rm $(BASENAME).info $(BASENAME).info.gz || true

