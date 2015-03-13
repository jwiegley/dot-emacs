# Don't delete if make is interrupted
.PRECIOUS: %.info %.html

all: emms.info

%.info: %.texinfo
	makeinfo --no-split $<

%.html: %.texinfo
	makeinfo --html --no-split $<
