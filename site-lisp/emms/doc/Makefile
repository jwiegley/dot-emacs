# Don't delete if make is interrupted
.PRECIOUS: %.info %.html

all: emms.info

clean:
	rm -f *.info

%.info: %.texinfo
	makeinfo --no-split $<

%.html: %.texinfo
	makeinfo --html --no-split $<
