VERSION=0.1
ELS=monky.el
DIST_FILES=$(ELS) Makefile monky.texi monky.info README.md monky-pkg.el.in monky-pkg.el

all: monky.elc monky.info

monky.elc: monky.el
	emacs -Q --batch -f batch-byte-compile monky.el

monky-pkg.el: monky-pkg.el.in
	sed -e s/@VERSION@/$(VERSION)/ < $< > $@

monky.info: monky.texi
	makeinfo monky.texi

update-doc: monky.info
	rm -rf /tmp/monky-gh-pages
	git clone -b gh-pages . /tmp/monky-gh-pages
	makeinfo --html --no-split --css-ref=http://ananthakumaran.github.com/monky/monky.css -o /tmp/monky-gh-pages/index.html monky.texi
	cd /tmp/monky-gh-pages && git add index.html && git commit -m "doc update" && git push origin gh-pages

dist: $(DIST_FILES)
	mkdir -p monky-$(VERSION)
	cp $(DIST_FILES) monky-$(VERSION)
	tar -cvf monky-$(VERSION).tar monky-$(VERSION)

clean:
	rm -rf monky-*.tar monky-$(VERSION) monky-pkg.el monky.info
