all: web-server web-server.info dir

web-server: web-server.texi
	makeinfo --html $<

web-server.info: web-server.texi
	makeinfo $<

dir: web-server.info
	install-info --info-dir=./ $<

clean:
	rm -f *.info;
	rm -rf web-server/
