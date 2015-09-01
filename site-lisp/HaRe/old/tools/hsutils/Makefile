TARGETS=stripcomments layout
RM=rm -f

all:: $(TARGETS)

stripcomments::
	ghc -optl -s --make -iLexer stripcomments.hs -o stripcomments

layout::
	ghc -optl -s --make -iLexer layout.hs -o layout

clean:
	$(RM) -r $(TARGETS) hi
	find . '(' -name '*.o' -o -name '*.hi' ')' -exec $(RM) '{}' ';'

hsutils-1.2.tar.gz::
	ln -s . hsutils-1.2
	tar zchf hsutils-1.2.tar.gz hsutils-1.2/{LICENSE,README,Makefile,*.hs,Lexer/{HsLex,HsTokens,HsLexUtils,HsLayoutPre,HsLexerPass1}.hs}
	rm hsutils-1.2

html:: hi/srclist.txt
	pfe htmlfiles

hi/srclist.txt:
	pfesetup -I Lexer stripcomments.hs

WEBROOT=~/public_html
WWW=$(WEBROOT)/hsutils

upload:: hsutils-1.2.tar.gz $(WWW)
	mv hsutils-1.2.tar.gz $(WWW) && \
	cd $(WWW) && \
	ln -s . hsutils-1.2 && \
	tar zxf hsutils-1.2.tar.gz && \
	rm hsutils-1.2

$(WWW):
	[ -d $(WWW) ] || mkdir $(WWW)
