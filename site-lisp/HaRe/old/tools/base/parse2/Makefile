
GENERATED=Lexer/HsLex.hs Parser/HsParser.hs
GENERATOR=LexerGen/HsLexerGen

TARGETS=$(GENERATED) $(GENERATOR)

#Tools:
HMAKE=sh ../../scripts/hsmake.sh
RM=rm -f

################################################################################
### Rules for the targets:

all: $(GENERATED)
lexer: Lexer/HsLex.hs
parser: Parser/HsParser.hs

Parser/HsParser.hs: Parser/HsParser.y
	cd Parser; happy HsParser.y

Lexer/HsLex.hs: LexerSpec/*.hs Lexer/HsTokens.hs
	@$(MAKE) $(GENERATOR)
	LexerGen/HsLexerGen >Lexer/HsLex.hs

#Lexer/HsLex.hs::
#	$(HMAKE) -O -package data -O tst
#	if [ ./tst -nt Lexer/HsLex.hs ] ; then ./tst >Lexer/HsLex.hs ; fi

#./lexgen Lexer/HsLex.hs

$(GENERATOR)::
	$(HMAKE) -O -package data $(GENERATOR) -o $(GENERATOR)

################################################################################
### Rules for cleaning up

clean:
	$(RM) -r $(TARGETS)
	find . '(' -name '*.o' -o -name '*.hi' ')' -exec $(RM) '{}' ';'
