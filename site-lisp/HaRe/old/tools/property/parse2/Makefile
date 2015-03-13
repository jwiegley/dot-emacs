TARGETS=Parser/PropParser.hs

RM=rm -f

all: $(TARGETS)
	@$(MAKE) -C ../../base/parse2 lexer

Parser/PropParser.hs: Parser/PropParser.y
	cd Parser; happy PropParser.y

clean:
	$(RM) -f $(TARGETS)
