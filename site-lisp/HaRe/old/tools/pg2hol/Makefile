# $Id: Makefile,v 1.1 2001/05/04 18:51:20 moran Exp $

HC         = ghc
HC_LOCAL_LIB = ${HOME}/lib
BASE       = ../base
PROP       = ../property
HC_INC     = ${BASE}/parse ${BASE}/pretty ${BASE}/AST ${BASE}/SA ${BASE}/TC \
             ${BASE}/lib ${HC_LOCAL_LIB} ${PROP}/AST ${PROP}/parse/extras   \
             ${PROP}/syntax ${PROP}/command .

HC_PKG = lang concurrent util
HC_DEP = ${HC} -M
HC_INCI = ${addprefix -i,${HC_INC}}
HC_PKGI = ${addprefix -package,${HC_PKG}}
HC_LIBI = ${addprefix -l,${HC_LIBS}}
HC_XOPTS = -recomp -fwarn-incomplete-patterns -H128M -fglasgow-exts
HC_OPTS = ${$*_HC_OPTS} ${HC_XOPTS} ${HC_INCI} ${HC_PKGI}

HINT_OPTS = ${HC_OPTS}

DEP_OPTS   = ${HC_INCI}
HC_LDOPTS  = ${HC_OPTS} ${addprefix -L,${HC_INC}} ${HC_LIBI}

HAPPY      = happy
HAPPYFLAGS = # --ghc makes parser unusable for Hugs
RUNTIMEFLAGS = # +RTS -H75M
PRINTER    = lj12
ENSCRIPT   = enscript

HAPPYSRC   = ${PROP}/parse/extras/PropParser.y
MAINSRC    = Main.hs

RM         = rm -f

MAIN       = pg2hol

%.hs: %.y
	$(HAPPY) $(HAPPYFLAGS) $< --info $(RUNTIMEFLAGS) -o $(HAPPYSRC:.y=.hs)

$(MAIN): $(HAPPYSRC:.y=.hs)
	${HC} --make $(MAINSRC) -o $@ ${HC_OPTS}

develop:
	$(HINT) $(MAINSRC) ${HINT_OPTS}

tidy:
	$(RM) ${BASE}/parse/Lexer.hi

clean:
	$(RM) ${HC_OBJ} $(MAIN).aux $(MAIN).hp $(MAIN).prof core \
           $(MAIN).ps profile.* *~ .depend* $(HAPPYSRC:.y=.info) \

printsource:
	$(ENSCRIPT) -1 -d $(PRINTER) -G $(HC_SRC)

veryclean: clean
	$(RM) $(MAIN) TAGS $(HAPPYSRC:.y=.hs)

TAGS: ${HC_SRC}
	hstags ${HC_SRC}

