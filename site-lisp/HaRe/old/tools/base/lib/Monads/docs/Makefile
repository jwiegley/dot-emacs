GHC_OPTS=-package lang -fglasgow-exts
DIRS=..

all:
	ghc ${GHC_OPTS} -i${DIRS} --make *.hs 
	 

clean: 
	-rm *.hi *.o *.hcr a.out
