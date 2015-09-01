GHC_OPTS=-package lang -fglasgow-exts # -O2 -prof -auto-all 

all:
	-mkdir GHC_files
	ghc ${GHC_OPTS} --make *.hs -hidir GHC_files -odir GHC_files
	 

clean: 
	-rm -r GHC_files
