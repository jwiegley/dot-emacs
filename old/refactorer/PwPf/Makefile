top			= .
lhsModules	= $(shell find $(top) -name "*.lhs")
hsModules	= GlobalPW.hs PWCore.hs Pointfree.hs PwPfConversion.hs ../RefacPwPf.hs
#$(shell find $(top) -name "*.hs")
#Core.hs Pointfree.hs Conversion.hs PCF.hs BNL.hs Common.hs

all: $(top)/docs/index.html 

$(top)/docs/index.html : docdir $(hsModules)
	haddock -h -o docs/ $(hsModules)

docdir: 
	mkdir -p $(top)/docs

clean:
	rm -f *~ *.log *.aux *.toc *.bak *.out *.bbl *.blg

cleanall : clean
	rm -f $(top)/docs/*
