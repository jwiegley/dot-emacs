all: Description.dvi Description.pdf Description.ps
Description.dvi: Modules.tex NamesEntities.tex CheckModules.tex Relations.tex ModSysAST.tex ModSysSem.tex related_work.tex abstract.tex conclusion.tex intro.tex Description.bbl pphs.sty
	latex Description
Description.pdf: Modules.tex NamesEntities.tex CheckModules.tex Relations.tex ModSysAST.tex ModSysSem.tex related_work.tex abstract.tex conclusion.tex intro.tex Description.bbl pphs.sty
	pdflatex Description
Description.ps:  Description.dvi
	dvips -t letter Description.dvi -o Description.ps
Description.bbl: Description.tex Description.bib
	latex Description
	bibtex Description
Modules.tex: ../Modules.lhs tmp
	./Hack ../Modules.lhs > Modules.tex
NamesEntities.tex: ../NamesEntities.lhs tmp
	./Hack ../NamesEntities.lhs > NamesEntities.tex
CheckModules.tex: ../CheckModules.lhs tmp
	./Hack ../CheckModules.lhs > CheckModules.tex
Relations.tex: ../Relations.lhs tmp
	./Hack ../Relations.lhs > Relations.tex
ModSysAST.tex: ../ModSysAST.lhs tmp
	./Hack ../ModSysAST.lhs > ModSysAST.tex
ModSysSem.tex: ../ModSysSem.lhs tmp
	./Hack ../ModSysSem.lhs > ModSysSem.tex
tmp:
	mkdir tmp
clean:
	-rm Description.dvi Description.pdf Description.ps
	-rm tmp/*
	-rm *.log *.aux *.blg
