ESH2TEX="$(realpath ../bin/esh2tex)" --debug-on-error
ESH2HTML="$(realpath ../bin/esh2html)" --debug-on-error
XELATEX=rubber -m xelatex
LUALATEX=lualatex

all: clean cli minimal misc tricky pv standalone lua reference strip

clean:
	git clean -Xfd
	rm -rf outputs
	mkdir -p outputs
	cd outputs; ${ESH2HTML} --write-preamble

cli:
	mkdir -p cli
	cd cli; ${ESH2TEX} --init
	make -C cli
	cp cli/main.pdf outputs/cli.pdf

minimal:
	${ESH2TEX} minimal.tex
	${XELATEX} --jobname=minimal minimal.esh.tex
	${ESH2HTML} minimal.html
	mv minimal.esh.html minimal.esh.tex minimal.pdf outputs/

misc:
	${ESH2TEX} misc.tex
	${XELATEX} --jobname=misc misc.esh.tex
	${ESH2HTML} misc.html
	mv misc.esh.html misc.esh.tex misc.pdf outputs/

tricky:
	cd tricky; ${ESH2TEX} tricky.tex
	cd tricky; ${XELATEX} --jobname=tricky tricky.esh.tex
	cd tricky; ${ESH2HTML} tricky.html
	mv tricky/tricky.pdf tricky/tricky.esh.tex tricky/tricky.esh.html outputs/

pv:
	${ESH2TEX} --write-preamble
	${ESH2TEX} --precompute-verbs-map pv.tex
	${XELATEX} pv-incomplete.tex
	${XELATEX} pv.tex
	mv pv.esh-pv.tex pv.pdf pv-incomplete.pdf outputs/

standalone:
	${ESH2TEX} --write-preamble
	${ESH2TEX} --standalone standalone.py
	${XELATEX} standalone.tex
	${ESH2HTML} --standalone standalone.py
	mv standalone.py.esh.html standalone.py.esh.tex standalone.pdf outputs/

lua:
	cd lua; ${ESH2TEX} lualatex.tex
	cd lua; ${LUALATEX} --jobname=lualatex lualatex.esh.tex
	mv lua/lualatex.pdf lua/lualatex.esh.tex ./outputs/

reference:
	make -C ../example/ reference html
	cp ../example/example.pdf ../example/example.esh.tex ../example/example.esh.html outputs/

strip:
	cd outputs/; (for f in *.pdf; do pdf2ps "$$f"; done)
	cd outputs/; (for f in *.ps; do sed --in-place -e '/^%%CreationDate: .*/d' "$$f"; done)
	rm outputs/*.pdf

.PHONY: all clean cli lua minimal misc tricky standalone reference
