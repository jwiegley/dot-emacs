all: build

html := dist/index.html



install:
	emacs --batch --eval "(package-install-file \"org-wiki.el\")" --kill

# Rules to build documentation 

html: $(html)

$(html):
	emacs README.org --batch -q -f org-html-export-to-html --kill
	mv README.html index.html
	cp index.html dist/index.html

html-open: $(html) 
	firefox dist/index.html

html-clean:
	rm -rf $(html)

html-redo:
	rm  -rf $(html)
	emacs README.org --batch  -q -f org-html-export-to-html --kill
	mv README.html index.html
	cp index.html dist/index.html	

html-dist: html-redo
	cd dist && git add index.html
	mkdir -p dist/wiki
	cp -r -v sandbox/wiki/* dist/wiki
	cd dist && git add wiki
	cd dist && git commit -a -m "update html doc"
	cd dist && git push

view-github:
	firefox https://caiorss.github.io/org-wiki

view-wiki-github:
	firefox https://caiorss.github.io/org-wiki/wiki/index.html

build:
	emacs -l ~/.emacs.d/init.el --batch -f batch-byte-compile org-wiki.el 


clean:
	rm -rf *.elc 

# Sandbox commands

sandbox-run:
	@echo "Running sandbox"
	cd ./sandbox && ./sandbox.sh run

sandbox-reload:
	@echo "Cleaning sandbox"
	rm -rf ./sandbox/elpa	
	@echo "Running sandbox"
	cd ./sandbox && ./sandbox.sh run

sandbox-clean:
	@echo "Cleaning sandbox"
	rm -rf ./sandbox/elpa
