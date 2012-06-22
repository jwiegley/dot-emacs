BUILD = emacs -Q -L . -l $(shell pwd)/build -batch -f batch-build-environment

all:
	$(BUILD)

# Compile all subprojects that have their own Makefiles before using build.el
compile: all
	find * -maxdepth 2 -name 'Makefile' | parallel "cd {//} ; make -k"

dryrun:
	$(BUILD) dryrun
