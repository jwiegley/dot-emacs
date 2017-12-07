CASK ?= cask
EMACS ?= emacs
INPUT_FILE := "test/user-input.txt"

all: test

# ecukes not used, so test only init
test: unit

unit:
	rm -f ${INPUT_FILE}
	touch ${INPUT_FILE}
	${CASK} exec ert-runner < ${INPUT_FILE}

# ecukes:
# 	${CASK} exec ecukes

install:
	${CASK} install

compile:
	${CASK} exec ${EMACS} -Q --batch -L . -f batch-byte-compile window-purpose*.el

clean: clean-elc clean-deps

clean-elc:
	rm -f *.elc

clean-deps:
	rm -rf .cask/

# make ARGS='--eval "(message \"run me like this\")"' run
# make ARGS='--batch --eval "(message \"or like this\")"' run
run:
	${CASK} exec ${EMACS} -Q -L . ${ARGS}

.PHONY: all test clean
