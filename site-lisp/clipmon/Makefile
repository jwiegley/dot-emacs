
# makefile for emacs .tar packages - partially working
# switch to cask, eventually


# name of package
PACKAGE = clipmon

# any extra files or folders for the .tar file
CONTENTS := clipmon.wav

# ------------------------------------------------------------------------------

EMACS = emacs
SOURCE = ${PACKAGE}.el
TEST = test/${PACKAGE}-test.el
MAKE-README = script/make-readme.el

# parse package metadata
# currently handles only one keyword, and no dependencies
# eg need :keywords '("speed" "convenience"))
#. better to call an elisp fn to parse this stuff and make -pkg file,
# or use cask.
# note: grep -P for perl regexp, -o to just output match
# ?<= is the look-behind operator - match is not included in output
DESCRIPTION  != grep ";;; ${SOURCE} --- " ${SOURCE} | grep -Po "(?<= --- ).+"
VERSION      != grep ";; Version:"        ${SOURCE} | grep -Po [0-9]+
HOMEPAGE     != grep ";; URL:"            ${SOURCE} | grep -Po "(?<=;; URL: ).+"
KEYWORDS     != grep ";; Keywords:"       ${SOURCE} | grep -Po "(?<=;; Keywords: ).+"
KEYWORDS := "\"${KEYWORDS}\""
DEPENDENCIES = "nil"

# for tar
PKG = ${PACKAGE}-pkg.el
PACKAGE_DIR := ${PACKAGE}-${VERSION}
PACKAGE_TAR := ${PACKAGE}-${VERSION}.tar
TAR_DIR := tar

# ------------------------------------------------------------------------------


help:
	@echo ""
	@echo "make info       show package info extracted from <package>.el"
	@echo "make test       run unit tests in <package>-test.el file"
	@echo "make all        clean, compile, pkg, readme, tar"
	@echo "make compile    compile .el files to .elc"
	@echo "make pkg        make <package>-pkg.el file for multi-file packages"
	@echo "make readme     make README.md from <package>.el commentary section"
	@echo "make tar        make <package>-<version>.tar package file"
	@echo "make clean      delete readme, -pkg, .elc, .tar"
	@echo "make clean-elc  delete .elc"
	@echo ""


info:
	@echo "Package:       ${PACKAGE}"
	@echo "Description:   ${DESCRIPTION}"
	@echo "Homepage:      ${HOMEPAGE}"
	@echo "Version:       ${VERSION}"
	@echo "Keywords:      ${KEYWORDS}"
	@echo "Dependencies:  ${DEPENDENCIES}"
	@echo ""


# compile to check for bugs, and build tarfile for install test
test: compile tar
	@echo ""
	@emacs -nw --version
	@echo ""
	${EMACS} -Q -batch -L . -l ${TEST} -f ert-run-tests-batch-and-exit


all: info clean compile test pkg readme tar


# make sure everything compiles, then remove .elc files
# need -L . so test can (require 'clipmon)
compile:
	${EMACS} -Q --batch -L . -f batch-byte-compile clipmon.el test/clipmon-test.el
	rm -f *.elc test/*.elc


pkg:
	@echo "(define-package \"${PACKAGE}\" \"${VERSION}\"" > ${PKG}
	@echo "  \"${DESCRIPTION}\""        >> ${PKG}
	@echo "  ${DEPENDENCIES}"           >> ${PKG}
	@echo "  :url \"${HOMEPAGE}\""      >> ${PKG}
	@echo "  :keywords '(${KEYWORDS}))" >> ${PKG}
	cat ${PKG}

# cask is asynchronous though
# pkg0:
# 	@echo "Running cask - hit Enter when done..."
# 	${CASK} pkg-file
# 	read
# 	cat ${PKG}


# generate a readme file from the commentary in the source file.
# emacs currently generating dos line endings - fix that.
# had to comment out dos2unix as travis build system didn't seem to have access to it. 
readme:
	rm -f README.md
	${EMACS} --script ${MAKE-README} <${SOURCE} >README.md
	# dos2unix README.md
	attrib +r README.md
	head -5 README.md
	tail -9 README.md


# melpa does this automatically
tar: pkg
	rm -rf ${PACKAGE_DIR}
	mkdir ${PACKAGE_DIR}
	cp ${SOURCE} ${PACKAGE_DIR}
	cp ${PKG} ${PACKAGE_DIR}
	cp -r ${CONTENTS} ${PACKAGE_DIR}
	tar -cvf ${PACKAGE_TAR} ${PACKAGE_DIR}
	rm -rf ${PACKAGE_DIR}
	tar -tvf ${PACKAGE_TAR}
	mkdir -p ${TAR_DIR}
	mv ${PACKAGE_TAR} ${TAR_DIR}
	ls -l ${TAR_DIR}


clean:
	rm -f *.elc
	rm -f ${PKG}
	rm -f ${PACKAGE_TAR}
	rm -rdf ${PACKAGE_DIR}


clean-elc:
	rm -f *.elc


.PHONY: help info test all compile pkg readme tar clean clean-elc


# end
