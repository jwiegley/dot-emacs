.PHONY: clean install build test

clean:
	rm -f *.elc
	rm -rf .cask/

install: .cask/
.cask/:
	cask --verbose install

build: .cask/
	cask build 2>&1 | tee build.log

test: test-build test-tag test-ert

# make sure the build errors if the package-version isn't up-to-date
test-tag:
	grep "Package-Version: $(shell git describe --tags | rev | cut -d- -f3- | rev)" magithub.el

# make sure there were no compile errors/warnings
test-build: build
	! grep -oe '.*:\(Error\|Warning\):.*' build.log

# run ERT tests
test-ert:
	cask exec ert-runner

setup-CI:
	export PATH="$(HOME)/bin:$(PATH)"
	wget 'https://raw.githubusercontent.com/flycheck/emacs-travis/master/emacs-travis.mk'
	make -f emacs-travis.mk install_emacs
	make -f emacs-travis.mk install_cask
	emacs --version
	cask exec emacs --version
