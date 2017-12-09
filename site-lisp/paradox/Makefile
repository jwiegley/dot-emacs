# This makefile runs the tests as Travis runs them.  Be sure to test
# locally before you push if you are under the impression that the
# patch should work.  This will cut down on the number of commits in
# the repository that, essentially, patch patches.
#
# To test Emacs 24.1, for example, use
#
#     make 24.1
#
# To test on all versions, of course, simply use
#
#     make
#
# or
#
#     make all
#

VERSIONS = 24.2 24.3 24.4 24.5 25.1

all :: $(VERSIONS)

$(VERSIONS) :: clean
	evm install emacs-$@-bin --skip || true
	evm use emacs-$@-bin
	emacs --version
	cask install
	cask exec ert-runner

clean:
	rm -rf .sx/
	cask clean-elc

install_cask:
	curl -fsSkL https://raw.github.com/cask/cask/master/go | python

install_evm:
	curl -fsSkL https://raw.github.com/rejeep/evm/master/go | bash
