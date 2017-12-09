EMACS ?= emacs
CASK = env --unset INSIDE_EMACS cask

all: depends elc

# Ignores failures, since dependences of ‘biblio’ are locally satisfied
depends:
	$(CASK) install || true
	$(CASK) update || true

elc:
	$(CASK) build

clean:
	$(CASK) clean-elc

test: clean # Must run clean to make uncover.el work
	$(CASK) exec buttercup -L . -L tests

version:
	$(CASK) exec $(EMACS) --version

screenshots:
	$(CASK) exec $(EMACS) -Q -L . -l etc/screenshots/biblio-screenshots.el --eval '(biblio-screenshots--do)'

pkg-file:
	$(CASK) pkg-file
