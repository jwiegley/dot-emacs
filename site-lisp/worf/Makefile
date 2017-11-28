emacs ?= emacs

update:
	$(emacs) -batch -l targets/install-deps.el

compile:
	$(emacs) -batch -l elpa.el -l targets/compile.el

plain:
	@echo "Using $(shell which $(emacs))..."
	@echo "Version: $(shell $(emacs) --version)"
	$(emacs) -Q -l elpa.el -l targets/interactive.el README.org

clean:
	rm -f *.elc

.PHONY: plain
