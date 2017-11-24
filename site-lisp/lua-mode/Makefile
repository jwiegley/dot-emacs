# Makefile for lua-mode

VERSION="$(shell sed -nre '/^;; Version:/ { s/^;; Version:[ \t]+//; p }' lua-mode.el)"
DISTFILE = lua-mode-$(VERSION).zip

# EMACS value may be overridden
EMACS?=emacs
EMACS_MAJOR_VERSION=$(shell $(EMACS) -batch -eval '(princ emacs-major-version)')
LUA_MODE_ELC=lua-mode.$(EMACS_MAJOR_VERSION).elc

EMACS_BATCH=$(EMACS) --batch -Q

default:
	@echo version is $(VERSION)

%.$(EMACS_MAJOR_VERSION).elc: %.elc
	mv $< $@

%.elc: %.el
	$(EMACS_BATCH) -f batch-byte-compile $<

compile: $(LUA_MODE_ELC)

dist:
	rm -f $(DISTFILE) && \
	git archive --format=zip -o $(DISTFILE) --prefix=lua-mode/ HEAD

.PHONY: test-compiled-nocask test-uncompiled-nocask test-compiled test-uncompiled
# check both regular and compiled versions
test-nocask: test-compiled-nocask test-uncompiled-nocask

test: test-compiled test-uncompiled

test-compiled-nocask: $(LUA_MODE_ELC)
	$(EMACS) -batch -l $(LUA_MODE_ELC) -l buttercup -f buttercup-run-discover

test-uncompiled-nocask:
	$(EMACS) -batch -l lua-mode.el -l buttercup -f buttercup-run-discover

test-compiled: $(LUA_MODE_ELC)
	EMACS=$(EMACS) cask exec buttercup -l $(LUA_MODE_ELC)

test-uncompiled:
	EMACS=$(EMACS) cask exec buttercup -l lua-mode.el

tryout:
	cask exec $(EMACS) -Q -l init-tryout.el test.lua

tryout-nocask:
	$(EMACS) -Q -l init-tryout.el test.lua

release:
	git fetch && \
	git diff remotes/origin/master --exit-code && \
	git tag -a -m "Release tag" rel-$(VERSION) && \
	woger lua-l lua-mode lua-mode "release $(VERSION)" "Emacs major mode for editing Lua files" release-notes-$(VERSION) http://github.com/immerrr/lua-mode/ && \
	git push origin master
	@echo 'Send update to ELPA!'
