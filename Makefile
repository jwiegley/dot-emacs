VERSION = $(shell grep ';; Version:' tuareg.el \
	| sed 's/;; Version: *\([0-9.]*\).*/\1/')
DESCRIPTION = $(shell grep ';;; tuareg.el ---' tuareg.el \
	| sed 's/[^-]*--- *\([^.]*\).*/\1/')
REQUIREMENTS = $(shell grep ';; Package-Requires:' tuareg.el \
	| sed 's/;; Package-Requires: *\(.*\)/\1/')
DIST_NAME = tuareg-$(VERSION)
TARBALL = $(DIST_NAME).tar.gz
OPAM_DIR = packages/tuareg/tuareg.$(VERSION)

SOURCES = tuareg.el ocamldebug.el tuareg-opam.el \
  tuareg-jbuild.el
ELS = $(SOURCES) tuareg-site-file.el
ELC = $(ELS:.el=.elc)

INSTALL_FILES = $(ELS) $(ELC)
INSTALL_DIR ?= $(shell opam config var share)/emacs/site-lisp

DIST_FILES += $(ELS) Makefile README.md tuareg.install

EMACSFORMACOSX = /Applications/Emacs.app/Contents/MacOS/Emacs
AQUAMACS = $(shell test -d /Applications \
	&& find /Applications -type f | grep 'Aquamacs$$')
ifeq ($(wildcard $(EMACSFORMACOSX)),$(EMACSFORMACOSX))
EMACS ?= $(EMACSFORMACOSX)
else
ifneq ($(strip $(AQUAMACS)),)
ifeq ($(wildcard $(AQUAMACS)),$(AQUAMACS))
EMACS ?= $(AQUAMACS)
endif
endif
endif
EMACS ?= emacs

#ENABLE_SMIE = --eval '(setq tuareg-use-smie t)'
RM ?= rm -f
CP ?= cp -f
LN = ln
DIFF = diff -u -B

INSTALL_RM_R = $(RM) -r
INSTALL_MKDIR = mkdir -p
INSTALL_CP = $(CP)

all : tuareg-site-file.el

elc : $(ELC)

%.elc : %.el
	$(EMACS) --batch -L . --no-init-file -f batch-byte-compile $<
	@echo "Files byte-compiled using $(EMACS)"

install : $(INSTALL_FILES)
	$(INSTALL_MKDIR) $(INSTALL_DIR)
	$(INSTALL_CP) $(INSTALL_FILES) $(INSTALL_DIR)/
	$(POST_INSTALL_HOOK)

uninstall :
	-test -d $(INSTALL_DIR) && \
	  $(INSTALL_RM_R) $(addprefix $(INSTALL_DIR)/, $(INSTALL_FILES))

.PHONY: refresh
refresh:

check : sample.ml.test

%.test: % $(ELC) refresh
	@echo ====Indent $*====
	-$(RM) $@
	$(EMACS) --batch -q --no-site-file $(ENABLE_SMIE) \
	  --load tuareg-site-file.el $< \
	  --eval '(setq indent-tabs-mode nil)' \
	  --eval '(defun ask-user-about-lock (file opponent) nil)' \
	  --eval '(indent-region (point-min) (point-max) nil)' \
	  --eval '(indent-region (point-min) (point-max) nil)' \
	  --eval '(write-region (point-min) (point-max) "$@")'
	$(DIFF) $< $@ || true

indent-test: indent-test.ml.test

tuareg-site-file.el: $(SOURCES)
	(echo ";;; $@ --- Automatically extracted autoloads.";\
	 echo ";;; Code:";\
	 echo "(add-to-list 'load-path";\
	 echo "             (or (file-name-directory load-file-name) (car load-path)))";\
	 echo "") >$@
	$(EMACS) --batch --eval '(setq generated-autoload-file "'`pwd`'/$@")' -f batch-update-autoloads "."

dist distrib: $(TARBALL)

$(TARBALL): $(DIST_FILES)
	mkdir -p $(DIST_NAME)
	for f in $(DIST_FILES); do $(LN) $$f $(DIST_NAME); done
	echo '(define-package "tuareg" "$(VERSION)" "$(DESCRIPTION)" ' "'"'$(REQUIREMENTS))' > $(DIST_NAME)/tuareg-pkg.el
	tar acvf $@ $(DIST_NAME)
	$(RM) -r $(DIST_NAME)

opam: $(TARBALL)
	$(INSTALL_MKDIR) $(OPAM_DIR)
	$(CP) -a $(filter-out %~, $(wildcard opam/*)) $(OPAM_DIR)
	echo "archive: \"https://github.com/ocaml/tuareg/releases/download/$(VERSION)/$(TARBALL)\"" > $(OPAM_DIR)/url
	echo "checksum: \"`md5sum $(TARBALL) | cut -d ' ' -f 1`\"" \
	  >> $(OPAM_DIR)/url

clean :
	$(RM) $(ELC) "$(DIST_NAME).tar.gz" "$(DIST_NAME).tar"
	$(RM) -r tuareg.$(VERSION)

.PHONY : all elc clean install uninstall check distrib dist opam
