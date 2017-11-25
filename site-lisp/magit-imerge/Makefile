
-include config.mk

DASH_DIR ?= /dev/null
WITH_EDITOR_DIR ?= /dev/null
MAGIT_DIR ?= /dev/null

LOAD_PATH = -L $(DASH_DIR) -L $(WITH_EDITOR_DIR) -L $(MAGIT_DIR)
BATCH = emacs -Q --batch $(LOAD_PATH)

all: magit-imerge.elc magit-imerge-autoloads.el

.PHONY: test
test: magit-imerge.elc
	@$(BATCH) -L . -l magit-imerge-tests.el \
	--eval "(ert-run-tests-batch-and-exit '(not (tag interactive)))"

.PHONY: clean
clean:
	$(RM) *.elc magit-imerge-autoloads.el

%.elc: %.el
	@$(BATCH) -f batch-byte-compile $<

%-autoloads.el: %.el
	@$(BATCH) --eval \
	"(let ((make-backup-files nil)) \
	  (update-file-autoloads \"$(CURDIR)/$<\" t \"$(CURDIR)/$@\"))"
