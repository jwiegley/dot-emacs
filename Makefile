## -*- mode: makefile-gmake -*-

EMACS	    = emacs
EMACS_BATCH = $(EMACS) -Q -batch

TARGET = $(patsubst %.el,%.elc,init.el)

DIRS    = lisp
SUBDIRS = $(shell find $(DIRS) -maxdepth 2	\
		       ! -name .git		\
		       ! -name doc		\
		       ! -name test		\
		       ! -name tests		\
		       ! -name obsolete		\
		       -type d -print)

MY_LOADPATH = -L . $(patsubst %,-L %, $(SUBDIRS))
BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

.PHONY: test build clean

# Main rule
all: init.elc

# Generate lisp and compile it
init.el: init.org
	@$(BATCH_LOAD) -L $(HOME)/.emacs.d/lisp/org-mode/lisp \
		--eval "(require 'org)" \
		--eval "(org-babel-load-file \"init.org\")"
	@chmod ugo-w $@

compile:
	@BATCH_LOAD="$(BATCH_LOAD)" ./compile-all $(DIRS)
	@echo All Emacs Lisp files have been compiled.

init.elc: init.el

%.elc: %.el
	@echo Compiling file $<
	@$(BATCH_LOAD) -f batch-byte-compile $<

speed:
	time emacs -L . -l init --batch --eval "(message \"Hello, world\!\")"

slow:
	time emacs -L . -l init --debug-init --batch --eval "(message \"Hello, world\!\")"

open:
	open $$(dirname $$(which emacs))/../Applications/Emacs.app

# This rule output configured packages compared to installed packages. Note
# that some must be filtered out (usually because they are builtins) or
# renamed (often because the package name does not match the installed name)
# in order to match.
compare:
	@comm -3 <(perl -ne 'print $$1, "\n" if /^ *\(use-package ([-+A-Za-z0-9_]+)/;' ~/.emacs.d/init.org \
	            | sed -e 's/^word-count$$/word-count-mode/' \
	            | sed -e 's/^ztree-diff$$/ztree/' \
	            | sed -e 's/^ob-verb$$/verb/' \
	            | sed -e 's/^proof-site$$/proof-general/' \
	            | sed -e 's/^hl-line+$$/hl-line-plus/' \
	            | sed -e 's/^dired+$$/dired-plus/' \
	            | sed -e 's/^bookmark+$$/bookmark-plus/' \
	            | sed -e 's/^latex$$/auctex/' \
	            | sed -e 's/^smartparens-config$$/smartparens/' \
	            | sed -e 's/^citre-config$$/citre/' \
	            | sort | uniq \
	            | egrep -v '^bahai-calendar$$' \
	            | egrep -v '^consult-dir-vertico$$' \
	            | egrep -v '^emacs$$' \
	            | egrep -v '^gist$$' \
	            | egrep -v '^org-babel$$' \
	            | egrep -v '^po-mode$$' \
	            | egrep -v '^selected-mc$$' \
	            | egrep -v '^c-includes$$' \
	            | egrep -v '^chess-ics$$' \
	            | egrep -v '^cl-info$$' \
	            | egrep -v '^coq-lookup$$' \
	            | egrep -v '^ediff-keep$$' \
	            | egrep -v '^edit-rectangle$$' \
	            | egrep -v '^erc-alert$$' \
	            | egrep -v '^erc-macros$$' \
	            | egrep -v '^esh-toggle$$' \
	            | egrep -v '^haskell-edit$$' \
	            | egrep -v '^inventory$$' \
	            | egrep -v '^my-gnus-score$$' \
	            | egrep -v '^nix-update$$' \
	            | egrep -v '^org-agenda$$' \
	            | egrep -v '^org-attach$$' \
	            | egrep -v '^org-attach-git$$' \
	            | egrep -v '^org-crypt$$' \
	            | egrep -v '^org-devonthink$$' \
	            | egrep -v '^org-habit$$' \
	            | egrep -v '^org-protocol$$' \
	            | egrep -v '^org-smart-capture$$' \
	            | egrep -v '^ox-md$$' \
	            | egrep -v '^paredit-ext$$' \
	            | egrep -v '^personal$$' \
	            | egrep -v '^prover$$' \
	            | egrep -v '^(url(-(cache|irc))?)$$' \
	            | egrep -v '^vertico-(directory|multiform|quick|repeat)$$' \
	            | egrep -v '^abbrev$$' \
	            | egrep -v '^align$$' \
	            | egrep -v '^ansi-color$$' \
	            | egrep -v '^auth-source-pass$$' \
	            | egrep -v '^autorevert$$' \
	            | egrep -v '^bookmark$$' \
	            | egrep -v '^browse-url$$' \
	            | egrep -v '^cal-dst$$' \
	            | egrep -v '^calc$$' \
	            | egrep -v '^calendar$$' \
	            | egrep -v '^cc-mode$$' \
	            | egrep -v '^compile$$' \
	            | egrep -v '^css-mode$$' \
	            | egrep -v '^cus-edit$$' \
	            | egrep -v '^dabbrev$$' \
	            | egrep -v '^diff-mode$$' \
	            | egrep -v '^dired$$' \
	            | egrep -v '^dired-x$$' \
	            | egrep -v '^doc-view$$' \
	            | egrep -v '^ediff$$' \
	            | egrep -v '^electric$$' \
	            | egrep -v '^elint$$' \
	            | egrep -v '^elisp-mode$$' \
	            | egrep -v '^em-unix$$' \
	            | egrep -v '^epa$$' \
	            | egrep -v '^erc$$' \
	            | egrep -v '^ert$$' \
	            | egrep -v '^eshell$$' \
	            | egrep -v '^etags$$' \
	            | egrep -v '^ffap$$' \
	            | egrep -v '^find-dired$$' \
	            | egrep -v '^flymake$$' \
	            | egrep -v '^flyspell$$' \
	            | egrep -v '^font-lock$$' \
	            | egrep -v '^gnus-agent$$' \
	            | egrep -v '^gnus-art$$' \
	            | egrep -v '^gnus-demon$$' \
	            | egrep -v '^gnus-dired$$' \
	            | egrep -v '^gnus-group$$' \
	            | egrep -v '^gnus-score$$' \
	            | egrep -v '^gnus-sieve$$' \
	            | egrep -v '^gnus-start$$' \
	            | egrep -v '^gnus-sum$$' \
	            | egrep -v '^grep$$' \
	            | egrep -v '^gud$$' \
	            | egrep -v '^help$$' \
	            | egrep -v '^hi-lock$$' \
	            | egrep -v '^hideif$$' \
	            | egrep -v '^hideshow$$' \
	            | egrep -v '^hilit-chg$$' \
	            | egrep -v '^hippie-exp$$' \
	            | egrep -v '^hl-line$$' \
	            | egrep -v '^holidays$$' \
	            | egrep -v '^ibuffer$$' \
	            | egrep -v '^ielm$$' \
	            | egrep -v '^image-file$$' \
	            | egrep -v '^indent$$' \
	            | egrep -v '^info$$' \
	            | egrep -v '^info-look$$' \
	            | egrep -v '^isearch$$' \
	            | egrep -v '^ispell$$' \
	            | egrep -v '^jka-compr$$' \
	            | egrep -v '^lisp-mode$$' \
	            | egrep -v '^message$$' \
	            | egrep -v '^mhtml-mode$$' \
	            | egrep -v '^midnight$$' \
	            | egrep -v '^mm-decode$$' \
	            | egrep -v '^mml$$' \
	            | egrep -v '^mule$$' \
	            | egrep -v '^nnmail$$' \
	            | egrep -v '^nroff-mode$$' \
	            | egrep -v '^nxml-mode$$' \
	            | egrep -v '^outline$$' \
	            | egrep -v '^pcomplete$$' \
	            | egrep -v '^ps-print$$' \
	            | egrep -v '^re-builder$$' \
	            | egrep -v '^recentf$$' \
	            | egrep -v '^rect$$' \
	            | egrep -v '^reftex$$' \
	            | egrep -v '^repeat$$' \
	            | egrep -v '^ruby-mode$$' \
	            | egrep -v '^savehist$$' \
	            | egrep -v '^saveplace$$' \
	            | egrep -v '^sendmail$$' \
	            | egrep -v '^server$$' \
	            | egrep -v '^sh-script$$' \
	            | egrep -v '^shell$$' \
	            | egrep -v '^smerge-mode$$' \
	            | egrep -v '^solar$$' \
	            | egrep -v '^sql$$' \
	            | egrep -v '^term$$' \
	            | egrep -v '^texinfo$$' \
	            | egrep -v '^text-mode$$' \
	            | egrep -v '^time$$' \
	            | egrep -v '^tramp$$' \
	            | egrep -v '^tramp-sh$$' \
	            | egrep -v '^uniquify$$' \
	            | egrep -v '^vc$$' \
	            | egrep -v '^which-func$$' \
	            | egrep -v '^whitespace$$' \
	            | egrep -v '^winner$$' \
	            | egrep -v '^agda-input$$' \
	            | egrep -v '^bind-key$$' \
	            | egrep -v '^coq-mode$$' \
	            | egrep -v '^corfu-popupinfo$$' \
	            | egrep -v '^dafny-mode$$' \
	            | egrep -v '^dash$$' \
	            | egrep -v '^diff-hl-flydiff$$' \
	            | egrep -v '^docker-compose$$' \
	            | egrep -v '^docker-container$$' \
	            | egrep -v '^docker-image$$' \
	            | egrep -v '^docker-network$$' \
	            | egrep -v '^docker-volume$$' \
	            | egrep -v '^eldoc$$' \
	            | egrep -v '^git-commit$$' \
	            | egrep -v '^lsp-headerline$$' \
	            | egrep -v '^lsp-lens$$' \
	            | egrep -v '^magit-autorevert$$' \
	            | egrep -v '^magit-commit$$' \
	            | egrep -v '^magit-pull$$' \
	            | egrep -v '^magit-push$$' \
	            | egrep -v '^magit-status$$' \
	            | egrep -v '^mc-freeze$$' \
	            | egrep -v '^mc-rect$$' \
	            | egrep -v '^org-roam-dailies$$' \
	            | egrep -v '^password-store-otp$$' \
	            | egrep -v '^pg-user$$' \
	            | egrep -v '^transient$$' \
                 ) \
	        <(grep '^  [a-zA-Z]' ~/src/nix/config/emacs.nix \
	            | sed -e 's/#.*//' \
	            | perl -pe 's/ +//g' \
	            | sort | uniq \
	            | egrep -v '^use-package$$' \
	         )

clean:
	rm -f init.el *.elc *~ settings.el

### Makefile ends here
