CASK  ?= cask
WGET  ?= wget
EMACS  = emacs

EMACSFLAGS =
EMACSBATCH = $(EMACS) --batch -Q $(EMACSFLAGS)

export EMACS

PKGDIR := $(shell EMACS=$(EMACS) $(CASK) package-directory)

SRCS = jist.el
OBJS = $(SRCS:.el=.elc)

.PHONY: all compile clean

all: compile README.md

compile: $(OBJS)

clean:
	$(RM) $(OBJS)

%.elc: %.el $(PKGDIR)
	$(CASK) exec $(EMACSBATCH) -f batch-byte-compile $<

$(PKGDIR) : Cask
	$(CASK) install
	touch $(PKGDIR)

README.md: make-readme-markdown.el $(SRCS)
	$(CASK) exec $(EMACSBATCH) --script $< <$(SRCS) >$@ 2>/dev/null

make-readme-markdown.el:
	$(WGET) -q -O $@ "https://github.com/mgalgs/make-readme-markdown/raw/master/make-readme-markdown.el"

.INTERMEDIATE: make-readme-markdown.el
