# This is not a full-featured Makefile and it is not intended to be used
# to install 'shift-number' package to your system.  Its only purpose is
# to byte-compile "shift-number.el" (using 'make') to make sure that
# there are no compilation warnings.

EMACS = emacs

LOAD_PATH = -L .
EMACS_BATCH = $(EMACS) -batch -Q $(LOAD_PATH)

ELS = shift-number.el
ELCS = $(ELS:.el=.elc)

all: $(ELCS)

%.elc: %.el
	@printf "Compiling $<\n"
	@$(EMACS_BATCH) -f batch-byte-compile $<

clean:
	$(RM) $(ELCS)
