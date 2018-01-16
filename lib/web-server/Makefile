EMACS := emacs
BATCH=$(EMACS) --batch --execute '(add-to-list (quote load-path) "$(shell pwd)")'

SRC=$(wildcard *.el)
ELC=$(SRC:.el=.elc)

.PHONY: src doc check clean
all: src doc

src: $(SRC)
	$(BATCH) -f batch-byte-compile $^

doc:
	$(MAKE) -C doc/

doc/web-server.info:
	$(MAKE) -C doc/ web-server.info

doc/dir:
	$(MAKE) -C doc/ dir

check: $(SRC)
	$(BATCH) -l cl -l ert -l web-server-test -f ert-run-tests-batch-and-exit

clean:
	rm -rf $(ELC) $(PACKAGE) $(PACKAGE).tar
	$(MAKE) -C doc/ $(MAKECMDGOALS)

# Packaging
PARSE=grep "$(1):" web-server.el|sed 's/^.*$(1): //'
NAME=web-server
VERSION=$(shell $(call PARSE,Version))
DOC=$(shell head -1 web-server.el|sed 's/^.*--- //')
REQ=$(shell $(call PARSE,Package-Requires))
DEFPKG=(define-package "$(NAME)" "$(VERSION)"\n  "$(DOC)"\n  (quote $(REQ)))
PACKAGE=$(NAME)-$(VERSION)

$(PACKAGE): $(filter-out web-server-test.el, $(SRC)) doc/web-server.info doc/dir
	mkdir -p $(PACKAGE)
	cp $^ $(PACKAGE)
	sed -n '/;;; Commentary:/,/;;; Code:/p' web-server.el|tail -n+3|head -n-2|cut -c4- >$(PACKAGE)/README
	echo -e '$(DEFPKG)' > $(PACKAGE)/$(NAME)-pkg.el

$(PACKAGE).tar: $(PACKAGE)
	tar cf $@ $<

package: $(PACKAGE).tar
