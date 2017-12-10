cwd := $(shell pwd)
emacs ?= emacsclient
emacsflags := -q -a ''
version := $(shell date +%s)
tar_version := $(version).0
package := discover-my-major-$(tar_version).tar
pkg := discover-my-major-pkg.el
sources := $(filter-out %-pkg.el, $(wildcard *.el))
tar = $(cwd)/$(shell ls -t *.tar | head -1)

all: package

package : $(package)
$(package) : $(sources) $(pkg)
	@echo
	@echo Creating the package for package.el...
	@rm -f *.tar
	@rm -rf discover-my-major-*/
	@mkdir -p discover-my-major-$(tar_version)
	@cp -f $(sources) $(pkg) discover-my-major-$(tar_version)
	@tar cf $(package) discover-my-major-$(tar_version)
	@rm -rf discover-my-major-$(tar_version)
	@rm -f $(pkg)
	@echo \"$(package)\" created.
	@echo

install : package
	@echo
	@echo Installing the Emacs package...
	@$(emacs) $(emacsflags) --eval '(package-install-file "$(tar)")'
	@echo
	@echo \"$(tar)\" installed.
	@echo

$(pkg) : $(sources)
	@echo
	@echo Creating the pkg file...
	@rm -f $(pkg)
	@echo \(define-package \"discover-my-major\" \"$(version)\" \"Discover key bindings and their meaning for the current Emacs major mode\" \'\(\(makey \"0.2\"\)\)\) > $(pkg)
	@echo \"$(pkg)\" created.
	@echo
