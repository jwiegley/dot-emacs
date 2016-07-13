
all: package

package:
	cask package
clean:
	rm -rf dist
	rm -f -- *.elc

