#!/bin/sh

# Create a tar file from the current sources for e.g. Marmalade.

VERSION="$(sed -ne 's/^;; Version: *\([0-9.]*\)/\1/p' iedit.el)"

mkdir -p release
mkdir -p "release/iedit-$VERSION"
cp *.el README.org "release/iedit-$VERSION"
echo "(define-package \"iedit\" \"$VERSION\" \"Edit multiple regions in the same way simultaneously.\" '())" > "release/iedit-$VERSION/iedit-pkg.el"

AUTOLOADS="$(pwd)/release/iedit-$VERSION/iedit-autoloads.el"
emacs -q --batch --eval \
  "(let ((generated-autoload-file \"$AUTOLOADS\"))
     (batch-update-autoloads))" \
  "release/iedit-$VERSION"
rm -f "release/iedit-$VERSION"/*.el~
tar -C release -c "iedit-$VERSION" > "release/iedit-${VERSION}.tar"
rm -rf "release/iedit-$VERSION"

echo
echo "Release read for upload in release/iedit-${VERSION}.tar"
