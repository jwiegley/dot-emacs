#!/bin/sh

# This script downloads the major files from the Tramp Git repository.
# It requires a running "wget program.

TRAMP_GIT_DIR=http://git.savannah.gnu.org/cgit/tramp.git/plain
TRAMP_TARGET_DIR=tramp
TRAMP_SUB_DIRS="contrib lisp test texi"

# Check, that the target directory and the index files do not exist.
for file in plain $TRAMP_SUB_DIRS $TRAMP_TARGET_DIR; do
    if [ -e $file ]; then
	echo \"$file\" exist, exiting
	exit
    fi
done

# Download index files.
wget --convert-links -nH -nd $TRAMP_GIT_DIR
for subdir in $TRAMP_SUB_DIRS; do
    wget --convert-links -nH -nd $TRAMP_GIT_DIR/$subdir
done

# Download upper directory.  The subdirectories produce a respective
# index.html file; this must be removed.
mkdir $TRAMP_TARGET_DIR
cd $TRAMP_TARGET_DIR
wget -F -i ../plain
rm -f index.html* ../plain

# Download subdirectories.
for subdir in $TRAMP_SUB_DIRS; do
    (mkdir $subdir; cd $subdir; wget -F -i ../../$subdir; rm -f ../../$subdir)
done
