#!/bin/sh

STARTRE='^;;; Commentary:$'
STOPRE='^;;; Code:$'
DATE=$(date +"%B %e, %Y %H:%M %Z")

# Produce README.md for GitHub
echo "# Deft for Emacs [![MELPA badge][melpa-badge]][melpa-link] [![MELPA stable badge][melpa-stable-badge]][melpa-stable-link] [![Travis CI Build Status][travis-badge]][travis-link]

  [melpa-link]: https://melpa.org/#/deft
  [melpa-stable-link]: https://stable.melpa.org/#/deft
  [melpa-badge]: https://melpa.org/packages/deft-badge.svg
  [melpa-stable-badge]: https://stable.melpa.org/packages/deft-badge.svg
  [travis-link]: https://travis-ci.org/jrblevin/deft
  [travis-badge]: https://travis-ci.org/jrblevin/deft.svg?branch=master

<!-- Automatically generated from comments in deft.el. -->" > README.md

# Produce index.text for the Deft homepage
echo "title:       Deft for Emacs
description: Emacs mode for quickly browsing, filtering, and editing directories of plain text notes.
markup:      markdown
city:        Columbus
guid:        tag:jblevins.org,2011:/projects/deft/
feed:        true
created:     August 6, 2011 00:30 EDT
modified:    $DATE" > index.text

cat deft.el |\
    # Keep only the Commentary section
    awk "/$STARTRE/,/$STOPRE/" |\
    # Remove the start and step regexps
    grep -v "$STARTRE" | grep -v "$STOPRE" |\
    # Convert headers
    sed -e 's/^;;; \(.*\):$/## \1/' |\
    # Remove leading spaces (but don't disturb pre blocks)
    sed -e 's/^;;[ ]\{0,1\}//' |\
    # Escape wiki links
    #sed -e 's/\(\[\[[^]\n]*\]\]\)/\\\1/g' |\
    # Use Markdown-style backticks for single-quoted lisp code
    sed -e 's/`\([^'\'']*\)'\''/`\1`/g' |\
    # Use <kbd> tags for single character, unprefixed keybindings
    sed -e 's/`\([^`]\)`/<kbd>\1<\/kbd>/g' |\
    # Use <kbd> tags for TAB and RET keys
    sed -e 's/`TAB`/<kbd>TAB<\/kbd>/g' |\
    sed -e 's/`RET`/<kbd>RET<\/kbd>/g' |\
    # Use <kbd> tags for keybindings prefixed by C, M, or S
    sed -e 's/`\([CMS]-[^`]*\)`/<kbd>\1<\/kbd>/g' |\
    # Remove email addresses
    sed -e 's/ <[^>]*@[^<]*> / /g' \
    | tee -a README.md >> index.text
