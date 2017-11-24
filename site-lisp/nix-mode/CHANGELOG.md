# Changelog

## master

### New files

* create CHANGELOG.md

### Changes

## 1.2.1

### Changes

* fix byte-compile error

## 1.2.0

### New files

* nix-format.el: format Nix code using nixfmt
* nix-mode-mmm.el: treate multiline strings as sh-script within nix-mode
* nix-repl.el: run nix-repl within Emacs
* nix-prettify-mode.el: shorten store paths to /nix/store/…-foo-0.1
* nix-shell.el: run nix-shell within Emacs
* nix-company.el: complete Nix expressions through company

### Changes

All of these reflect nix-mode.el and what's been changed from the original nix-mode.el.

* add some simple tests for nix-mode
* handle antiquotes within Nix expressions better
* handle multiline string better
* fixes some edge cases for ''${ (escaped antiquote)
* indent Nix code based on Nix-specific rules (not just indent-relative)
* enforce Nix spacing style rules in nix-mode (2 spaces, no tabs)

### Bug fixes

This version fixes the following bugs in the original Nix version:

* fixes the issue where /* by a multiline string is interpreted as a comment
  (NixOS/nix#662)
* fixes antiquote highlighting within double quotes like x="${asdf}" (NixOS/nix#1055)
* fixes an issue in org-mode fontification of nix files (NixOS/nix#1040)
* Also, should these issues should be closable: NixOS/nix#1419, NixOS/nix#1086,
  NixOS/nix#1054

## 1.0

Original nix-mode
from [https://github.com/NixOS/nix/](https://github.com/NixOS/nix/). See that
repository for older changelog.
