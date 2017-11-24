[![Melpa Status](http://melpa.org/packages/persistent-scratch-badge.svg)](http://melpa.org/#/persistent-scratch)
[![Melpa Stable Status](http://stable.melpa.org/packages/persistent-scratch-badge.svg)](http://stable.melpa.org/#/persistent-scratch)

# Persistent scratch

`persistent-scratch` is an Emacs package that preserves the state of scratch
buffers accross Emacs sessions by saving the state to and restoring it from a
file.

## Installation

The package is available in [MELPA](http://melpa.org/) and
[MELPA Stable](http://stable.melpa.org/).

If you have MELPA or MELPA Stable in `package-archives`, use

    M-x package-install RET persistent-scratch RET

If you don't, open `persistent-scratch.el` in Emacs and call
`package-install-from-buffer`.

Other installation methods are unsupported.

## Usage

To save the current state of scratch buffers to file indicated by
`persistent-scratch-save-file`:

    M-x persistent-scratch-save

To restore scratch buffers from `persistent-scratch-save-file`:

    M-x persistent-scratch-restore

To save the state to an arbitrary file:

    M-x persistent-scratch-save-to-file

To restore the state from an arbitrary file:

    M-x persistent-scratch-restore-from-file

To toggle periodic autosave:

    M-x persistent-scratch-autosave-mode

To create a new backup file (only when backup is enabled, see
`persistent-scratch-backup-directory`), so that the next
`persistent-scratch-save` won't overwrite the existing backup:

    M-x persistent-scratch-new-backup

To customize the save file path, what state to save, the autosave period, what
buffers are considered scratch buffers and whether to backup old saved states:

    M-x customize-group RET persistent-scratch RET

## Init file considerations

Variables can be customized either via `customize` or by setting them via `setq`
directly.

To both enable autosave and restore the last saved state, if any, on Emacs
start, add
```emacs-lisp
(persistent-scratch-setup-default)
```
to the init file. This will **not** error when the save file doesn't exist.

To just enable autosave, enable `persistent-scratch-autosave-mode` like any
other minor mode:
```emacs-lisp
(persistent-scratch-autosave-mode 1)
```

To just restore the last saved file, use `persistent-scratch-restore`. Bear in
mind it may signal an error if there's no save file, so it's a good idea to call
it inside `ignore-errors` or `with-demoted-errors`.
