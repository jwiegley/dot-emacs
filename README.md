helm-company.el [![Build Status](https://travis-ci.org/yasuyk/helm-company.png)](https://travis-ci.org/yasuyk/helm-company)
============

[Helm] interface for [company-mode]

## Requirements

- [Helm]
- [company-mode]

## Installation

## Installation

### Manual

Just drop `helm-company.el`. somewhere in your `load-path`.

```lisp
(add-to-list 'load-path "~/somewhere")
```

### MELPA

If you're an Emacs 24 user or you have a recent version of package.el
you can install `helm-company.el` from the [MELPA](http://melpa.milkbox.net/) repository.

## Configuration

Add the following to your Emacs init file.

    (autoload 'helm-company "helm-company") ;; Not necessary if using ELPA package
    (eval-after-load 'company
      '(progn
         (define-key company-mode-map (kbd "C-:") 'helm-company)
         (define-key company-active-map (kbd "C-:") 'helm-company)))

## Usage

####  `helm-company`

Select `company-complete` candidates by [`helm`][helm].
It is useful to narrow company candidates.

[Helm]:http://emacs-helm.github.io/helm/
[company-mode]:http://company-mode.github.io/
