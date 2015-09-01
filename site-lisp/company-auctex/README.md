# Company-AUCTeX

This is a group of backends for [company-mode](https://github.com/company-mode/company-mode/) providing auto-completion for [AUCTeX](https://www.gnu.org/software/auctex/).

It is adapted from [auto-complete-auctex](https://github.com/monsanto/auto-complete-auctex/).

## Installation

1. From MELPA (see http://melpa.org/#/getting-started for enabling it, if required):

        M-x package-install RET company-auctex RET

2. From Github:

        git clone https://github.com/alexeyr/company-auctex.git

  In the initialization file (`~/.emacs`, `~/.emacs.d/init.el`, etc.):

        (add-to-list 'load-path "path/to/company-auctex.el")
        (require 'company-auctex)

Then require the package and initialize it:

    (company-auctex-init)
    
## Issues

* If `company-backends` is set directly without using `push`, `add-to-list` or similar functions (e.g. by Customize interface), `(company-auctex-init)` must be run after this (or its backends added to the same place).
* This error can happen after updating to AUCTeX 11.88: `Lisp error: (invalid-function TeX-auto-add-type)` triggered by `(require 'latex)` in `company-auctex`. It seems to be caused by something in existing configuration and can also happen without `company-auctex`. Workarounds include: downgrading to 11.87; reinstalling AUCTeX; cleaning up cruft from `custom-set-variables`. See [issue 1](https://github.com/alexeyr/company-auctex/issues/1) for more details.

## To-do

1. Expand README (add features, screenshots).

2. Support inserting Unicode characters in non-TeX modes (similar to [ac-math](https://github.com/vitoshka/ac-math)).

3. Some commands (\begin, \emph, etc.) aren't getting completed. Need to check if they are in any lists provided by AUCTeX.
