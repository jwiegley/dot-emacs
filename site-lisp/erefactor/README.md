# erefactor.el

Simple refactoring, linting utilities for Emacs-Lisp.

## Install:

Put this file into load-path'ed directory,
and byte compile its if desired.
And put the following expression into your ~/.emacs.

    (require 'erefactor)
    (add-hook 'emacs-lisp-mode-hook
       (lambda ()
         (define-key emacs-lisp-mode-map "\C-c\C-v" erefactor-map)))

And set these variables correctly.
 `erefactor-lint-path-alist', `erefactor-lint-by-emacsen'

Put the following in your .emacs, if you desire highlighting local variable.

    (add-hook 'emacs-lisp-mode-hook 'erefactor-lazy-highlight-turn-on)
    (add-hook 'lisp-interaction-mode-hook 'erefactor-lazy-highlight-turn-on)

## Usage:

* C-c C-v l : elint current buffer in clean environment.
* C-c C-v L : elint current buffer by multiple emacs binaries.
             See `erefactor-lint-emacsen'
* C-c C-v r : Rename symbol in current buffer.
             Resolve `let' binding as long as i can.
* C-c C-v R : Rename symbol in requiring modules and current buffer.
* C-c C-v h : Highlight current symbol in this buffer
             and suppress `erefacthr-highlight-mode'.
* C-c C-v d : Dehighlight all by above command.
* C-c C-v c : Switch prefix bunch of symbols.
             ex: '(hoge-var hoge-func) -> '(foo-var foo-func)
* C-c C-v ? : Display flymake elint warnings/errors

* To show compilation warnings when evaluate `defun' form.

    M-x erefactor-check-eval-mode
