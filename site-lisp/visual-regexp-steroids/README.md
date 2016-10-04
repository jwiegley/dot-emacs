# visual-regexp-steroids

visual-regexp-steroids is an extension to [visual-regexp](https://github.com/benma/visual-regexp.el) which enables the use of modern regexp engines (no more escaped group parentheses, and other goodies!).
In addition to that, you can optionally use the better regexp syntax to power `isearch-forward-regexp` and `isearch-backward-regexp`.

For now, Python and [pcre2el](https://github.com/joddie/pcre2el) is supported out of the box (tested on Linux and Windows). If you want to add custom scripts to enable your favorite language, please get in touch.

## Installation

Requirements:
* [visual-regexp](https://github.com/benma/visual-regexp.el)
* Python

If you are using Emacs 24, you can get visual-regexp-steroids from [melpa](http://melpa.milkbox.net/) with the package manager.

Add the following code to your init file. Of course you can select your own key bindings.
Note: `vr/mc-mark` is an interface to [multiple-cursors](https://github.com/magnars/multiple-cursors.el/).

The functions are the same as in visual-regexp, but powered by Python (or another custom engine).
You can choose the engine (e.g. to fall back to the Emacs regexp engine) with `vr/select-replace`, `vr/select-query-replace` and `vr/select-mc-mark`.

```Lisp
;; if the files are not already in the load path
(add-to-list 'load-path "folder-to/visual-regexp/")
(add-to-list 'load-path "folder-to/visual-regexp-steroids/")
(require 'visual-regexp-steroids)
(define-key global-map (kbd "C-c r") 'vr/replace)
(define-key global-map (kbd "C-c q") 'vr/query-replace)
;; if you use multiple-cursors, this is for you:
(define-key global-map (kbd "C-c m") 'vr/mc-mark)
;; to use visual-regexp-steroids's isearch instead of the built-in regexp isearch, also include the following lines:
(define-key esc-map (kbd "C-r") 'vr/isearch-backward) ;; C-M-r
(define-key esc-map (kbd "C-s") 'vr/isearch-forward) ;; C-M-s
```
To customize, use `M-x customize-group [RET] visual-regexp`. You can specify which engine to use by modifying `vr/engine` (defaults to Python), and how the Python interpreter is invoked by modifying the `vr/command-python` variable. The default is `python /path/to/visual-regexp-steroids/regexp.py`.

## Examples

Same example as in [visual-regexp](https://github.com/benma/visual-regexp.el), but this time using Python's regular expressions (note the absence of escape characters):

![Example](https://github.com/benma/visual-regexp-steroids.el/raw/master/screenshots/screenshot0A.png)

visual-regexp-steroids also features expressions as replacements (toggle with `C-c C-c`).
![Example](https://github.com/benma/visual-regexp-steroids.el/raw/master/screenshots/montage1.png)

Expressions have a predefined variables. `i`, the match counter, is one of them:
![Example](https://github.com/benma/visual-regexp-steroids.el/raw/master/screenshots/montage2.png)

## Tip Jar
If you found this useful, please consider donating.

BTC: 1KtDEa5saBdJ2AFcFq93QZ3jz3sYpq2z2
