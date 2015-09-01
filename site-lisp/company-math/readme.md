This add-on defines three *[company-mode](http://company-mode.github.io/)* backends:

* `company-math-symbols-latex`	- math latex tags (_by default, active only on latex math faces_)

      ![symbols](https://raw.github.com/vspinu/company-math/master/img/latex-symbols.png)

* `company-math-symbols-unicode`	- unicode symbols (_by default, active everywhere except math faces_)

      ![math](https://raw.github.com/vspinu/company-math/master/img/unicode-symbols.png)

* `company-latex-commands` 		- latex commands 

## Usage ##

Start math completion by typing the prefix <kbd>`\`</kbd> key. To select the
completion type <kbd>RET</kbd>. Depending on the context and your configuration
unicode symbol or latex tag will be inserted.

## Activation ##

Install from [MELPA](http://melpa.milkbox.net/) repository.

You can either register each backend globally:


```lisp

;; global activation of the unicode symbol completion 
(add-to-list 'company-backends 'company-math-symbols-unicode)


```

or locally per emacs mode:


```lisp

;; local configuration for TeX modes
(defun my-latex-mode-setup ()
  (setq-local company-backends
              (append '(company-math-symbols-latex company-latex-commands)
                      company-backends)))

(add-hook 'TeX-mode-hook 'my-latex-mode-setup)
 
```

## Customization ##

Set `company-tooltip-align-annotations` to t in order to allin symbols to the
right as in the above previews.

By default unicode symbols backend (`company-math-symbols-unicode`) is not
active in latex math environments and latex math symbols
(`company-math-symbols-latex`) is not available outside of math latex
environmnts. You can use the following variables to adjust this behavior to your
liking: `company-math-disallow-unicode-symbols-in-faces`,
`company-math-allow-unicode-symbols-in-faces`,
`company-math-disallow-latex-symbols-in-faces`,
`company-math-allow-latex-symbols-in-faces`.
 
