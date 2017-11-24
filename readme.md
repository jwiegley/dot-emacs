This add-on defines three *[company-mode](http://company-mode.github.io/)* backends:

* `company-math-symbols-latex`	- math latex tags (_by default, active only on latex math faces_)

   ![symbols](https://raw.github.com/vspinu/company-math/master/img/latex-symbols.png)

* `company-math-symbols-unicode`	- math unicode symbols and sub(super)scripts (_by default, active everywhere except math faces_)

   ![math](https://raw.github.com/vspinu/company-math/master/img/unicode-symbols.png)

* `company-latex-commands` 		- latex commands 

## Usage ##

Start math completion by typing the prefix <kbd>`\`</kbd> key. To select the
completion type <kbd>RET</kbd>. Depending on the context and your configuration
unicode symbol or latex tag will be inserted. 

Since version 1.2 sub(super)script completion is available for the
`company-math-symbols-unicode` backend. Subscripts are inserted with either `__`
or `\_` prefixes. Superscripts with `^^` or `\^`. Customize
`company-math-subscript-prefix` and `company-math-superscript-prefix` if you
don't like this default.

## Activation ##

Install from ELPA or MELPA repositories.

You can either register each backend globally:


```elisp

;; global activation of the unicode symbol completion 
(add-to-list 'company-backends 'company-math-symbols-unicode)

```

or locally per emacs mode:


```elisp

;; local configuration for TeX modes
(defun my-latex-mode-setup ()
  (setq-local company-backends
              (append '((company-math-symbols-latex company-latex-commands))
                      company-backends)))

(add-hook 'tex-mode-hook 'my-latex-mode-setup)
 
```

If you are using `AUCTeX` you might need to use `TeX-mode-hook` instead:

```elisp
(add-hook 'TeX-mode-hook 'my-latex-mode-setup)
```

## Further Customization ##

Set `company-tooltip-align-annotations` to t in order to align symbols to the
right as in the snapshots from above.

By default unicode symbols backend (`company-math-symbols-unicode`) is not
active in latex math environments and latex math symbols
(`company-math-symbols-latex`) is not available outside of math latex
environments. You can use the following custom lists of faces to change this
behavior: `company-math-disallow-unicode-symbols-in-faces`,
`company-math-allow-unicode-symbols-in-faces`,
`company-math-disallow-latex-symbols-in-faces`,
`company-math-allow-latex-symbols-in-faces`.
 
