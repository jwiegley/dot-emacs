# phi-search-mc.el

This package is a multiple-cursors extension for
[phi-search](https://github.com/zk-phi/phi-search).

## Functions

phi-search-mc.el provides the following interactive commands:

* phi-search-mc/mark-here
* phi-search-mc/mark-forward
* phi-search-mc/mark-backward
* phi-search-mc/mark-all

  These functions serve as great way to add fake cursors at your
  desired points using phi-search.

* phi-search-from-isearch
* phi-search-from-isearch-mc/mark-next
* phi-search-from-isearch-mc/mark-previous
* phi-search-from-isearch-mc/mark-all

## Installation

This package is available on [MELPA](http://melpa.org/).

## Configuration

Run the following line to rebind `mc/mark-next-like-this`,
`mc/mark-previous-like-this` and `mc/mark-all-like-this` in phi-search
buffer to `phi-search-mc/mark-next`, `phi-search-mc/mark-previous` and
`phi-search-mc/mark-all`, respectively.

```elisp
(phi-search-mc/setup-keys)
```

Run the following line to bind `phi-search`, `mc/mark-next-like-this`,
`mc/mark-previous-like-this` and `mc/mark-all-like-this` in isearch
mode to `phi-search-from-isearch`,
`phi-search-from-isearch-mc/mark-next`,
`phi-search-from-isearch-mc/mark-previous` and
`phi-search-from-isearch-mc/mark-all`, respectively.

```elisp
(add-hook 'isearch-mode-hook 'phi-search-from-isearch-mc/setup-keys)
```

If you have bound multi-stroke keys to `mc/mark-next-like-this` etc.,
this may not be enough.  For example, I bound
<kbd>C-></kbd>/<kbd>C-<</kbd>/<kbd>C-.!</kbd> to `mc/mark-*`
functions, and since they are complex multi-stroke keys on my terminal
emulator where <kbd>C-></kbd> is mapped to <kbd>C-x @ c ></kbd> etc.,
I had to add the following lines for the features to work properly.

```elisp
(defvar phi-search-from-isearch-mc/ctl-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd ">")   'phi-search-from-isearch-mc/mark-next)
    (define-key map (kbd "<")   'phi-search-from-isearch-mc/mark-previous)
    (define-key map (kbd ". !") 'phi-search-from-isearch-mc/mark-all)
    map))

(defadvice phi-search-from-isearch-mc/setup-keys
  (after for-terminal activate)
  (define-key isearch-mode-map (kbd "C-x @ c") phi-search-from-isearch-mc/ctl-map))
```

## Author

Copyright (c) 2013-2015 Akinori MUSHA.

Licensed under the 2-clause BSD license.  See `LICENSE.txt` for
details.

Visit [GitHub Repository](https://github.com/knu/phi-search-mc.el) for
the latest information.
