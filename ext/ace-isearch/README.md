ace-isearch.el [![MELPA](http://melpa.org/packages/ace-isearch-badge.svg)](http://melpa.org/#/ace-isearch)
===========

## Introduction
`ace-isearch.el` provides a minor mode which combines `isearch` and [`ace-jump-mode`](https://github.com/winterTTr/ace-jump-mode).

The "default" behavior can be summrized as:
- L = 1     : `ace-jump-mode`
- 1 < L < 6 : `isearch`
- L >= 6    : `helm-swoop-from-isearch`

where L is the input string length during `isearch`.  When L is 1, after a
few seconds specified by `ace-isearch-input-idle-delay`, `ace-jump-mode` will
be invoked. Of course you can customize the above behaviour.

## Requirements

* Emacs 24 or higher
* [ace-jump-mode](https://github.com/winterTTr/ace-jump-mode)
* [helm-swoop](https://github.com/ShingoFukuyama/helm-swoop)

## Installation

You can install `ace-isearch.el` from [MELPA](http://melpa.org/#/ace-isearch) with `package.el`

```
 M-x package-install ace-isearch
```

Otherwise you can install it by [el-get](https://github.com/dimitri/el-get/blob/master/recipes/ace-isearch.rcp).

## Basic Usage

#### `ace-isearch-mode`

Enable `ace-isearch` minor mode:

```lisp
(ace-isearch-mode +1)
```

#### `global-ace-isearch-mode`

Enable global ace-isearch mode:

```lisp
(global-ace-isearch-mode +1)
```

## Customization

#### `ace-isearch-submode` (Default:`ace-jump-word-mode`)
Specify the function name as `ace-jump-word-mode` or `ace-jump-char-mode` utilized in invoking `ace-jump-mode`.

#### `ace-isearch-switch-submode`
You can switch the value of `ace-isearch-submode` interactively.

#### `ace-isearch-use-ace-jump` (Default:`t`)
If this variable is set to `nil`, `ace-jump-mode` is never invoked.

If set to `t`, it is always invoked if the length of `isearch-string` is equal to 1.

If set to `printing-char`, it is invoked only if you hit a printing character to search for as a first input.
This prevents it from being invoked when repeating a one character search, yanking a character or calling
`isearch-delete-char` leaving only one character.

#### `ace-isearch-input-idle-delay` (Default：`0.4`)
Delay seconds for invoking `ace-jump-mode` and `ace-isearch-function-from-isearch` described below during isearch.

#### `ace-isearch-input-length` (Default：`6`)
As default behaviour, when the input string length during isearch exceeds `ace-isearch-input-length`, 
the function specified by `ace-isearch-funtion-from-isearch` will be invoked.

#### `ace-isearch-function-from-isearch` (Default:`helm-swoop-from-isearch`)
Specify the function name invoked when the input string length during isearch exceeds `ace-isearch-input-length`.
If [swoop](https://github.com/ShingoFukuyama/emacs-swoop) has been installed, swoop can be invoked:

```el
(setq ace-isearch-funtion-from-isearch 'swoop-from-isearch)
```

In this case, the following setting would be better.

```el
(define-key swoop-map (kbd "C-s") 'swoop-action-goto-line-next)
(define-key swoop-map (kbd "C-r") 'swoop-action-goto-line-prev)
```

Of course you can set this variable to `helm-occur-from-isearch`.

```el
(setq ace-isearch-funtion-from-isearch 'helm-occur-from-isearch)
```

#### `ace-isearch-use-function-from-isearch` (Default:`t`)
If you don't want to invoke `ace-isearch-funtion-from-isearch`, set this variable to `nil`.

#### `ace-isearch-set-ace-jump-after-isearch-exit`
This functionality is optional.
`ace-jump-mode` will be invoked further using the isearch query after exiting isearch.
This helps to reduce many key repeats of `C-s` or `C-r`.

You can enable this as follows:

```el
(ace-isearch-set-ace-jump-after-isearch-exit t)
```

Otherwise you can disable this as follows:

```el
(ace-isearch-set-ace-jump-after-isearch-exit nil)
```

#### `ace-isearch-fallback-function`  (Default:`helm-swoop-from-isearch`)
This functionality is optional.
When isearch fails and `ace-isearch-use-fallback-function` is non-nil,
`ace-isearch-fallback-function` will be invoked as a fallback function.

You shoud specify the symbol name of function which uses `isearch-string`, the query string during isearch.
For a trivial example, you can specify it as follows:

```el
(defun my-fallback-function ()
  (message "Your isearch string is %s", isearch-string))
  
(setq ace-isearch-use-function-from-isearch t)
(setq ace-isearch-fallback-function 'my-fallback-function)
```

#### `ace-isearch-use-fallback-function`  (Default:`nil`)
If this variable is set to non-nil, `ace-isearch-fallback-function` will be invoked
when isearch fails.

## Notice
`ace-isearch-fallback-function` may not be used with `ace-isearch-set-ace-jump-after-isearch-exit` simultaneously.
Especially when `ace-isearch-fallback-function` is set to `helm-swoop-from-isearch` in which `isearch-exit` is invoked inside, `ace-isearch-set-ace-jump-after-isearch-exit` will prevent the fallback function from being invoked.

## Sample Configuration
```el
(require 'ace-isearch)
(global-ace-isearch-mode +1)

(custom-set-variables
 '(ace-isearch-input-length 7)
 '(ace-isearch-input-idle-delay 0.3)
 '(ace-isearch-submode 'ace-jump-char-mode)
 '(ace-isearch-use-ace-jump 'printing-char))
 
(ace-isearch-set-ace-jump-after-isearch-exit t)
```
