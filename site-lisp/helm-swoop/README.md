[![melpa badge][melpa-badge]][melpa-link] [![melpa stable badge][melpa-stable-badge]][melpa-stable-link]

List match lines to another buffer, which is able to squeeze by any words you input. At the same time, the original buffer's cursor is jumping line to line according to moving up and down the line list.

![helm-swoop](https://raw.githubusercontent.com/ShingoFukuyama/images/master/helm-swoop.gif)

### Feature

* Culling all lines in buffer with your input
* Highlight multiple matched pattern
* Jumping line to line according to list buffer's move
* Cache result until modifies the buffer
* Go back to the last line
* Multi separated line culling
* Culling lines are editable

### Usage

#### Now helm-swoop has several ways.

* `M-x helm-swoop` when region active
* `M-x helm-swoop` when the cursor is at any symbol
* `M-x helm-swoop` when the cursor is not at any symbol
* `M-3 M-x helm-swoop` or `C-u 5 M-x helm-swoop` multi separated line culling
* `M-x helm-multi-swoop` multi-occur like feature
* `M-x helm-multi-swoop-all` apply all buffers
* `C-u M-x helm-multi-swoop` apply last selected buffers from the second time
* `M-x helm-multi-swoop-org` apply to all org-mode buffers
* `M-x helm-multi-swoop-current-mode` apply to all buffers with the same major-mode as the current buffer
* `M-x helm-multi-swoop-projectile` Apply to all opened buffers of the current project
* `M-x helm-swoop-same-face-at-point` list lines have the same face at the cursor is on
* During isearch `M-i` to hand the word over to helm-swoop
* During helm-swoop `M-i` to hand the word over to helm-multi-swoop-all
* While doing `helm-swoop` press `C-c C-e` to edit mode, apply changes to original buffer by `C-x C-s`

It's able to use words within a region or a word at symbol as search query when it called. Also use a keybind you set just type like M-i instead of `M-x helm-swoop`. 

#### Edit mode
While doing `helm-swoop` type `C-c C-e` to enter the edit mode.
Before enter the edit mode, you can choose some lines marked by `C-SPC` or `M-SPC` to edit.
Apply changes to original buffer type `C-x C-s`.

#### Across multiple buffers

##### `M-x helm-multi-swoop`
1. Select any buffers by [C-SPC] or [M-SPC]
2. Press [RET] to start helm-multi-swoop

![helm-multi-swoop](https://raw.githubusercontent.com/ShingoFukuyama/images/master/helm-multi-swoop.gif)

##### `M-x helm-multi-swoop-all`
Skip select phase and apply all buffers.

##### `C-u M-x helm-multi-swoop`
Skip select phase and apply last selected buffers, if you have done helm-multi-swoop before.

#### `M-x helm-multi-swoop-org`
Skip the select phase and apply to all org-mode buffers

#### `M-x helm-multi-swoop-current-mode`
Skip the select phase and apply to all buffers with the same major mode as the current buffer

#### `M-x helm-multi-swoop-projectile`
Skip the select phase and apply to all opened buffers of the current project.
It requires projectile to be installed.
You may specify a filter that will be used for buffers
by setting variable `helm-multi-swoop-projectile-buffers-filter`.
By default its value is `projectile-buffers-with-file-or-process`.

#### Multiline behavior 
`M-4 M-x helm-swoop` or `C-u 4 M-x helm-swoop`

![helm-swoop2](https://raw.githubusercontent.com/ShingoFukuyama/images/master/helm-swoop2.gif)

### Config

```elisp
;; helm from https://github.com/emacs-helm/helm
(require 'helm)

;; Locate the helm-swoop folder to your path
(add-to-list 'load-path "~/.emacs.d/elisp/helm-swoop")
(require 'helm-swoop)

;; Change the keybinds to whatever you like :)
(global-set-key (kbd "M-i") 'helm-swoop)
(global-set-key (kbd "M-I") 'helm-swoop-back-to-last-point)
(global-set-key (kbd "C-c M-i") 'helm-multi-swoop)
(global-set-key (kbd "C-x M-i") 'helm-multi-swoop-all)

;; When doing isearch, hand the word over to helm-swoop
(define-key isearch-mode-map (kbd "M-i") 'helm-swoop-from-isearch)
;; From helm-swoop to helm-multi-swoop-all
(define-key helm-swoop-map (kbd "M-i") 'helm-multi-swoop-all-from-helm-swoop)
;; When doing evil-search, hand the word over to helm-swoop
;; (define-key evil-motion-state-map (kbd "M-i") 'helm-swoop-from-evil-search)

;; Instead of helm-multi-swoop-all, you can also use helm-multi-swoop-current-mode
(define-key helm-swoop-map (kbd "M-m") 'helm-multi-swoop-current-mode-from-helm-swoop)

;; Move up and down like isearch
(define-key helm-swoop-map (kbd "C-r") 'helm-previous-line)
(define-key helm-swoop-map (kbd "C-s") 'helm-next-line)
(define-key helm-multi-swoop-map (kbd "C-r") 'helm-previous-line)
(define-key helm-multi-swoop-map (kbd "C-s") 'helm-next-line)

;; Save buffer when helm-multi-swoop-edit complete
(setq helm-multi-swoop-edit-save t)

;; If this value is t, split window inside the current window
(setq helm-swoop-split-with-multiple-windows nil)

;; Split direcion. 'split-window-vertically or 'split-window-horizontally
(setq helm-swoop-split-direction 'split-window-vertically)

;; If nil, you can slightly boost invoke speed in exchange for text color
(setq helm-swoop-speed-or-color nil)

;; ;; Go to the opposite side of line from the end or beginning of line
(setq helm-swoop-move-to-line-cycle t)

;; Optional face for line numbers
;; Face name is `helm-swoop-line-number-face`
(setq helm-swoop-use-line-number-face t)

;; If you prefer fuzzy matching
(setq helm-swoop-use-fuzzy-match t)

;; If you would like to use migemo, enable helm's migemo feature
(helm-migemo-mode 1)
```

#### Configure pre-input search query

By default, helm-swoop uses search query at the cursor.
You can configure this behavior by setting `helm-swoop-pre-input-function` on your own.

i.e.

```elisp
;; Use search query at the cursor  (default)
(setq helm-swoop-pre-input-function
      (lambda () (thing-at-point 'symbol)))

;; Disable pre-input
(setq helm-swoop-pre-input-function
      (lambda () ""))
;; Or, just use M-x helm-swoop-without-pre-input

;; Match only for symbol
(setq helm-swoop-pre-input-function
      (lambda () (format "\\_<%s\\_> " (thing-at-point 'symbol))))

;; Always use the previous search for helm. Remember C-<backspace> will delete entire line
(setq helm-swoop-pre-input-function
      (lambda () (if (boundp 'helm-swoop-pattern)
                     helm-swoop-pattern "")))

;; If there is no symbol at the cursor, use the last used words instead.
(setq helm-swoop-pre-input-function
      (lambda ()
        (let (($pre-input (thing-at-point 'symbol)))
          (if (eq (length $pre-input) 0)
              helm-swoop-pattern ;; this variable keeps the last used words
            $pre-input))))
```

### Require

[helm.el](https://github.com/emacs-helm/helm)



[melpa-link]: http://melpa.org/#/helm-swoop
[melpa-stable-link]: http://stable.melpa.org/#/helm-swoop
[melpa-badge]: http://melpa.org/packages/helm-swoop-badge.svg
[melpa-stable-badge]: http://stable.melpa.org/packages/helm-swoop-badge.svg
