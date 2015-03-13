# git-messenger.el

`git-messenger.el` is Emacs port of [git-messenger.vim](https://github.com/rhysd/git-messenger.vim).

`git-messenger.el` provides function that popup commit message at current line.
This is useful when you want to know why this line was changed.


## Screenshot

![git-messenger.el](image/git-messenger.png)


## Installation

You can install `git-messenger.el` from [MELPA](https://github.com/milkypostman/melpa.git) with package.el
(`M-x package-install git-messenger`).


## Dependency

* [popup](https://github.com/auto-complete/popup-el)


## Commands

### `git-messenger:popup-message`

Pop up last commit message at current line. Show detail message, Commit ID, Author,
Date and commit message with `C-u` prefix

![git-messenager-detail](image/git-messenger-detail.png)


## Key Bindings

You can modify key bindings by customizing `git-messenger-map`.

| Key                  | Command                                                 |
|:--------------------:|:--------------------------------------------------------|
| `M-w`                | Copy commit message and quit                            |
| `c`                  | Copy commit ID and quit                                 |
| `d`                  | Pop up `git diff` of last change of this line           |
| `s`                  | Pop up `git show --stat` of last change of this line    |
| `S`                  | Pop up `git show --stat -p` of last change of this line |
| `q`                  | Quit                                                    |


## Customize

### `git-messenger:show-detail`(Default `nil`)

Always show detail message if this value is `t`.

## Hooks

### `git-messenger:before-popup-hook`

Run before popup commit message. Hook function take one argument, commit message.

### `git-messenger:after-popup-hook`

Run after popup commit message. Hook function take one argument, commit message.

### `git-messenger:popup-buffer-hook`

Run after popup buffer.


## Global Variables

You may be able to use these variables useful in commands of `git-messenger-map`.

#### `git-messenger:last-message`

Last popup-ed commit message

#### `git-messenger:last-commit-id`

Last popup-ed commit ID


## Sample Configuration

```lisp
(require 'git-messenger) ;; You need not to load if you install with package.el
(global-set-key (kbd "C-x v p") 'git-messenger:popup-message)

(define-key git-messenger-map (kbd "m") 'git-messenger:copy-message)

;; Enable magit-commit-mode after typing 's', 'S', 'd'
(add-hook 'git-messenger:popup-buffer-hook 'magit-commit-mode)
```
