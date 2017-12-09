# esh-buf-stack.el

This library adds a buffer stack feature to Eshell.
It is inspired by the buffer stack in Zsh.

You can install it by using `package-install` via [MELPA](http://melpa.milkbox.net/).

To use this package, add these lines to your `.emacs` file:
```elisp
    (require 'esh-buf-stack)
    (setup-eshell-buf-stack)
    (add-hook 'eshell-mode-hook
              (lambda ()
                (local-set-key
                 (kbd "M-q") 'eshell-push-command)))
```
You can push the current command to the buffer stack by using `M-q`,
and after executing another command, you can see the top of the stack poped.
