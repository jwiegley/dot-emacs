[![MELPA Stable](https://stable.melpa.org/packages/zoom-badge.svg)](https://stable.melpa.org/#/zoom)
[![MELPA](https://melpa.org/packages/zoom-badge.svg)](https://melpa.org/#/zoom)

# Zoom

This minor mode takes care of managing the window sizes by enforcing a fixed and
automatic balanced layout where the currently selected window is resized
according to `zoom-size` which can be an absolute value in lines/columns, a
ratio between the selected window and frame size or even a custom callback.

![Screencast](https://i.imgur.com/RktspPg.gif)

## Installation

### [MELPA] package

```
M-x package-install RET zoom
```

[MELPA]: https://melpa.org/#/getting-started

### Local package

```
M-x package-install-file RET /path/to/zoom.el
```

### Manual

```el
(require 'zoom "/path/to/zoom.el")
```

## Usage

Enable Zoom with `M-x zoom-mode` otherwise use `M-x zoom` to manually rearrange
windows just once.

Load it automatically with:

```el
(custom-set-variables
 '(zoom-mode t))
```

See the [FAQ].

[FAQ]: https://github.com/cyrus-and/zoom#faq

## Example configurations

For a complete reference see `M-x customize-group RET zoom`.

---

Resize the selected window using the [golden ratio]:

```el
(custom-set-variables
 '(zoom-size '(0.618 . 0.618)))
```

[golden ratio]: https://en.wikipedia.org/wiki/Golden_ratio

---

Resize the selected window according to the frame width, for example:

- 90 columns and 75% of the frame height if the frame width is larger than 1024
  pixels;
- half the frame size otherwise.

```el
(defun size-callback ()
  (cond ((> (frame-pixel-width) 1280) '(90 . 0.75))
        (t                            '(0.5 . 0.5))))

(custom-set-variables
 '(zoom-size 'size-callback))
```

---

Override the key binding of `balance-windows`:

```el
(global-set-key (kbd "C-x +") 'zoom)
```

---

Prevent some windows from being resized, for example:

- `dired` and `markdown` major modes;
- `zoom.el` `init.el` buffer names;
- calculator-related windows;
- any buffer containing less than 20 lines.

```el
(custom-set-variables
 '(zoom-ignored-major-modes '(dired-mode markdown-mode))
 '(zoom-ignored-buffer-names '("zoom.el" "init.el"))
 '(zoom-ignored-buffer-name-regexps '("^*calc"))
 '(zoom-ignore-predicates '((lambda () (> (count-lines (point-min) (point-max)) 20)))))
```

(Please note that ignored windows are not resized when selected but all the
windows are nevertheless arranged with `balance-windows`.)

## FAQ

### What about [`golden-ratio.el`]?

I have been a more or less happy [`golden-ratio.el`] user for some time when I
stared noticing some bugs and sadly I discovered that it is apparently a dead
project now, so I decided to write a new and improved minor mode from scratch
that implements the same basic idea of automatic window layout as my first
attempt at Emacs mode development.

[`golden-ratio.el`]: https://github.com/roman/golden-ratio.el

### Why when there are several horizontal splits the completions buffer is very small?

This happens when `zoom-minibuffer-preserve-layout` is non-`nil` (the default)
because most of the space is probably occupied by the zoomed window. The
solution (apart from setting the aforementioned variable to `nil`) is to enable
the `temp-buffer-resize-mode` minor mode:

```el
(custom-set-variables
 '(temp-buffer-resize-mode t))
```
