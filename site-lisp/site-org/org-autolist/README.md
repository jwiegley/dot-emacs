## Summary

**org-autolist** makes org-mode lists behave more like lists in non-programming editors such as Google Docs, MS Word, and OS X Notes.

When editing a list item, pressing "Return" will insert a new list item automatically. This works for both bullet points and checkboxes, so there's no need to think about whether to use `M-<return>` or `M-S-<return>`. Similarly, pressing "Backspace" at the beginning of a list item deletes the bullet / checkbox, and moves the cursor to the end of the previous line.

## Installation

The recommended way to install  org-autolist is via `package.el`.

### MELPA Stable

The latest stable version can be found in the [MELPA Stable](http://stable.melpa.org/#/org-autolist) repository.

### MELPA

If you'd like the latest, potentially unstable version, you can also install org-autolist from the normal [MELPA](http://melpa.org/#/org-autolist) repository.

## Usage

To enable org-autolist mode in the current buffer:

```el
(org-autolist-mode)
```

To enable it whenever you open an org file, add this to your `init.el`:

```
(add-hook 'org-mode-hook (lambda () (org-autolist-mode)))
```

## Examples

The easiest way to illustrate org-autolist's functionality is with a few examples. Here, we'll use the `|` character to indicate the cursor position.

### Inserting list items

Suppose we start with this list:

```
- one
- two
  - apple|
```

Pressing "Return" once will result in the following:

```
- one
- two
  - apple
  - |
```

Pressing "Return" again will result in:

```
- one
- two
  - apple
- |
```

And pressing "Return" a final time will result in:

```
- one
- two
  - apple
|
```

### Deleting list items

Now, suppose we start with:

```
- [ ] one
- [ ] two
  - [ ] apple
  - [ ] |
```

Pressing "Backspace" will produce:

```
- [ ] one
- [ ] two
  - [ ] apple|
```

Similarly, if we instead start from here:

```
- [ ] one
- [ ] two
  - [ ] |apple
```

Then pressing "Backspace" will produce:

```
- [ ] one
- [ ] two|apple
```

## Feedback

If you find a bug, or have a suggestion for an improvement, then feel free to submit an issue or pull request!
