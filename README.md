# imenu-list
This Emacs minor-mode creates an automatically updated buffer called `*Ilist*` that is populated with the current buffer's imenu entries.

To activate imenu-list manually, use `M-x imenu-list-minor-mode`.  
To activate it automatically on startup, add this to your init file:
`(imenu-list-minor-mode)`

You can also use `M-x imenu-list-smart-toggle` to toggle imenu-list (and its window) on and off.
You may wish to bind it to a key, for example `C-'`:
```elisp
(global-set-key (kbd "C-'") #'imenu-list-smart-toggle)
```
The old suggestion was to bind `imenu-list-minor-mode`; however, `imenu-list-minor-mode` does not take the visibility of the `*Ilist*` buffer into account, and only checks the current value of `imenu-list-minor-mode`. The smart-toggle enables or disables the minor-mode depending on the visibility of the `*Ilist*` buffer.

The imenu of the current buffer will be displayed in the `*Ilist*` buffer. From the `*Ilist*` buffer, you can use these shortcuts:  
- `<enter>`: goto entry under cursor, or toggle case-folding.  
- `<space>`: display entry under cursor, but `*Ilist*` buffer remains current  
- `<mouse click>`: same as \<enter\>  
- `<tab>`: expand/collapse subtree (`hs-toggle-hiding`)  
- `f`: same as \<tab\>  
- `n`: next line  
- `p`: previous line  
- `g`: manually refresh entries  
- `q`: quit window and disable `imenu-list-minor-mode`  

Some users might prefer the `imenu-list-minor-mode`/`imenu-list-smart-toggle` commands to also set the focus to the `*Ilist*` window.
To do so, use the variable `imenu-list-focus-after-activation`:
```elisp
(setq imenu-list-focus-after-activation t)
```

The size of `*Ilist*` window can be automatically resized every time the `*Ilist*` buffer is
updated. To do so, use the variable `imenu-list-auto-resize`:
```elisp
(setq imenu-list-auto-resize t)
```
Note that the width of the window won't be resized if you're using emacs 24.3 or older.
That's because of a limitation in `fit-window-to-buffer`.
It is possible to take further actions every time the `*Ilist*` buffer is updated, by using
the hook `imenu-list-update-hook`.

After jumping to an entry from the `*Ilist*` buffer, e.g. by pressing `<enter>` or `<space>`, the target buffer will be recentered so the cursor is in the middle. To cancel that, reset the hook `imenu-list-after-jump-hook`:

```elisp
(setq imenu-list-after-jump-hook nil)
```

To use a different recentering logic, for example `recenter-top-bottom`, use the following:

```elisp
(setq imenu-list-after-jump-hook nil)
(add-hook 'imenu-list-after-jump-hook #'recenter-top-bottom)
```

## Automatic Update

When `imenu-list-minor-mode` is enabled, the `*Ilist*` buffer is updated automatically whenever the user is idle, with a default delay time of 0.5 seconds. To change the delay time, set the value of `imenu-list-idle-update-delay-time`.

## Display
imenu-list has several faces for showing different levels of nesting in the `*Ilist*` buffer. To customize them, see `M-x customize-group RET imenu-list RET`.

The mode-line of `*Ilist*` buffer can be changed by customizing `imenu-list-mode-line-format`, also available via `M-x customize-group RET imenu-list RET`.

Here are some pictures. Note that you can hide/show parts of the imenu list.

![](https://github.com/bmag/imenu-list/blob/master/images/imenu-list-light.png)

![](https://github.com/bmag/imenu-list/blob/master/images/imenu-list-dark.png)

## Window Position and Size
The size and position of `*Ilist*` window can be changed by customizing these variables:
- `imenu-list-position`: should be `left`, `right`, `above` or `below`, to display the window
at the left, right, top or bottom of the frame.
- `imenu-list-size`: should be a positive integer or a percentage. If integer, decides the total
number of rows/columns the window has. If percentage (0 < `imenu-list-size` < 1), decides the
number of rows/columns relative to the total number of rows/columns in the frame.

imenu-list controls its display by adding an entry to `display-buffer-alist`. If you want
fuller control over how the window is displayed, you should replace that entry.

If imenu-list can't open a new window (could happen when the frame is small or already split into many windows),
the window will be displayed using the regular rules of `display-buffer`.

### window-purpose
For users of `window-purpose`, imenu-list adds an entry to `purpose-special-action-sequences`.
If you want fuller control over how the window is displayed, you should replace that entry.
