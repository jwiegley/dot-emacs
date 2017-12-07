# Purpose

[![MELPA](http://melpa.org/packages/window-purpose-badge.svg)](http://melpa.org/#/window-purpose)
[![MELPA Stable](http://stable.melpa.org/packages/window-purpose-badge.svg)](http://stable.melpa.org/#/window-purpose)
[![Build Status](https://travis-ci.org/bmag/emacs-purpose.svg?branch=master)](https://travis-ci.org/bmag/emacs-purpose)
[![Coverage Status](https://coveralls.io/repos/bmag/emacs-purpose/badge.svg?branch=master)](https://coveralls.io/r/bmag/emacs-purpose?branch=master)

**Note: a full explanation can be found in the [GitHub wiki](https://github.com/bmag/emacs-purpose/wiki).**

## Introduction

Purpose ("window-purpose" on MELPA) provides a new window management system for
Emacs, which gives you a better control over where Emacs displays buffers.

With Purpose, each buffer has a configurable "purpose" and each window
can interactivaly be dedicated to a certain "purpose". When you dedicate
a window (<kbd>C-c , d</kbd>), Purpose makes sure that this window will be used
only for buffers which have the same purpose as the buffer that is
currently displayed in that window. The purpose of a buffer can be
customized via the variables `purpose-user-mode-purposes`,
`purpose-user-name-purposes`, `purpose-user-regexp-purposes` and
`purpose-use-default-configuration` (see the
[wiki](https://github.com/bmag/emacs-purpose/wiki/Purpose-Configuration)).

### Supported Emacs Versions
Purpose is tested with Emacs versions 24.3, 24.4 and 24.5. Backward-compatibility for earlier versions might be added in the future - if you want such support, contact me.

## Quickstart

### Activate Purpose
Manually: <kbd>M-x purpose-mode</kbd>

In your init file:
```elisp
(require 'window-purpose)
(purpose-mode)
```

### Configure Purpose
Manually: <kbd>M-x customize-group purpose</kbd>. Look at:
- "Purpose User Mode Purposes": recognize purpose according to major mode
- "Purpose User Name Purposes": recognize purpose according to buffer
  name (for exact names)
- "Purpose User Regexp Purposes": recognize purpose according to buffer
  name (for name patterns)
- "Purpose Use Default Configuration": toggle default configuration
  on/off

In init file:
```elisp
(add-to-list 'purpose-user-mode-purposes '(<major-mode> . <purpose>))
(add-to-list 'purpose-user-name-purposes '(<name> . <purpose>))
(add-to-list 'purpose-user-regexp-purposes '(<pattern> . <purpose>))
(setq purpose-use-default-configuration t) ; not really necessary, default is t
(purpose-compile-user-configuration) ; activates your changes
```

### Useful Commands
| Key         | Command                                                                                                                   |
| :---------- | :------------------------------------------------------------------------------------------------------------------------ |
| <kbd>C-c , b</kbd>   | `purpose-switch-buffer-with-purpose`: switch to a buffer with the same purpose as the current one                         |
| <kbd>C-u C-x b</kbd> | `switch-buffer-without-purpose`: switch to a buffer, but don't use Purpose for it. Handy for changing the current layout. |
| <kbd>C-c , d</kbd>   | `purpose-toggle-window-purpose-dedicated`                                                                                 |
| <kbd>C-c , D</kbd>   | `purpose-toggle-window-buffer-dedicated`                                                                                  |
| <kbd>C-c , 1</kbd>   | `purpose-delete-non-dedicated-windows`                                                                                    |
|             | `purpose-save-window-layout`: save current layout (by name)                                                                |
|             | `purpose-load-window-layout`: load layout (by name)                                                                       |
|             | `purpose-save-window-layout-file`: save current layout directly to file                                                                |
|             | `purpose-load-window-layout`: load layout directly from file                                                                       |
|             | `purpose-reset-window-layout`: reload previously loaded layout                                                            |

### Example: Simple Python Layout
How to get a simple and persistent layout for coding in Python that
looks like this:

![simple python layout](https://github.com/bmag/emacs-purpose/blob/master/images/simple-python-layout.png)

#### step 1: configuration
```elisp
(add-to-list 'purpose-user-mode-purposes '(python-mode . py))
(add-to-list 'purpose-user-mode-purposes '(inferior-python-mode . py-repl))
(purpose-compile-user-configuration)
```

#### step 2: change window layout
If you have a previously saved layout, you can load it with
`purpose-load-window-layout` and skip step 2 and step 3.

1. open a Python file
2. <kbd>C-c , d</kbd> (`purpose-toggle-window-purpose-dedicated`) so window is
   dedicated ("[py]" in the status bar will change to "[py!]")
3. <kbd>C-x 1</kbd> (`delete-other-windows`)
4. <kbd>C-x 2</kbd> (`split-window-below`)
5. <kbd>C-c C-z</kbd> (`python-shell-switch-to-shell`)
6. <kbd>C-c , d</kbd> so window is dedicated
7. <kbd>C-x o</kbd> (`other-window`) to select the python file's window
8. <kbd>C-x ^</kbd> (`enlarge-window`) until you like the sizes of the windows

#### step 3: save window layout
<kbd>M-x purpose-save-window-layout</kbd>

## Using Purpose

### Dedicating windows
Dedicating a window limits which buffers will be displayed in it. There are two
types of window dedication: buffer-dedication and purpose-dedication.

Use `purpose-toggle-window-buffer-dedicated` to dedicate a window to its buffer.
This window will not display any other buffer while it is buffer-dedicated. A
"#" in the mode-line next to the window's purpose indicates that the window is
buffer-dedicated.

Use `purpose-toggle-window-purpose-dedicated` to dedicate a window to its
purpose. This window will only display buffers with the same purpose. A "!" in
the mode-line next to the window's purpose indicates that the window is
purpose-dedicated.

You can delete all non-dedicated windows by using
`purpose-delete-non-dedicated-windows`.

### Switching buffers
When switching buffers, Purpose will display the new buffer in the correct
window, according to the current configuration.

Use `switch-to-buffer` to switch to any buffer. The buffer will be displayed
according to the current purpose-configuration.

Use `purpose-switch-buffer-with-purpose` to switch to another buffer with the
same purpose as the current buffer.

Use `purpose-switch-buffer-with-some-purpose` to select a purpose and then
switch to a buffer with that purpose.

Use `switch-buffer-without-purpose` to switch to any buffer. The buffer will be
displayed using Emacs' original behavior. This is useful when you want to change
the window layout.

Use `purpose-set-window-purpose` to switch the purpose of the current window. If
there is a buffer with the chosen purpose, that buffer will be displayed in the
current window. Otherwise, a dummy buffer will be created and used.

### Changing layout
Purpose lets you save, load and reset the window layout.

Use `purpose-save-window-layout` to save the current window layout. The layout
will be saved in a directory of your choice, in a file named
`<layout-name>.window-layout`.

Use `purpose-load-window-layout` to load a window layout. The available layouts
are located the directories specified in customizable variable `purpose-layout-dirs`.

Use `purpose-save-window-layout-file` to save the current window layout directly to
a file of your choice.

Use `purpose-load-window-layout-file` to load a window layout directly from a file
of your choice.

Use `purpose-reset-window-layout` to reset the window layout to the latest
layout that you loaded.

In addition to window layouts, Purpose also lets save, load and reset the frame
layout. A "frame layout" consists of the window layouts of multiple frames.
All of the window layout commands have frame layout equivalents, e.g.
`purpose-load-frame-layout` is equivalent to `purpose-load-window-layout`.

## Customizing Purpose

### Prompts
With `purpose-preferred-prompt`, you can choose whether you want Purpose to use
IDO or Helm when it needs information from the user. By default, when both IDO
and Helm are enabled, Purpose prefers IDO.

### Changing purpose configuration
Purpose lets you define your own purposes. You can do so by using the variables
`purpose-user-mode-purposes`, `purpose-user-name-purposes` and
`purpose-user-regexp-purposes`. You can also deactivate the default purpose
configuration if it bothers you, by setting `purpose-use-default-configuration`
to nil.

### Changing display rules
If you want, you can the rules of how certain buffers are displayed. To do so,
use the variable `purpose-special-action-sequences`. Let's explain this with an
example. The following code makes all help buffers appear in a separate
frame. This means you will get a "popup" frame for help buffers.

```elisp
(setq pop-up-frames t) ; allows emacs to popup new frames
;; give help buffers the 'popup-frame purpose
(add-to-list 'purpose-user-mode-purposes
             '(help-mode . popup-frame))
(purpose-compile-user-configuration)
;; new rules for buffers with the 'popup-frame purpose
(add-to-list 'purpose-special-action-sequences
             '(popup-frame
               purpose-display-reuse-window-buffer
               purpose-display-reuse-window-purpose
               purpose-display-pop-up-frame))
```

### Respect purposes when killing a buffer
When killing a visible buffer, Emacs has to decide which buffer to show instead.
Enabling the `purpose-x-kill` extension will make Emacs consider the purpoes of
the window that needs to show a new buffer. If the window is purpose-dedicated,
the killed buffer is replaced with another buffer with the same purpose. If there
are no buffers with the same purpose as the killed buffer, the window is deleted.
To enable the `purpose-x-kill` extension:

```elisp
(require 'window-purpose-x)
(purpose-x-kill-setup)
```

### Location of Layout Files
Window layout and frame layout files are stored in the directories specified by
`purpose-layout-dirs`. By default, its value is `("~/.emacs.d/layouts/")`. To store
layouts in a different location, simply change the value of this variable.

## Using Purpose with other packages
See [Integration With Other Packages](https://github.com/bmag/emacs-purpose/wiki/Integration-With-Other-Packages)
for information about how some packages relate to Purpose.
