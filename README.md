# Writeroom-mode #

`writeroom-mode` is a minor mode for Emacs that implements a distraction-free writing mode similar to the famous Writeroom editor for OS X. `writeroom-mode` is meant for GNU Emacs 24, lower versions are not actively supported.


## Installation ##

`writeroom-mode` can be installed through the package manager from [Melpa](http://melpa.org/). If installing manually, make sure to also install its dependency [`visual-fill-column`](https://github.com/joostkremers/visual-fill-column).


## Usage ##

`writeroom-mode` can be activated in a buffer by calling `M-x writeroom-mode RET`. By default, `writeroom-mode` does the following things:

* activate fullscreen
* disable transparency
* disable the menu bar
* disable the tool bar
* disable the scroll bar
* enable a bottom window divider of 1 pixel
* maximise the current window (i.e., delete all other windows in the frame)
* place the fringes outside the margins
* disable the mode line
* add window margins to the current buffer so that the text is 80 characters wide

The last three effects are buffer-local. The other effects apply to the current frame. Because `writeroom-mode` is a minor mode, this isn't entirely on the up and up, since minor modes aren't supposed to have such global effects. But `writeroom-mode` is meant for distraction-free writing, so these effects do make sense.

All these effects can be disabled or customised. In addition, there are several more options that are disabled by default but can be enabled in the customisation buffer.


## Multiple writeroom-mode buffers ##

It is possible to activate `writeroom-mode` in more than one buffer. The global effects are of course activated only once and they remain active until `writeroom-mode` is deactivated in *all* buffers. Alternatively, if you wish to use `writeroom-mode` in all buffers that have a particular major mode (e.g., `text-mode`, `markdown-mode`), you can use the global minor mode `global-writeroom-mode`. This function enables the global effects and activates the buffer-local effects in all (current and future) buffers that have a major mode listed in the user option `writeroom-major-modes` (by default only `text-mode`).

When `global-writeroom-mode` is active, the function `writeroom-mode` can still be called to enable or disable `writeroom-mode` in individual buffers (regardless of their major mode, of course). Calling `global-writeroom-mode` again disables `writeroom-mode` in all buffers in which it is active, also those in which it was activated manually.


## Frame effects ##

Most of the global effects that `writeroom-mode` enables are handled by setting specific frame parameters. This means that they apply to the current frame. If you switch to another frame and display a `writeroom-mode` buffer, only the buffer-local effects will be visible.

`writeroom-mode` tries to make sure that it only affects one frame, and that it restores that particular frame when it is deactivated in the last buffer. This means it should be safe to activate `writeroom-mode` in one frame and deactivate it in another. Killing the `writeroom-mode` frame should also be safe.

The affected frame is always restored to its original state, before `writeroom-mode` was activated, even if you change any of the frame parameters manually while `writeroom-mode` is active.


## Customisation ##

### Global Writeroom Mode ###

Activate this option to automatically turn on `writeroom-mode` in any buffer that has one of the major modes matched any mask listed in `writeroom-major-modes` and not in ‘writeroom-major-modes’.


### Border Width ###

Width of the border around the text area. Disabled by default, see `writeroom-global-effects` to enable the border.


### Extra Line Spacing ###

Increase the line spacing. Can be an absolute value (the number of pixels to add to the line) or a number relative to the default line height. Disabled by default.


### Fringes Outside Margins ###

If set, place the fringes outside the margins. `writeroom-mode` expands the window margins, causing the fringes to be pushed inside, which may be visually distracting. This option keeps the fringes at the window’s edges. Unset it if you prefer to have the fringes close to the text.


### Fullscreen Effect ###

Effect to apply when `writeroom-mode` activates fullscreen. Can be `fullboth`, which uses the entire screen (i.e., window decorations are disabled and the window manager’s panel or task bar is covered by the Emacs frame) or `maximized`, in which case the Emacs frame is maximised but keeps its window decorations and does not cover the panel.


### Bottom Divider Width ###

Width in pixels of the bottom window divider. Default value is 1. The bottom window divider helps in distinguishing the minibuffer from the text area, and also in distinguishing two windows split top-to-bottom.


### Global Effects ###

List of global effects:

- fullscreen
- transparency
- scroll bar
- menu bar
- tool bar
- bottom window divider
- border (add a border around the text area; disabled by default)
- sticky (display the window on all virtual workspaces; disabled by default)

Each option can be enabled or disabled individually.


### Major Modes ###

List of major modes in which `writeroom-mode` should be activated automatically. Use in conjunction with `global-writeroom-mode`.

The elements in this list can be major-mode symbols, or regular expressions (in which case they must of course be strings).


### Use Derived Modes ###

If this option is set, `global-writeroom-mode` also activates `writeroom-mode` in buffers whose major mode is a derived mode of one of the modes in `writeroom-major-modes`. (Only the major mode symbols in `writeroom-major-modes` are relevant.)


### Major Modes Exceptions ###

List of major modes in which `writeroom-mode` should not be activated by `global-writeroom-mode`. (It is still possible to activate `writeroom-mode` manually). This can also be a mixed list of major-mode 
symbols and regular expressions.


### Maximize Window ###

Maximise the current window in its frame, i.e., delete all other windows.


### Mode Line ###

The mode line format to use. This option can be `nil`, which disables the mode line altogether (which is the default), it can be `t`, which retains the mode line, or it can be set to a customised format to only show some information. If the latter option is chosen, the mode line shows only the file name and the file modification status, but the format can be customised. See the documentation for the variable `mode-line-format` for details. If you set this option, it may be more visually pleasing to set the option Bottom Divider Width to 0.


### Mode Line Toggle Position ###

If you disable or customise the mode line, you may sometimes want to see the entire mode line. `writeroom-mode` provides the function `writeroom-toggle-mode-line` (see below) to do this. You can specify where you want to make the mode line visible when using this function: in the mode line itself, or in the header line.

Note that the default value of this option is to display the mode line in the header line, because for some reason that is more reliable. (Toggling the mode line multiple times in a row does not always work very well.)


### Restore Window Config ###

Restore the window configuration that existed before `writeroom-mode` was activated. This is primarily useful if you use `writeroom-mode` in only a single buffer, since the window configuration that is restored is the one that existed at the moment when `writeroom-mode` is called for the first time. Disabled by default.


### Width ###

Width of the text area. Can be specified as an absolute value (number of characters) or as a fraction of the total window width (in which case it should be a number between 0 and 1).


## Changing the width interactively ##

The width of the text area in the current buffer can be changed interactively with the commands `writeroom-increase-width` and `writeroom-decrease-width`, which increase and decrease the text width by 2 characters. There is also a more general command `writeroom-adjust-width`, which adjusts the width of the text area by the amount passed as prefix argument. That is, calling it with `M-5 M-x writeroom-adjust-width` increases the text width by 5 characters. Calling `writeroom-adjust-width` without prefix argument resets the width to the default value.

These commands are not bound to any keys, but you can bind them in the following manner (the actual keys are just examples, of course; choose any keys you like):

```lisp
(with-eval-after-load 'writeroom-mode
  (define-key writeroom-mode-map (kbd "C-M-<") #'writeroom-decrease-width)
  (define-key writeroom-mode-map (kbd "C-M->") #'writeroom-increase-width)
  (define-key writeroom-mode-map (kbd "C-M-=") #'writeroom-adjust-width))
```


## Text size adjustments ##

Text size adjustments are taken into account in calculating the margins, which means that if the text size is increased, the margins are decreased, so that the number of characters on the line remains more or less the same. Since it is not possible to detect interactive text size adjustments (e.g., with `text-size-adjust`), the adjustments of the margins cannot be made automatically. You need to force a redisplay, e.g., with the command `redraw-display`.

Alternatively, you can advise the command you use for adjusting the text size (most likely `text-size-adjust`):

    (advice-add 'text-scale-adjust :after
      #'visual-fill-column-adjust)


## Displaying the mode line ##

By default, `writeroom-mode` disables the mode line. If you occasionally need to see the full mode line, you can use the command `writeroom-toggle-mode-line`, which makes the mode line visible. Calling it again hides the mode line. This command is bound to `s-?` (`s` is the super key, i.e., the Windows key on PCs, the ⌘ key on Macs), but it can be rebound by putting something like the following in your `init.el`:

```lisp
(with-eval-after-load 'writeroom-mode
  (define-key writeroom-mode-map (kbd "s-?") nil)
  (define-key writeroom-mode-map (kbd "<some-key>") #’writeroom-toggle-mode-line))
```

The first `define-key` disables the binding for `s-?`. Substitute your preferred key binding in the second line to bind `writeroom-toggle-mode-line` to it.


## Adding global effects ##

It is possible to add your own global effects to `writeroom-mode`. If there is a global minor mode that you want turned on when `writeroom-mode` is activated for the first time, you can simply add it to the user option `writeroom-global-effects` by checking the box "Custom effects", clicking the [INS] button and adding the function to the list.

Alternatively, you can also write your own function. This function should take one argument and enable the effect if the argument is `1` and disable it if the argument is `-1`. To give an example, if you want to activate a minimalist colour theme in `writeroom-mode`, you can write the following function:

```lisp
(defun my-writeroom-theme (arg)
  (cond
   ((= arg 1)
    (enable-theme 'minimalist-dark))
   ((= arg -1)
    (disable-theme 'minimalist-dark))))
```

If your function affects the frame, you should make sure that it only affects the `writeroom-mode` frame by passing the variable `writeroom--frame` to all frame-changing functions. If your frame effect involves changing the value of a frame parameter, you may be able to use the macro `define-writeroom-global-effect`; see its doc string for details.

In principle, it is not a good idea to define a custom global effect function as a toggle, but if you are sure you'll only ever use a single frame, it should be safe enough. For example, sometimes setting the `fullscreen` frame parameter does not work. In this case, if you're on Linux, you could send an X client message directly:

```lisp
(defun my-toggle-fullscreen (_)
  (x-send-client-message nil 0 nil "_NET_WM_STATE" 32
                         '(2 "_NET_WM_STATE_FULLSCREEN" 0)))
```


## Other similar modes ##

There are two other modes that I know of that also implement a distraction-free writing environment: [Darkroom](https://github.com/joaotavora/darkroom) and [Olivetti](https://github.com/rnkn/olivetti). Both are narrower in scope than `writeroom-mode`.

In particular, both Darkroom and Olivetti only affect the buffer (or more precisely, its window), not the frame. They centre the text by adding window margins, and optionally resize the text and hide the mode line. They do not make Emacs fullscreen and do not remove the menu and tool bars, the scroll bar or the window decorations. This is a conscious choice (see, e.g., [this pull request](https://github.com/joaotavora/darkroom/pull/2) and [this issue](https://github.com/rnkn/olivetti/issues/6)), motivated by the fact that affecting the frame in this way may lead to problems when using multiple Emacs frames.

It is true that changing the appearance of the current frame (the global effects, as `writeroom-mode` calls them) is risky if you use multiple frames. `writeroom-mode` applies its global effects to the frame that is current when it is first activated and tries to make sure that *only* this frame is ever affected. Therefore, it should be safe to use `writeroom-mode`, even if you use multiple frames. (If you do run into issues, however, I would welcome a bug report.) Alternatively, you can turn off all global effects and use `writeroom-mode` in much the same way as Darkroom or Olivetti.

Another difference with Darkroom and Olivetti is that `writeroom-mode` tries to be as customisable as possible. It has a larger number of customisation options than either of the other modes and also provides a way to add custom global effects. This may or may not be what you need, of course.
