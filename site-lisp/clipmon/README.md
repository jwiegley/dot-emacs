
clipmon.el [![Travis build status](https://secure.travis-ci.org/bburns/clipmon.png?branch=master)](http://travis-ci.org/bburns/clipmon) [![melpa.org](http://melpa.org/packages/clipmon-badge.svg)](http://melpa.org/#/clipmon) [![GPL-3.0](http://img.shields.io/:license-gpl-blue.svg)](http://opensource.org/licenses/GPL-3.0)
----------------------------------------------------------------------------


Description
----------------------------------------------------------------------------

Clipmon is a clipboard monitor - it watches the system clipboard and can
automatically insert any new text into the current location in Emacs.

It also adds changes to the system clipboard to the kill ring, making Emacs
into a clipboard manager for text - you can then use a package like
browse-kill-ring or helm-ring to view and manage your clipboard history.

**Warning (2015-12-24): in an X-windows system with clipmon-mode on, bringing
  up a graphical menu (e.g. Shift+Mouse-1) will cause Emacs to hang. See
  http://debbugs.gnu.org/cgi/bugreport.cgi?bug=22214.
  X-windows starts a timer when checking the contents of the clipboard, which
  interferes with the clipmon timer.**

Update (2016-01-27): in an X-windows system, Clipmon now uses the clipboard
instead of the primary selection - see https://github.com/bburns/clipmon/issues/4.

You can use Clipmon for taking notes from a webpage, for example - just copy the
text you want to save and it will be added to Emacs. It helps to have an
autocopy feature or addon for the browser, e.g. AutoCopy 2 for Firefox - then
you can just select text to add it to Emacs.

Here's a diagram - text flows from the top to the bottom:

                 +---------------------+
                 |   Other programs    |+
                 +---------------------+|
                  +---------------------+
                          /
                    +-----------+
                    |  System   |
                    | clipboard |
                    +-----------+
    OS                /
    ---------------------------------------------------
    Emacs           /
                   /
          +--------------+      +---------------+
          | clipmon-mode |......|  autoinsert   |
          +--------------+      +---------------+
                  |                     .
            +-----------+               .
            | Emacs     ++              .
            | kill ring ++       +--------------+
            +-----------+|+      |  transforms  |
             +-----------+|      +--------------+
              +-----------+             .
                     |                  .
                     | yank             . autoinsert
                +--------------------------+
                |      Emacs buffer        |
                +--------------------------+


The solid line is turned on and off with `clipmon-mode`, while the dotted
line is turned on and off with `clipmon-autoinsert-toggle`, usually bound to a key.
There are also various transformations you can perform on the text, e.g.
adding newlines to the end.

(Emacs's kill-ring is like the system clipboard but with multiple items in
it. If you copy a bunch of things in another program, Emacs normally only
knows about the last one copied, but with clipmon mode on, it will monitor
the system clipboard and add any new text it sees to the kill ring.)


Installation
----------------------------------------------------------------------------

It's simplest to use the package manager:

    M-: (package-install 'clipmon)

It will then be ready to use, and will also be available the next time you
start Emacs.


Usage
----------------------------------------------------------------------------

To give it a try, do M-: (clipmon-autoinsert-toggle) - this will turn on
autoinsert. Then go to another application and copy some text to the
clipboard - clipmon should detect it after a second or two and make a beep.
If you switch back to Emacs, the text should be there in your buffer.

Note that you can still yank and pull text in Emacs as usual while autoinsert
is on, since it only monitors the system clipboard.

You can turn off autoinsert with the same command - to add a keybinding to it
add something like this to your init file:

    (global-set-key (kbd "<M-f2>") 'clipmon-autoinsert-toggle)

You can also turn it on and off from the Options menu.

Also, if no change is detected after a certain number of minutes, autoinsert will
turn itself off automatically with another beep. This is so you don't forget
that autoinsert is on and accidentally add text to your buffer.

And note: if you happen to copy the same text to the clipboard twice, clipmon
won't know about the second time, as it only detects changes. And if you copy
text faster than the timer interval is set it may miss some changes, but you
can adjust the interval.


Using as a clipboard manager
----------------------------------------------------------------------------

To try out clipmon as a clipboard manager, make sure clipmon-mode is on by
doing M-: (clipmon-mode 1) (also accessible from the Options menu) and that
autoinsert is off, then copy a few pieces of text from another program (more
slowly than the default timer interval of 2 seconds though). Switch back to
Emacs, and see that you can yank any of the text back with C-y, M-y, M-y...

Note that when you turn on autoinsert, it also turns on clipmon-mode, to
capture text to the kill ring, but if you'd like to turn on clipmon-mode
automatically, you can add this to your init file:

    ;; monitor the system clipboard and add any changes to the kill ring
    (add-to-list 'after-init-hook 'clipmon-mode-start)

You can also use the package browse-kill-ring to manage the kill ring - you
can install it with M-: (package-install 'browse-kill-ring), then call
`browse-kill-ring` to see the contents of the kill ring, insert from it,
delete items, etc. Helm also has a package called helm-ring, with the
function `helm-show-kill-ring`.

You can persist the kill ring between sessions if you'd like (though note
that this might involve writing sensitive information like passwords to the
disk - although you could always delete such text from the kill ring with
`browse-kill-ring-delete`). To do so, add this to your init file:

    ;; persist the kill ring between sessions
    (add-to-list 'after-init-hook 'clipmon-persist)

This will use Emacs's savehist library to save the kill ring, both at the end
of the session and at set intervals. However, savehist also saves various
other settings by default, including the minibuffer history - see
`savehist-mode` for more details. To change the autosave interval, add
something like this:

    (setq savehist-autosave-interval (* 5 60)) ; save every 5 minutes (default)

The kill ring has a fixed number of entries which you can set, depending on
how much history you want to save between sessions:

    (setq kill-ring-max 500) ; default is 60 in Emacs 24.4

To see how much space the kill-ring is taking up, you can call this function:

    (clipmon-kill-ring-total)
    => 29670 characters


Options
----------------------------------------------------------------------------

There are various options you can set with customize:

    (customize-group 'clipmon)

or set them in your init file - these are the default values:

    (setq clipmon-timer-interval 2)       ; check system clipboard every n secs
    (setq clipmon-autoinsert-sound t)     ; t for included beep, or path or nil
    (setq clipmon-autoinsert-color "red") ; color of cursor when autoinsert is on
    (setq clipmon-autoinsert-timeout 5)   ; stop autoinsert after n mins inactivity

before inserting the text, transformations are performed on it in this order:

    (setq clipmon-transform-trim t)        ; remove leading whitespace
    (setq clipmon-transform-remove         ; remove text matching this regexp
          "\\[[0-9][0-9]?[0-9]?\\]\\|\\[citation needed\\]\\|\\[by whom?\\]")
    (setq clipmon-transform-prefix "")     ; add to start of text
    (setq clipmon-transform-suffix "\n\n") ; add to end of text
    (setq clipmon-transform-function nil)  ; additional transform function


Todo
----------------------------------------------------------------------------

- Prefix with C-u to set a target point, then allow cut/copy/pasting from
  within Emacs, eg to take notes from another buffer, or move text elsewhere.


----

Author: Brian Burns  
URL: https://github.com/bburns/clipmon  
Version: 20160925  

This file was generated from commentary in clipmon.el - do not edit!

----

