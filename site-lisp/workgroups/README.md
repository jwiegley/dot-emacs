# Workgroups for Windows (for Emacs)

It's tedious setting Emacs' window layout just the way you like it -- splitting
windows, adjusting their size, switching to the right buffers, etc.  And even
when it *is* set, it won't stay that way for long.  On top of that, you can't
save your window-configurations to disk, so you have to start over from scratch
every time you restart Emacs.

There are solutions out there to parts of the problem -- elscreen, revive.el,
window-configuration-to-register, etc. -- but none provide a complete solution.
Workgroups does.

With Workgroups, you can:

- Store an unlimited number of window configs

- Save window configs to disk, and load them from disk

- Kill and yank window configs

It also provides:

- Animated window config morphing

- Frame reversing and window movement

- A concept of "base" and "working" configs, for maximum flexibility

- Lots of other stuff


## Background

Workgroups is a window configuration management package for GNU Emacs.  Here's
what the Elisp info docs have to say about window configurations `(info
"(Elisp)Window Configurations")`:

> A "window configuration" records the entire layout of one frame--all windows,
> their sizes, which buffers they contain, how those buffers are scrolled, and
> their values of point and the mark; also their fringes, margins, and scroll
> bar settings.  It also includes the value of `minibuffer-scroll-window'.  As a
> special exception, the window configuration does not record the value of point
> in the selected window for the current buffer.  Also, the window configuration
> does not record the values of window parameters; see *Note Window
> Parameters::.

The problem with Emacs' window configurations is that they're opaque C types:
you can't peer inside them.  To get at the information in a window
configuration, you must restore it in a frame, then access that frame's
parameters.

Here's what the same info node has to say about window configuration opacity:

> Other primitives to look inside of window configurations would make sense, but
> are not implemented because we did not need them.

Workgroups solves this problem by implementing an independent window
configuration object.  Workgroups' window configurations (called "wconfigs")
save all the settings listed above, and more.  For instance, if a region is
highlighted in `transient-mark-mode`, that region will still be highlighted
after restarting Emacs and restoring that wconfig.  They also save frame
position and size.  And wconfigs can be constructed and manipulated
programatically, without the need to restore them in a live frame, enabling
things like frame morphing, window moving, frame reversing and other operations.


## Getting Workgroups

The latest version of Workgroups can always be found
[here](http://github.com/tlh/workgroups.el). You can clone the repo by running:

    git clone git://github.com/tlh/workgroups.el

Workgroups is being actively developed.  Later on, when you want to update to
the latest:

    git fetch
    git merge origin


## Installation

- Put `workgroups.el` somewhere on your Emacs load path

- Byte-compile `workgroups.el`.  This isn't required, but it'll speed some
  things up:

        M-x byte-compile-file RET /path/to/workgroups.el RET

- Add this line to your `.emacs` file:

        (require 'workgroups)


## Configuration

- Set your prefix key (or not).  The prefix key for Workgroups' commands
  defaults to `C-z`.  You could set it to `C-c w` like this:

        (setq wg-prefix-key (kbd "C-c w"))

  Workgroups saves the prefix key's current definition when it's enabled, and
  restores it when it's disabled, so you don't have to worry about stomping
  keydefs if you want to try out different prefixes.

  Most commands are bound to both `<prefix> <key>` and `<prefix> C-<key>` for
  convenience.  See the definition of `wg-map` in the source for a complete list
  of bindings.

- There are many other customization options.  See the customization section in
  the source for details, or use:

        M-x customize-group RET workgroups RET


## Usage

- Turn on `workgroups-mode` either by issuing the command:

        M-x workgroups-mode RET

  or by evaluating this form, which can be added to your `.emacs` file:

        (workgroups-mode 1)

  You should see "wg" in the minor mode list on the mode-line.

- To get started right away, hit `<prefix> ?` for a list of commands and their
  bindings.


## Tutorial

### Workgroup Creation

To start off, add a few workgroups.  Hit `<prefix> c` to issue the command
`wg-create-workgroup`, give it a name, hit `RET`, and a new workgroup is
created.  Maybe split the screen a few times with `C-x 2` and `C-x 3`, and
switch to different buffers in some of the windows to make it unique.  Repeat
this process a few times to create some different workgroups.

Every workgroup must have a unique name.  You can rename workgroups after
they've been created with `<prefix> A` (`wg-rename-workgroup`).


### Workgroup Switching

`<prefix> v` issues the command `wg-switch-to-workgroup`.  This will do a
completing-read (with
[ido](http://www.emacswiki.org/emacs/InteractivelyDoThings) if it's enabled) on
the available workgroup names, and switch to the workgroup with that name.
`<prefix> n` will switch to the workgroup rightward in the workgroups list from
the current workgroup, and `<prefix> p` will switch to the one leftward in the
list.  `<prefix> 0` through `<prefix> 9` switch to the workgroup at that
position in the workgroups list.  Try switching between your workgroups now.


### Morph

After you've switched between workgroups, you'll notice that Workgroups animates
the transition between wconfigs.  "Morph" reuses whatever tree structure the two
window trees have in common, sliding in or wiping subtrees as necessary to
complete the transformation.  You can toggle it off and on with `<prefix> w`
(`wg-toggle-morph`), or you can set the value of `wg-morph-on` to t or nil to
turn it on or off permenently.

There are a couple variables that determine morph speed.  `wg-morph-hsteps` and
`wg-morph-vsteps` control the number of columns and lines respectively that
window boundaries move for each step of the morph transition.  The defaults for
these are a little low, so that you can see what morph is doing.  You can set
them as high as you like, but values less than 1 are invalid.

There are separate horizontal and vertical step values used in terminal frames
(`wg-morph-terminal-hsteps` and `wg-morph-terminal-vsteps`).  This is because
Emacs' `redisplay` is usually significanly faster on local terminal frames, so
morphing can happen too fast to see at values appropriate for GUI frames.  If
they are set, their values are used in terminal frames.  If they are nil, the
step values default to `wg-morph-hsteps` and `wg-morph-vsteps`.

*NOTE on morphing in xterm*

xterm has some wierd redisplay issues:

- An unset background color can cause *extremely* slow `redisplay` in xterm.  So
  if:
 
        (frame-parameter (selected-frame) 'background-color)

  returns:

        => "unspecified-bg"

  you may run into this.

- Very large terminal geometries (270x70 or higher) can also cause very slow
  `redisplay` in xterm. Until I figure out the best way to handle this, you
  should just see what works, and either set your background color or turn off
  morphing with:

        `(setq wg-morph-on nil)`


### Base and Working Configs

Window configs drift through use. Windows get resized; different buffers get
selected; point and mark change, and so on.  When you switch from one workgroup
to another, then back to the first, you want it to be in the same state that you
left it in so you don't lose your place.  At the same time, it can be tedious
getting the window configuration just the way you like it, and it sucks when it
gets mangled, so it'd be nice to be able to revert it back to a known-good state
at any time.

For this reason, every workgroup actually consists of two wconfigs: a base
config and a working config [1].  The base config is the pristine original
wconfig, set exactly the way you like it.  And the working config is whatever
the frame happens to look like while you're using it [2].  The base config only
gets altered explicitly, and you can revert back to it at any time.  Use
`<prefix> r` (`wg-revert-workgroup`) to revert the working config to the base
config.  The opposite of reverting is updating.  `<prefix> u`
(`wg-update-workgroup`) updates the base config with the current working config.

So the two commands are mirror images of each other: the former sets the working
config to the base config (reverting the working config), and the latter sets
the base config to the working config (updating the base config).  You can
revert all workgroups' working configs to their base configs with `<prefix> R`
(`wg-revert-all-workgroups`), and you can update all workgroups' base configs to
their working configs with `<prefix> U` (`wg-update-all-workgroups`).  Update
all your workgroups with `<prefix> U` now.

It's important to understand that you never actually *use* the base config --
only the working config.  The base config sits in the background, and can only
be modified with explicit updates.

[1] That's not entirely true: working configs are actually properties of frames,
so every frame has its own working config for each workgroup.  This is because
when working with multiple frames, one expects the working config to remain the
same in that frame.  If you move to another frame and modify a workgroup's
working config, then switch back to the first frame, it doesn't feel right when
the working config has changed while you were gone.  This may seem complicated,
but in practice it's very natural.  There's only one base config per workgroup,
though -- they're the same across all frames.

[2] Workgroups updates working configs lazily: it doesn't update the working
config every time changes are made to the frame -- only when the working config
is requested by a function.  This produces the same behavior as more tedious
perpetual updates, but much simpler code.


### Saving and Loading

Saving and loading was the original motivation for writing Workgroups.  You can
save your workgroups to a file with `<prefix> C-s` (`wg-save`) and you can load
workgroups from a file with `<prefix> C-l` (`wg-load`).  Save your workgroups
now.

Once you have a file of saved workgroups, it's convenient to load it on Emacs
startup.  To do so you can add a line like this to your `.emacs`:

    (wg-load "/path/to/saved/workgroups")

So your final `.emacs` setup may look something like this:

    (add-to-list 'load-path "/path/to/workgroups.el")
    (require 'workgroups)
    (setq wg-prefix-key (kbd "C-c a"))
    (workgroups-mode 1)
    (wg-load "/path/to/saved/workgroups")

The customization variable `wg-switch-on-load` controls whether to automatically
switch to the first workgroup in a file when the file is loaded.  It defaults to
`t`, so when you add the above to your `.emacs` file, the first workgroup in the
file will automatically be switched to on Emacs startup.


### Killing and Yanking

You can kill workgroups with `<prefix> k` (`wg-kill-workgroup`).  Killing a
workgroup deletes it from the list of workgroups, and copies its working config
to the kill ring.  You can yank killed wconfigs into the current frame with
`<prefix> y` (`wg-yank-config`).  If the last command was `wg-yank-config`,
calling it again will yank the *next* wconfig in the kill ring, and so on, much
like Emacs' own kill ring.

You can save a wconfig to the kill ring without killing its workgroup with the
kill-ring-save commands.  `<prefix> M-w` (`wg-kill-ring-save-working-config`)
saves the working config to the kill ring, and `<prefix> M-W`
(`wg-kill-ring-save-base-config`) saves the base config to the kill ring.

`<prefix> M-k` (`wg-kill-workgroup-and-buffers`) kills a workgroup, and all the
buffers visible in it, and `<prefix> K` (`wg-delete-other-workgroups`) deletes
all but the current workgroup.


### Cloning

Cloning a workgroup creates a new workgroup under a different name with the a
copy of the current workgroup's base and working configs.  `<prefix> C`
(`wg-clone-workgroup`) will clone the current workgroup.


### Offsetting and Swapping

You can move a workgroup leftward or rightward in the workgroups list with
`<prefix> ,` (`wg-offset-left`) and `<prefix> .` (`wg-offset-right`)
respectively.  These commands work cyclically, so when you offset a workgroup
leftward or rightward when it's already on the far left or right of the list, it
will wrap around to the other side.

`<prefix> x` (`wg-swap-workgroups`) will swap the position in the workgroups
list of the previously selected workgroup with that of the current workgroup.


### Switching to Buffers

You can switch to workgroups based on the buffers that are visible in them with
`<prefix> b` (`wg-get-by-buffer`).  Workgroups constructs the list of available
buffer names from the workgroups list, so it's possible to switch to a workgroup
determined from a buffer file-name that hasn't been visited yet, if you haven't
switched to that workgroup yet in your current Emacs session.


### Messaging

Workgroups has commands to display various bits of information in the echo-area,
like the current workgroup name, the list of workgroups, the current time, etc.
The help buffer has a complete list (see the Help section below).


### Help

To bring up a help buffer listing all the commands and their bindings, hit
`<prefix> ?` (`wg-help`).


## FAQ

**Q:** Does Workgroups for Windows have anything to do with Microsoft Windows
  for Workgroups?  
**A:** Nope.  

**Q:** Why is it called "Workgroups"?  
**A:** Mostly because it's funny, but it also makes sense.  I needed a name that
  would also work for the collections of wconfigs being manipulated.  Elscreen
  has "screens", which works well.  I couldn't call them "window configurations"
  because it's too long, and Emacs already uses that for something else.  It'd
  be misleading, too, since a workgroup is actually a named set of multiple
  wconfigs (one base config, and then a working config for each frame).
  "Workgroup" seemed like a good name for such a collection of window
  configurations, and, thanks to Microsoft, the word "workgroups" is already
  associated with the word "windows".  So "Workgroups" it is.  I'll have to do
  something special for the 0.3.11 release.

**Q:** Why should I use Workgroups instead of Elscreen?  
**A:** Workgroups provides persistence, base and working configs, morphing,
  frame-reversing and other chrome, unlimited workgroups per frame and cleaner
  code.  And it's maintained.

**Q:** What's the difference between a "window configuration", a "wconfig" and a
  "workgroup"?  
**A:** A "window configuration" is Emacs' opaque internal representation of most
  of the state of one frame.  A "wconfig" is Workgroups' independent,
  translucent window configuration object.  And a "workgroup" is a named set of
  multiple wconfigs (one base config, and then a working config for each frame).


## Feature Requests

Feature requests, like other parameters you'd like Workgroups to persist, should
be added to the [wiki](http://github.com/tlh/workgroups.el/wiki)


## Reporting Bugs

If you encounter a bug in Workgroups, please file an issue
[here](http://github.com/tlh/workgroups.el/issues).  If possible, please include
a stack-trace and the value of `wg-list`.


## A Note On Application Buffers

Workgroups doesn't currently save the state of applications like ERC or Gnus,
though this is on the TODO list.  If you save a workgroup that includes
application buffers, and then you restore that workgroup in another Emacs
session before relaunching those applications and buffers, Workgroups will just
default to `*scratch*`.  To get back to your saved state, launch those
applications and buffers and hit `<prefix> R` to `wg-revert-all-workgroups`.


## License

Copyright (C) 2010 tlh Workgroups for Windows (for Emacs) is released under the
GPL.  See the file `workgroups.el`.
