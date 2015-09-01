ztree
=====

Ztree is a project dedicated to implementation of several text-tree applications inside Emacs. It consists of 2 subprojects: **ztree-diff** and **ztree-dir**(the basis of **ztree-diff**). Available in MELPA (http://melpa.milkbox.net/#/).

ztree-diff
==========
**ztree-diff** is a directory-diff tool for Emacs inspired by commercial tools like Beyond Compare or Araxis Merge. It supports showing the difference between two directories; calling **Ediff** for not matching files, copying between directories, deleting file/directories, hiding/showing equal files/directories.

The comparison itself performed with the external **GNU diff** tool, so make sure to have one in the executable path. Verified on OSX and Linux.

If one wants to have a stand-alone application, consider the (WIP)[zdircmp](https://github.com/fourier/zdircmp) project based on **ztree-diff**.

Add the following to your .emacs file:

```scheme
(push (substitute-in-file-name "path-to-ztree-directory") load-path)
(require 'ztree-diff)
```

Call the `ztree-diff` interactive function:

```
M-x ztree-diff
```
Then you need to specify the left and right directories to compare.

###Hotkeys supported
The basic hotkeys are the same as in the **ztree-dir**. Additionally:
 * `RET` on different files starts the **Ediff** (or open file if one absent or the same)
 * `Space` show the simple diff window for the current file instead of **Ediff** (or view file if one absent or the same)
 * `TAB` to fast switch between panels
 * `h` key to toggle show/hide identical files/directories
 * `C` key to copy current file or directory to the left or right panel
 * `D` key to delete current file or directory
 * `v` key to quick view the current file
 * `r` initiates the rescan/refresh of current file or subdirectory
 * `F5` forces the full rescan.

Screenshots:

![ztreediff emacsx11](https://github.com/fourier/ztree/raw/screenshots/screenshots/emacs_diff_xterm.png "Emacs in xterm with ztree-diff")

![ztreediff-diff emacsx11](https://github.com/fourier/ztree/raw/screenshots/screenshots/emacs_diff_simplediff_xterm.png "Emacs in xterm with ztree-diff and simple diff")


ztree-dir
---------
**ztree-dir** is a simple text-mode directory tree for Emacs. See screenshots below for the GUI and the terminal versions of the **ztree-dir**.

As above Add the following to your .emacs file:

```scheme
(push (substitute-in-file-name "path-to-ztree-directory") load-path)
(require 'ztree-dir)
```

Call the `ztree-dir` interactive function:

```
M-x ztree-dir
```

* Open/close directories with double-click, `RET` or `Space` keys.
* To jump to the parent directory, hit the `Backspace` key.
* To toggle open/closed state of the subtree of the current directory, hit the `x` key.


![ztree emacsapp](https://github.com/fourier/ztree/raw/screenshots/screenshots/emacs_app.png "Emacs App with ztree-dir")

![ztree emacsx11](https://github.com/fourier/ztree/raw/screenshots/screenshots/emacs_xterm.png "Emacs in xterm with ztree-dir")

