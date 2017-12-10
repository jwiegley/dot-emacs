# discover-my-major

Discover key bindings and descriptions for commands defined by a buffer's major and minor modes.

The command is inspired by [discover.el](https://github.com/mickeynp/discover.el) and also uses the [makey library](https://github.com/mickeynp/makey). I thought, "Hey! Why not parse the information about the major mode bindings somehow and display that like `discover.el` does..."

The output is pretty bare bones and not optimized but it seems to work already quite well for most modes:

![package-menu-mode screenshot](https://raw.github.com/steckerhalter/discover-my-major/master/package-menu-mode.png)

![git-commit-mode screenshot](https://raw.github.com/steckerhalter/discover-my-major/master/git-commit-mode.png)

## Installation

### quelpa

`quelpa` is at https://github.com/quelpa/quelpa

```lisp
(quelpa '(discover-my-major :fetcher github :repo "steckerhalter/discover-my-major"))
```

### MELPA

Packages are available in [MELPA](http://melpa.milkbox.net/).

### el-get

```lisp
(:name discover-my-major
       :type git
       :url "https://github.com/steckerhalter/discover-my-major")
```

## Usage

In any mode you should be able to summon the popup to discover the commands defined by the current buffer's `major-mode`, by invoking `M-x discover-my-major`; and for any of the buffer's active minor modes, by invoking `M-x discover-my-mode`. Each of these commands which will show you a list of key bindings defined by that mode in the current buffer along with their descriptions.

The recommended key binding is `C-h C-m`, but be aware that by default `C-h C-m` is bound to `view-order-manuals`. If the `help+` package is installed, this key is bound to `help-on-click/key` by default.

```lisp
(global-set-key (kbd "C-h C-m") 'discover-my-major)
(global-set-key (kbd "C-h M-m") 'discover-my-mode)
```

Or alternatively, to avoid overriding `C-h C-m`:

```lisp
(global-set-key (kbd "C-h M-m") 'discover-my-major)
(global-set-key (kbd "C-h M-S-M") 'discover-my-mode)
```
