## git-gutter-fringe+.el

git-gutter-fringe+ is a display mode for
[git-gutter+.el](https://github.com/nonsequitur/git-gutter-plus).
It uses the buffer fringe instead of the buffer margin.

|                          | git-gutter+.el | git-gutter-fringe+.el |
|:-------------------------|:-------------:|:--------------------:|
| Works in tty frame       | +             | -                    |
| Works with linum-mode    | -             | +                    |
| Gutter on the right side | -             | +                    |

![git-gutter-fringe.el](images/git-gutter-fringe.png)

## Installation

* With package.el:

  Add  [MELPA](https://github.com/milkypostman/melpa.git) as a package source.
  Run `M-x package-install git-gutter-fringe+`
  (And make sure you've got the latest version of
  [fringe-helper](http://www.emacswiki.org/emacs/FringeHelper))

* Add this to your .emacs file:

        (require 'git-gutter-fringe+)

 The fringe display mode is automatically activated.

## Disabling/Enabling

Run `M-x git-gutter+-toggle-fringe` to disable/enable the fringe display mode.

## Minimal skin

![git-gutter-fringe-minimal](images/git-gutter-fringe-minimal.png)

Features smaller, greyscale diff symbols. Activate it with

    (git-gutter-fr+-minimal)

## Customize

### Look and feel

![git-gutter-fringe-customize](images/git-gutter-fringe-customize.png)

You can customize the colors of modified, added, and deleted fringe marks either by
modifying the faces from git-gutter+ or directly using the git-gutter-fr+ faces.

Using the fact git-gutter-fr+ faces are inherited from git-gutter+:
```elisp
(set-face-foreground 'git-gutter+-modified "yellow")
(set-face-foreground 'git-gutter+-added    "blue")
(set-face-foreground 'git-gutter+-deleted  "white")
```

Or directly, to allow different colors for git-gutter-fr+ and git-gutter+:
```elisp
(set-face-foreground 'git-gutter-fr+-modified "yellow")
(set-face-foreground 'git-gutter-fr+-added    "blue")
(set-face-foreground 'git-gutter-fr+-deleted  "white")
```

### Change signs in fringe

![git-gutter-fringe-change-signs](images/git-gutter-fringe-change-signs.png)

```elisp
;; Please adjust fringe width if your own sign is too big.
(setq-default left-fringe-width  20)
(setq-default right-fringe-width 20)

(fringe-helper-define 'git-gutter-fr+-added nil
  ".XXXXXX."
  "XX....XX"
  "X......X"
  "X......X"
  "XXXXXXXX"
  "XXXXXXXX"
  "X......X"
  "X......X")

(fringe-helper-define 'git-gutter-fr+-deleted nil
  "XXXXXX.."
  "XX....X."
  "XX.....X"
  "XX.....X"
  "XX.....X"
  "XX.....X"
  "XX....X."
  "XXXXXX..")

(fringe-helper-define 'git-gutter-fr+-modified nil
  "XXXXXXXX"
  "X..XX..X"
  "X..XX..X"
  "X..XX..X"
  "X..XX..X"
  "X..XX..X"
  "X..XX..X"
  "X..XX..X")
```

### Position of fringe

![git-gutter-fringe-right](images/git-gutter-fringe-right.png)

You can change position of fringe, left or right. Default is left.

```elisp
(setq git-gutter-fr+-side 'right-fringe)
```
