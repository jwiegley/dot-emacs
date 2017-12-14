# helm-google

Emacs Helm Interface for quick Google searches

## Screenshot

![screen shot](https://raw.github.com/steckerhalter/helm-google/master/screenshot.png)

## Installation

### quelpa

`quelpa` is at https://github.com/quelpa/quelpa

```lisp
(quelpa '(helm-google :fetcher github :repo "steckerhalter/helm-google"))
```

### MELPA

`helm-google` is on [MELPA](http://melpa.milkbox.net/) (see there for more info).

## Usage

Call it with:

    M-x helm-google

Or bind it to a key:

```lisp
(global-set-key (kbd "C-h C--") 'helm-google)
```

If a region is selected it will take that as default input and search Google immediately. Otherwise it will start to search after you have entered a term. Pressing `RET` on a result calls the `browse-url` function which should open the URL in your web browser.

There are two Helm actions defined. The first (default) action is the one mentioned above and the second action will open the URL with the internal `Emacs Web Wowser` (EWW, since Emacs 24.4). You can press <key>F2</key> to execute this action directly.

If you want use EWW by default you can set it as your default browser like so:

```lisp
(setq browse-url-browser-function 'eww-browse-url)
```

If you want to keep the search open use `C-z` instead of `RET`.

### helm-google-suggest

`helm-google` is added as an action to `helm-google-suggest` (thanks to Dickby). Press TAB and choose `Helm-Google` or use the shortcut listed there directly.
