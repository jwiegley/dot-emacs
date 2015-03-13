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

## Configuration

`helm-google` has two methods to search for results. One is a deprecated JSON API which still works but only gives a maximum of 4 results. The other method is via scraping the html of the website.

You can configure the method via `M-x customize helm-google RET`. The default is html. If Google changes the markup this may break and you probably want to use the API.

## Usage

Call it with:

    M-x helm-google

Or bind it to a key:

```lisp
(global-set-key (kbd "C-h C--") 'helm-google)
```

If a region is selected it will take that as default input and search Google immediately. Otherwise it will start to search after you have entered a term. Pressing `RET` on a result calls the `browse-url` function which should open the URL in your web browser.

If you want use the internal Emacs web browser (EWW, since Emacs 24.4) you can set it as your default browser like so:

```lisp
(setq browse-url-browser-function 'eww-browse-url)
```

If you want to keep the search open use `C-z` instead of `RET`.
