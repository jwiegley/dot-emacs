Markdown preview mode
===========================

[![MELPA Stable](http://stable.melpa.org/packages/markdown-preview-mode-badge.svg)](http://stable.melpa.org/#/markdown-preview-mode)
[![MELPA](http://melpa.org/packages/markdown-preview-mode-badge.svg)](http://melpa.org/#/markdown-preview-mode)

Markdown preview in emacs features:

* on save/idle preview update
* scroll sync
* custom/extra css and javascript
* remote preview
* multiple simultaneous previews

## Install

* `package-install markdown-preview-mode`
* `el-get-install markdown-preview-mode`

### Markdown processor

`markdown-preview-mode` depends on `markdown-mode` for markdown processor, defined by `markdown-command` and it is [markdown](http://daringfireball.net/projects/markdown/) by default. Please, make sure it is in your `$PATH`.

## Run

* `markdown-preview-mode` - start mode and open preview window.
* `markdown-preview-open-browser` - open priview window for current buffer.
* `markdown-preview-cleanup` - cleanup running processes (close websocket and http servers).

## Customize

* `customize-option markdown-command` - change markdown processor; take a look at [multimarkdown](http://fletcherpenney.net/multimarkdown/)
* `customize-option` [browse-url-browser-function](http://www.emacswiki.org/emacs/BrowseUrl) - change the browser.
* `customize-option markdown-preview-host` - change http/websocket server address.
* `customize-option markdown-preview-ws-port` - change websocket server port.
* `customize-option markdown-preview-http-port` - change http server port.
* `customize-option markdown-preview-auto-open` - change the way preview window is open.

## Remote access

* Set `markdown-preview-auto-open` to `nil` to disable window opening at remote emacs server.
* Start `markdown-preview-mode`. Http link for preview will be printed to `*Messages*` buffer. If not - run `markdown-preview-open-browser` to get the link printed.
* Setup 2 tunnels for `0.0.0.0:7379` and `0.0.0.0:9000` and then open preview link in local browser. Adjust tunnels according to your custom `ws-port` and `http-port` settings.

## Extra css

### Add extra css to default solarized dark theme

```lisp
(add-to-list 'markdown-preview-stylesheets "https://raw.githubusercontent.com/richleland/pygments-css/master/emacs.css")
```
### Override theme completely

```lisp
(setq markdown-preview-stylesheets (list "http://thomasf.github.io/solarized-css/solarized-light.min.css"))
```

## Extra javascript

### Add MathJax

```lisp
(add-to-list 'markdown-preview-javascript "http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-MML-AM_CHTML")
```
### async

```lisp
(add-to-list 'markdown-preview-javascript '("http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-MML-AM_CHTML" . async))
```

## Dependencies

* [markdown-mode.el](https://github.com/defunkt/markdown-mode)
* [websocket.el](https://github.com/ahyatt/emacs-websocket)
* [web-server.el](https://github.com/eschulte/emacs-web-server)
* [uuidgen](https://github.com/kanru/uuidgen-el)
