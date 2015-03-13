# Prodigy [![Build Status](https://api.travis-ci.org/rejeep/prodigy.el.png?branch=master)](http://travis-ci.org/rejeep/prodigy.el)

Manage external services from within Emacs

I came up with the idea when I got to work one Monday morning and
before I could start working I had to manually start ten or so
services.

To get rid of this tedious work, I started working on this Emacs
plugin. Prodigy provides a
[Magit](https://github.com/magit/magit)-like GUI to manage services in
a simple way.

## Installation

Add `prodigy` to your [Cask](https://github.com/cask/cask) file:

```lisp
(depends-on "prodigy")
```

## API

### prodigy-define-service (`&optional doc-string &rest args`)

See doc-string for information about available properties to specify:
`M-x describe-function RET prodigy-define-service`

## Commands

Start Prodigy with `M-x prodigy`. You should see a list of all defined
services.

### Quit (`q`)

Quit Prodigy.

### Next service (`n`)

Go to next service.

### Prev service (`p`)

Go to previous service.

### Start service (`s`)

Start service at line or marked services.

### Stop service (`S`)

Stop service at line or marked services.

### Restart service (`r`)

Restart service at line or marked services.

### Display service process output (`$`)

Switch to buffer for service at line.

### Open in browser (`o`)

Open service at line in browser.

### Mark service (`m`)

Mark service at line.

### Mark services with tag (`t`)

Mark services with tag.

### Mark all services (`M`)

Mark all services.

### Unmark service (`u`)

Unmark service at line.

### Unmark services with tag (`t`)

Unmark services with tag.

### Unmark all services (`U`)

Unmark all services.

### Refresh GUI (`g`)

Refresh GUI.

## Examples

Start simple Python server:

```lisp
(prodigy-define-service
  :name "Python app"
  :command "python"
  :cwd "/path/to/my/project"
  :args '("-m" "SimpleHTTPServer" "6001")
  :tags '(work))
```

Start Node server:

```lisp
(prodigy-define-service
  "My awesome Node app."
  :name "Node app"
  :command "nodemon"
  :cwd "/path/to/my/project"
  :args '("app.coffee")
  :port 6002
  :tags '(work node))
```

Start Sinatra server:

```lisp
(prodigy-define-service
  :name "Sinatra"
  :command "server"
  :cwd "/path/to/my/project"
  :path '("/path/to/my/project/bin")
  :port 6003
  :tags '(work ruby)
  :init (lambda ()
          ;; Setup RVM
          ))
```

## Contribution

Contribution is much welcome!

Install [Cask](https://github.com/cask/cask) if you haven't
already, then:

    $ cd /path/to/prodigy.el
    $ cask

Run all tests with:

    $ make
