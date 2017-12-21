# simple-httpd

A simple Emacs web server.

This used to be `httpd.el` but there are already several of these out
there already of varying usefulness. Since the name change, it's been
stripped down to simply serve files and directory listings. Client
requests are sanitized so this *should* be safe, but I make no
guarantees.

This package is available on [MELPA](http://melpa.milkbox.net/).

## Usage

Once loaded, there are only two interactive functions to worry about:
`httpd-start` and `httpd-stop`. Files are served from `httpd-root`
(can be changed at any time) on port `httpd-port`. Directory listings
are enabled by default but can be disabled by setting `httpd-listings`
to `nil`.

```cl
(require 'simple-httpd)
(setq httpd-root "/var/www")
(httpd-start)
```

## Servlets

Servlets can be defined with `defservlet`. This one creates at servlet
at `/hello-world` that says hello.

```cl
(defservlet hello-world text/plain (path)
  (insert "hello, " (file-name-nondirectory path)))
```

See the comment header in `simple-httpd.el` for full details.

## Extensions

Packages built on simple-httpd:

 * [skewer-mode](https://github.com/skeeto/skewer-mode)
 * [impatient-mode](https://github.com/netguy204/imp.el)
 * [airplay](https://github.com/gongo/airplay-el)
 * [elfeed-web](https://github.com/skeeto/elfeed)

## Unit tests

The unit tests can (and should usually) be run like so,

    emacs -batch -L . -l simple-httpd-test.el -f ert-run-tests-batch

It does some mocking to avoid using network code during testing.
