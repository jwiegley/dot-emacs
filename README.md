[![Build Status](https://travis-ci.org/lewang/ws-butler.png)](http://travis-ci.org/lewang/ws-butler)

## ws-butler -- an unobtrusive way to trim spaces from end of line

- Only lines touched get trimmed.  If the white space at end of buffer is
  changed, then blank lines at the end of buffer are truncated respecting
  `require-final-newline`.

- Trimming only happens when saving.

## What does unobtrusive mean?

The user is not made explicitly aware when trimming happens.  You keep working
and the butler takes care of whitespace for you.

This means if point is at a location that was trimmed, point is not moved, but
the data on disk has been cleaned up (revert the buffer to confirm).

### Not moving point because of space deletion.

By default, ws-butler preserves "virtual spaces" in front of point if necessary.  The file on disk is cleaned up however.

This can be disabled with `ws-butler-keep-whitespace-before-point`.

#### Trimming only specific lines.

There might be lines you don't want to get trimmed, e.g. spaces in multiline strings.  The behavior can be customized through `ws-butler-trim-predicate`.  This variable should hold a function that expects 2 arguments (region beginning and end) and should return true only for regions that one wants to get trimmed. As an example

    (setq ws-butler-trim-predicate
          (lambda (beg end)
            (not (eq 'font-lock-string-face
                     (get-text-property end 'face)))))


## Installation

### Debian 9 or later or Ubuntu 16.10 or later

`apt-get install elpa-ws-butler`

## History

1. I started by trimming all spaces at EOL in source code in a
   "write-file-hook" when I started programming.  It seemed like a great idea.

2. Then I got a job working on a code base where no one else trimmed spaces,
   so my commits became super noisy.  I wanted to stop being the "white space"
   police, so switched to [ws-trim][].
    * ws-trim works in a `post-command-hook` and trims white space while you
      edit.
    * This was too eager for me. For example, I would stop and scroll away to
      look at some code, and when I get back to continue, my indentation is
      gone.
    * It caused some problems with other customizations which also rely on
      `post-command-hook`.

3. I started experimenting with using `highlight-changes-mode` to trim only
   lines I touch on save.

4. Now, the dependency on `highlight-changes-mode` has been removed and we
   handle change changing through text properties ourselves.

[ws-trim]: ftp://ftp.lysator.liu.se/pub/emacs/ws-trim.el
