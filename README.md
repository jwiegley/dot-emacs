# ht.el

The missing hash table library for Emacs.

## Functions

* `ht-create` `(test?)`
* `ht-get` `(table key default?)`
* `ht-set` `(table key value)`
* `ht-update` `(table table)`
* `ht-merge` `(&rest tables)`
* `ht-remove` `(table key)`
* `ht-clear` `(table)`
* `ht-keys` `(table)`
* `ht-values` `(table)`
* `ht-items` `(table)`
* `ht-map` `(function table)`
* `ht-each` `(function table)`
* `ht-copy` `(table)`
* `ht-from-alist` `(alist)`
* `ht-from-plist` `(plist)`
* `ht-to-alist` `(table)`
* `ht-to-plist` `(table)`
* `ht-p` `(table-or-object)`
* `ht-contains-p` `(table key)`

## Macros

* `ht` `(&rest pairs)`
* `ht-amap` `(form table)`
* `ht-aeach` `(form table)`

## Examples

Creating a hash table and accessing it:

    (require 'ht)

    (defun say-hello (name)
      (let ((greetings (ht ("Bob" "Hey bob!")
                           ("Chris" "Hi Chris!"))))
        (ht-get greetings name "Hello stranger!")))

This could be alternatively written as:

    (require 'ht)

    (defun say-hello (name)
      (let ((greetings (ht-create)))
        (ht-set greetings "Bob" "Hey Bob!")
        (ht-set greetings "Chris" "Hi Chris!")
        (ht-get greetings name "Hello stranger!")))

## Why?

Libraries like [s.el](https://github.com/magnars/s.el) (strings) and
[dash.el](https://github.com/magnars/dash.el) (lists) have shown how
much nicer Emacs lisp programming can be with good libraries. ht.el
aims to similarly simplify working with hash tables.

Common operations with hash tables (e.g. enumerate the keys) are too
difficult in Emacs lisp.

ht.el offers:

* A consistent naming scheme (contrast `make-hash-table` with `puthash`)
* A more natural argument ordering
* Mutation functions always return `nil`
* A more comprehensive range of hash table operations, including a
  conventional map (`ht-map` returns a list, elisp's `maphash` returns
  nil).

### Similar libraries

* [kv.el](https://github.com/nicferrier/emacs-kv) (focuses more on alists)

## Installation

ht.el is availabe on [MELPA](http://melpa.milkbox.net/) and
[Marmalade](http://marmalade-repo.org/).

Add a package archive to your .emacs.d/init.el:

    (require 'package)
    (add-to-list 'package-archives '("melpa" . "http://melpa.milkbox.net/packages/") t)
    
then run `M-x package-install <RET> ht <RET>`

## API changelog

ht.el uses semantic versioning, so an incompatible API change will
result in the major version increasing. See CHANGELOG.md for a history
of all changes.

### v1.0

* `ht-map` now returns a list.

## Running tests

`M-x ht-run-tests`

## What's an alist/plist?

An alist is an association list, which is a list of pairs. It looks like this:

    ((key1 . value1)
     (key2 . value2)
     (key3 . value3))
     
An alist can also look like this:
     
    ((key1 . value1)
     (key2 . value2)
     (key1 . oldvalue))
     
A plist is a property list, which is a flat list with an even number
of items. It looks like this:

    (key1 value1
     key2 value2
     key3 value3)

Both of these are slow. ht.el provides `ht-from-alist` and
`ht-from-plist` to help you convert to hash tables. If you need to
work with an alist or plist, use the functions `ht-to-alist` and
`ht-to-plist` to convert an hash table to those formats.
