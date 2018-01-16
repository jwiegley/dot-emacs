
## Changelog

### v0.19.0

* Remove deprecated `f-up` function, use `f-traverse-upwards` instead
* Add `f-append-text` and `f-append-bytes`
* Add `f-hidden?`

### v0.18.0

* Add `f-swap-ext` (by @phillord)
* Add `f-depth` (by @cheunghy)

### v0.17.0

* Add `f-common-parent` (by @Fuco1)

### v0.16.0

* Add `f-with-sandbox`

### v0.15.0

* Add `f-split`

### v0.14.0

* Add `f-traverse-upwards` and its anaphoric version `f--traverse-upwards`
* Deprecate `f-up` and its anaphoric version `f--up`

### v0.13.0

* Add `f-uniquify` and `f-uniquify-alist` (by @Fuco1)

### v0.12.0

* `f-parent` returns nil if argument is root

### v0.11.0

* Add `f-descendant-of?`
* Add `f-ancestor-of?`
* Add `f-parent-of?`
* Add `f-child-of?`
* Remove deprecation for `f-read` and `f-write` and make them aliases
  to `f-read-text` and `f-write-text` respectively
* Add anaphoric function `f--entries` for `f-entries`
* Add anaphoric function `f--files` for `f-files`
* Add anaphoric function `f--directories` of `f-directories`
* Add `f-up` and anaphoric version `f--up`

### v0.10.0

* Add `f-root`
* Fix `f-root?` bug for weird syntax

### v0.9.0

* Make `s-long`
* Make `s-short` default and `f-abbrev` the alias
* Add `f-full`
* Do not append path separator if file in `f-slash`
* Fixed bug in `f-path-separator`

### v0.8.0

* Moved `f-this-file` to misc section
* Add `f-slash`
* Add `f-path-separator`

### v0.7.1

* Fix coding bug in `f-read-text`

### v0.7.0

* Add `f-touch`

### v0.6.1

* Fix `f-write-text` for unibyte strings

### v0.6.0

* Add `f-write-text` and `f-write-bytes` and deprecate `f-write`
* Add `f-read-text` and `f-read-bytes` and deprecate `f-read`
* Add `f-this-file`
* Add `f-canonical`
* Fix `f-same?` for symlinks

### v0.5.0

* Add `f-same?` (alias `f-equal?`)

### v0.4.1

* Bump `s` and `dash` versions

### v0.4.0

* Add `f-copy`

### v0.3.0

* Add `f-ext?`

### v0.2.1

* Fix `f-filename` when ending with slash

### v0.2.0

* Add `f-root?`
* Fix `f-dirname` when ending with slash

### v0.1.0

* Add `f-abbrev` (alias `f-short`)

### v0.0.2

* `f-join` platform independent

### v0.0.1
