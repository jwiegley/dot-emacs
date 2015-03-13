## v1.5

* `ht-aeach` now evaluates to `nil` as it should (use `ht-amap` if you
  want the resulting hash table).

## v1.4

* Added `ht-merge`.

## v1.3

* Removed runtime dependency on `cl`.

## v1.2

* Fixed various `void-variable` crashes due to `ht-amap` only being
  declared after its usage.

## v1.1

* Added `ht-contains-p`.

## v1.0 -- API Change

* `ht-map` now returns a list, as you'd expect a map function to do.
* Added `ht-each` for when you're only interested in side-effects.
* Added an anaphoric version of `ht-each`, `ht-aeach`.

## v0.11

* Added `ht-map` and an anaphoric version `ht-amap`.

## v0.10

* Added `ht-p`, an alias of `hash-table-p`, (mainly for completeness).

## v0.9

* Added `ht-update`.

## v0.8

* Added the `ht` macro to make hash table literals easy

## v0.7

* Added `ht-to-alist` and `ht-to-plist`

## v0.6

* Fixed a bug where `ht-from-alist` would overwrite the latest key-value
  association with older ones

## v0.5

* Added `ht-from-plist`

## v0.4

* Added `ht-from-alist`

## v0.3

* Added ht-copy

## v0.2

* Changed functions from hm-* to ht-* (Emacs doesn't use the term hash map)

## v0.1

* Initial release
