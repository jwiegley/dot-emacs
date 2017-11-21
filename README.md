m-buffer.el
===========
[![Build Status](https://travis-ci.org/phillord/m-buffer-el.png?branch=master)](https://travis-ci.org/phillord/m-buffer-el)

## Introduction

This package provides a set of list-orientated functions for operating over
the contents of Emacs buffers. Functions are generally purish: i.e. they may
change the state of one buffer by side-effect, but should not affect point,
current buffer, match data or so forth. Generally, markers are preferred over
point locations so that it is possible, for example, to search for regexp
matches and then replace them all without the early replacement invalidating
the location of the later ones.

m-buffer is now documented at http://phillord.github.io/m-buffer-el/ or live
in Emacs with [Lentic Server](https://github.com/phillord/lentic-server).


## Status

The code is now in active use. APIs are open to change, but I am not intending
to.

Version 0.14 did not support Emacs-24, which unintentionally broke assess.el
which needs to work on these platforms. Emacs-24 is now supported again.

## Contributions

Contributions are welcome. However, I would like to keep the option of hosting
m-buffer.el on ELPA, therefore, contributors should have
[Copyright Assignment papers](https://www.gnu.org/prep/maintain/html_node/Copyright-Papers.html)
with the FSF.


## Change Log

### 0.15

Support Emacs-24 again

### 0.14

New function added `m-buffer-match-multi`

### 0.13

New function added `m-buffer-at-string`

#### Bug Fixes

- m-buffer was actually moving point, because the state was saved before
  changing buffer.
- The benchmark documentation file was being compiled and run on installation,
  when it is supposed to serve as static documentation.

### 0.12

New funtion added: `m-buffer-partition-by-marker`

### 0.11

This release mostly includes considerably improved documentation.

There is one change which is half-way between a breaking change and a bug fix.
Previously, in the m-buffer-match-* functions "match" arguments could take any
keyword argument and these would over-ride any arguments already set. This
means that a call such as:

    (m-buffer-match-page (current-buffer) :regexp "this")

would behave the same as:

    (m-buffer-match (current-buffer) :regexp "this")

rather than matching pages. Alternatively, this call:

    (m-buffer-match-line
       (current-buffer)
       :post-match (lambda () t))

never terminates. Both of these now throw an error instead.

#### Breaking Changes

- m-buffer-match-* functions now error on conflicting arguments

### 0.10

#### Bug Fixes

- m-buffer-replace-match no longer moves point

### 0.9

#### Bug Fixes

- Now byte-compiles without errors/warning

#### Breaking Changes

- `m-buffer-point' renamed to `m-buffer-at-point'

### 0.8

- New macros for marker usage.
- m-buffer-at added. New stateless functions for information about Emacs buffers.

#### Breaking Changes

- File organisation has been refactored with some macros moved out of m-buffer.el

### 0.7
- `m-buffer-match-first-line' added.

### 0.6

 - All match functions now take a :numeric argument which forces the
   return of numbers rather than markers.
 - Two new functions for subtracting one set of matches from another:
   `m-buffer-match-subtract` and `m-buffer-match-exact-subtract`
 - `m-buffer-with-markers` is a `let*` like macro which autonils markers after
   use.
 - `m-buffer-with-current-location` is like `with-current-buffer` but also
   takes a location.
 - `m-buffer-with-current-marker` is like `with-current-buffer` but takes a
   marker.
 
### 0.5
 - Automated Testing with Cask

#### Breaking Changes
 - m-buffer-replace-match optional arguments now expanded to match
   replace-match. This means the 3rd argument has changed meaning.

### 0.4

 - m-buffer-match-data has become m-buffer-match
 - Testing is now via Cask


#### New Functions

 - m-buffer-delete-match

### 0.3

 - Various functions for colourising/adding faces
 - Documentation improvements.
 - m-buffer-nil-markers has been depluralised to m-buffer-nil-marker
 - m-buffer-replace-match now returns start end markers
 - m-buffer-clone-markers added.
 

### 0.2

#### New Functions
 - Functions for matching block things -- line start and end, sentence end,
   paragraph separators, words.
 - `m-buffer-match-string` and `m-buffer-match-substring` for extracting
   match-strings. 
 

#### Name changes
 - Functions now use singular rather than plural -- so `m-buffer-matches-data`
   has become `m-buffer-match-data`.
 - All uses of `beginning` have been changed to `begin` -- it is shorter and
   matches `end`

#### Matchers
 - Regexp functions are now overloaded and take either a buffer and regexp or
   match-data (except for `m-buffer-match-data` for which it makes no sense to
   pass in match-data). This allows easy chaining of methods.
 - Matchers now also overloaded for windows -- searching in the visible
   portion of window. `m-buffer-match-data-visible-window` access this feature
   directly.
 - Match Options are now keyword rather than positional which considerably
   simplifies the implementation, especially with an eye to future expansion.

#### Build and Test
 - Reworked tests and build scripts.
