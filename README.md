
# ov.el [![Build Status](https://travis-ci.org/ShingoFukuyama/ov.el.svg?branch=master)](https://travis-ci.org/ShingoFukuyama/ov.el) [![melpa badge][melpa-badge]][melpa-link] [![melpa stable badge][melpa-stable-badge]][melpa-stable-link]

Simple way to manipulate overlay for Emacs.

![ov.el](https://raw.githubusercontent.com/ShingoFukuyama/images/master/ov1.gif)

Overlay is capable of manipulating text appearance, cursor behavior, etc.
It doesn't affect font-lock or text-properties.

## Command

You can always do `M-x ov-clear` to clear all overlays in the current buffer.

## Functions

### Make overlay / Set properties

* [ov](#ov-beg-end-rest-properties) `(beg end &rest properties)`
* [ov-make](#ov-make-beg-end) `(beg end)`
* [ov-line](#ov-line-optional-point) `(&optional point)`
* [ov-match](#ov-match-string-optional-beg-end) `(string &optional beg end)`
* [ov-regexp](#ov-regexp-regexp-optional-beg-end) `(regexp &optional beg end)`
* [ov-set](#ov-set-ov-or-ovs-or-regexp-rest-properties) `(ov-or-ovs-or-regexp &rest properties)`
* [ov-insert](#ov-insert-any) `(any)`
* [ov-region](#ov-region)

### Clear overlay

* [ov-clear](#ov-clear-optional-prop-or-beg-val-or-end-beg-end) `(&optional beg end property value)`
* [ov-reset](#ov-reset-ov-or-ovs-variable) `(ov-or-ovs-variable)`

### Look up overlay parameters, etc

* [ov-p](#ov-p-ov) `(ov)`
* [ov-beg](#ov-beg-ov) `(ov)`
* [ov-end](#ov-end-ov) `(ov)`
* [ov-length](#ov-length-ov) `(ov)`
* [ov-buf](#ov-buf-ov) `(ov)`
* [ov-val](#ov-val-ov-property) `(ov property)`
* [ov-prop](#ov-prop-ov) `(ov)`
* [ov-spec](#ov-spec-ov-or-ovs) `(ov-or-ovs)`

### Get an existing overlay or overlay list

* [ov-at](#ov-at-optional-point) `(&optional point)`
* [ov-in](#ov-in-prop-or-val-val-or-end-beg-end) `(prop-or-beg val-or-end beg end)`
* [ov-all](#ov-all)
* [ov-backwards](#ov-backwards-optional-point) `(&optional point)`
* [ov-forwards](#ov-forwards-optional-point) `(&optional point)`

### Overlay manipulation

* [ov-move](#ov-move-ov-beg-end-optional-buffer) `(ov beg end &optional buffer)`
* [ov-next](#ov-next-optional-point-or-prop-prop-or-val-val) `(&optional point-or-prop prop-or-point val)`
* [ov-prev](#ov-prev-optional-point-or-prop-prop-or-val-val) `(&optional point-or-prop prop-or-point val)`
* [ov-goto-next](#ov-goto-next-optional-point-or-prop-prop-or-point-val) `(&optional point-or-prop prop-or-point val)`
* [ov-goto-prev](#ov-goto-prev-optional-point-or-prop-prop-or-point-val) `(&optional point-or-prop prop-or-point val)`
* [ov-keymap](#ov-keymap-ov-or-ovs-or-id-rest-keybinds) `(ov-or-ovs-or-id &rest keybinds)`
* [ov-read-only](#ov-read-only-ov-or-ovs-optional-insert-in-front-insert-behind) `(ov-or-ovs &optional insert-in-front insert-behind)`
* [ov-placeholder](#ov-placeholder-ov-or-ovs) `(ov-or-ovs)`
* [ov-smear](#ov-smear-regexp-or-list-optional-match-end-base-color-color-range) `(regexp-or-list &optional match-end base-color color-range)`


## Make overlay / Set properties

:link: [Overlay Properties](http://www.gnu.org/software/emacs/manual/html_node/elisp/Overlay-Properties.html)

#### ov `(beg end &rest properties)`

Make an overlay from `beg` to `end`.  If `properties` are specified, set them for the created overlay.

Return: `overlay`

```cl
(ov 10 40 'face 'font-lock-warning-face 'intangible t)
(ov 30 80 '(face font-lock-warning-face intangible t))
(ov (point-min) (point) 'face '(:background "#00ff00" :height 1.5))
(ov (point-min) (point-max) '(face (:background "#00ff00" :height 1.5)))
;; Just make an overlay without setting properties
(setq ov1 (ov 5 15))    ; => #<overlay from 5 to 15 in *scratch*>
```

You can always do `M-x ov-clear` to clear all overlays in the current buffer.

#### ov-make `(beg end)`

Just make an overlay from `beg` and `end`.

Return: `overlay`
Alias: `ov-create`

```cl
(setq ov1 (ov-make 10 55))           ; => #<overlay from 10 to 55 in *scratch*>
(setq ov2 (ov-make (point-min) 25))  ; => #<overlay from 1 to 25 in *scratch*>
```

#### ov-line `(&optional point)`

Make an overlay from the beginning of the line to the beginning of the next line, which include `point`.

Return: `overlay`

```cl
(setq ov1 (ov-line))  ; => #<overlay from 734 to 827 in *scratch*>
```

#### ov-match `(string &optional beg end)`

Make overlays spanning the regions that match `string`.

If `beg` and `end` are numbers, they specify the bounds of the search.

Return: `overlay list`

```cl
(setq ov1 (ov-match "setq"))
(setq ov2 (ov-match "setq" 1 200))
```

#### ov-regexp `(regexp &optional beg end)`

Make overlays spanning the regions that match `regexp`.

If `beg` and `end` are numbers, they specify the bounds of the search.

Return: `overlay list`

```cl
(setq ov1 (ov-regexp "setq"))
(setq ov2 (ov-regexp "setq" 100 550))
```

#### ov-set `(ov-or-ovs-or-regexp &rest properties)`

Set overlay properties and values.
`ov-or-ovs-or-regexp` can be an overlay, overlays or a regexp.

If an overlay or list of overlays, `properties` are set for these.

If a regexp, first overlays are created on the matching regions (see
`ov-regexp`), then the properties are set.

If you want to use a literal string, use `(ov-match "string")` instead.

Return: `overlay` or `overlay list`, depending on `ov-or-ovs-or-regexp`
Alias: `ov-put`

```cl
(setq ov1 (ov-make 335 700))
(ov-set ov1 'face 'font-lock-warning-face 'intangible t)

(setq ov2 (ov-match "set"))
(ov-set ov2 '(face font-lock-function-name-face intangible t))

(ov-set (ov-regexp "^.ov-") 'display "λλ-" 'before-string "(" 'line-prefix "<λ>")
(ov-set "^;;.+$" 'face 'warning)

(ov-set (ov-line) 'before-string (propertize ">>> " 'face 'font-lock-warning-face))
(ov-set (ov-line) `(before-string ,(propertize ">>> " 'face 'font-lock-warning-face)))
```

#### ov-insert `any`

Insert `any` (string, number, list, etc) covered with an empty overlay.

Return: `overlay`

```cl
(ov-set (ov-insert "Overlay1") 'face 'menu 'intangible t)
```

#### ov-region

Make an overlay from a region if region is active.

When you make a region, do `M-: (ov-set (ov-region) 'face '(:box t))`.

Return: `overlay`

```cl
(ov-set (ov-region) 'face '(:box t))
```

## Clear overlay

#### ov-clear `(&optional prop-or-beg val-or-end beg end)`

Clear overlays satisfying a condition.

If `prop-or-beg` is a symbol, clear overlays with this property set to non-nil.

If `val-or-end` is non-nil, the specified property's value should
`equal` to this value.

If both of these are numbers, clear the overlays between these points.

If `beg` and `end` are numbers, clear the overlays with specified
property and value between these points.

With no arguments, clear all overlays in the buffer.

Arguments pattern:

```cl
(ov-clear PROPERTY VALUE BEG END)
(ov-clear PROPERTY VALUE)
(ov-clear BEG END)
(ov-clear PROPERTY)
(ov-clear)
```

```cl
(ov-clear 100 550 'my-fancy-comment t)
(ov-clear 'face 'font-lock-function-name-face)
(ov-clear 200 1000)
(ov-clear 'face)
(ov-clear) ;; clear overlays in the whole buffer
```

#### ov-reset `(ov-or-ovs-variable)`

Clear overlays in `ov-or-ovs-variable`.

`ov-or-ovs-variable` should be a symbol whose value is an overlay
or a list of overlays.

Finally, the variable is set to nil.

```cl
(setq ov1 (ov-line))
(ov-set ov1  'invisible t)
(ov-reset ov1)

(setq ov2 (ov-match "ov-"))
(ov-set ov2 '(face (:underline t)))
(ov-reset ov2)
```


## Look up overlay parameters, etc

#### ov-p `(ov)`

Check whether `ov` is overlay or not.

Alias: `ov?`

```cl
(setq ov1 99)
(setq ov2 (ov-make 10 20))
(setq ov3 ov2)
(ov-p ov1) ; => nil
(ov-p ov2) ; => t
(ov-p ov3) ; => t
```

#### ov-beg `(ov)`

Get the beginning of an overlay.

Return: `point`

```cl
(setq ov1 (ov-make 200 700))
(ov-beg ov1) ; => 200
```

#### ov-end `(ov)`

Get the end of an overlay.

Return: `point`

```cl
(setq ov1 (ov-make 200 700))
(ov-end ov1) ; => 700
```

#### ov-length `(ov)`

Return the length of the region spanned by `overlay`.

Return: `number`

```cl
(setq ov1 (ov-make 200 700))
(ov-length ov1) ; => 500
```

#### ov-buf `(ov)`

Get the buffer object of an overlay.

Return: `buffer object`

```cl
(setq ov1 (ov-make 200 700))
(ov-buf ov1)               ; => #<buffer *scratch*>
(buffer-name (ov-buf ov1)) ; => "*scratch*"
```

#### ov-val `(ov property)`

Get the value of `property` from an overlay.

Return: `value` of property

```cl
(setq ov1 (ov-line))
(ov-set ov1 'aaa "abc" 'bbb 22 'ccc 45)
(ov-val ov1 'bbb)           ; => 22
(ov-val ov1 'aaa)           ; => "abc"
```

#### ov-prop `(ov)`

Get the properties from an overlay.

Return: `properties list`

```cl
(setq ov1 (ov-make (point-min) (point-max)))
(ov-set ov1 '(face (:overline t) mouse-face (:underline t)))
(ov-prop ov1) ; => (mouse-face (:underline t) face (:overline t))
```

#### ov-spec `(ov-or-ovs)`

Make a specification list from an overlay or list of overlays.

Return: `list ((beginning end buffer (properties)) (beginning end buffer (properties))...)` or `nil`

```cl
(setq ov1 (ov-match "ov-spec"))
(ov-set ov1 'evaporate t)
(ov-spec ov1)
;; => ((5802 5809 README.md (evaporate t)) (5782 5789 README.md (evaporate t)) ...)

(setq ov2 (ov-line))
(ov-spec ov2) ; => ((5879 5921 README.md nil))
```

## Get an existing overlay or overlay list

#### ov-at `(&optional point)`

Get an overlay at `point`.
`point` defaults to the current `point`.

Return: `overlay` or `nil`

```cl
(save-excursion
  (ov-set (ov-make 20 50) 'face '(:box t))
  (goto-char 30)
  (ov-at))        ; => #<overlay from 20 to 50 in *scratch*>
```

#### ov-in `(prop-or-val val-or-end beg end)`

Get overlays satisfying a condition.

If `prop-or-beg` is a symbol, get overlays with this property set to non-nil.

If `val-or-end` is non-nil, the specified property's value should
`equal` to this value.

If both of these are numbers, get the overlays between these points.

If `beg` and `end` are numbers, get the overlays with specified
property and value between these points.

With no arguments, get all overlays in the buffer.

Return: `overlay list`

Arguments pattern:

```
(ov-in PROPERTY VALUE BEG END)
(ov-in PROPERTY VALUE)
(ov-in PROPERTY)
(ov-in BEG END)
(ov-in)
```

```cl
;; Get all overlays
(setq ov1 (ov-in))
;; Get overlays between 10 and 500
(setq ov2 (ov-in 10 500))
;; Get the overlays which has a specific property and its value
(setq ov3 (ov-in 'face 'warning))
;; Get the overlays which has a specific property
(setq ov4 (ov-in 'face))
;; Get the overlays between 10 and 500, which has a specific property and its value
(setq ov5 (ov-in 'face 'worning 10 500))
;; If 'any specified to val-or-end, it matches any value
(setq ov6 (ov-in 'face 'any 10 500))
```

#### ov-all

Get all the overlays in the entire buffer.

Return: `overlay list` or `nil`

```cl
(setq ov1 (ov-all))
```

#### ov-backwards `(&optional point)`

Get all the overlays from the beginning of the buffer to `point`.

Return: `overlay list` or `nil`

```cl
(setq ov1 (ov-backwards))
(setq ov2 (ov-backwards 1200))
```

#### ov-forwards `(&optional point)`

Get all the overlays from `point` to the end of the buffer.

Return: `overlay list` or `nil`

```cl
(setq ov1 (ov-forwards))
(setq ov2 (ov-forwards 1000))
```

## Overlay manipulation

#### ov-move `(ov beg end &optional buffer)`

Move an existing overlay position to another position.

Return: `overlay`

```cl
(setq ov1 (ov-line))
(ov-set ov1 'face 'underline)
(ov-move ov1 (point-at-bol) (point-at-eol))
;; Move overlay ov1 to another buffer
(progn
  (with-current-buffer (get-buffer-create "test")
    (insert "aaaaaaaaaaaaaaa"))
  (ov-move ov1 (point-min) (point-max) (get-buffer "test"))
  (pop-to-buffer "test"))
```

<!-- #### ov-timeout `(time func func-after)` -->

<!-- Execute `func-after` after `time` seconds passed since `func` done. -->

<!-- ```cl -->
<!-- (ov-timeout 0.5 -->
<!--   '(ov-set "ov" '(face (:background "#ff0000") aaa t)) -->
<!--   '(ov-clear 'aaa t)) -->

<!-- (defun ov-fn1 () -->
<!--   (ov-set (ov-match "ov") '(face (:background "#ff9900") bbb t))) -->
<!-- (defun ov-fn2 () -->
<!--   (ov-clear 'bbb t)) -->
<!-- (ov-timeout 1.2 ov-fn1 ov-fn2) -->
<!-- ``` -->

#### ov-next `(&optional point-or-prop prop-or-val val)`

Get the next overlay satisfying a condition.

If `point-or-prop` is a symbol, get the next overlay with this
property being non-nil.

If `prop-or-val` is non-nil, the property should have this value.

If `point-or-prop` is a number, get the next overlay after this
point.

If `prop-or-val` and `val` are also specified, get the next overlay
after `point-or-prop` having property `prop-or-val` set to `val` (with
`val` unspecified, only the presence of property is tested).

Return: `overlay`

Arguments pattern:

```
(ov-next POINT PROPERTY VALUE)
(ov-next PROPERTY VALUE)
(ov-next PROPERTY)
(ov-next)
```

```cl
(ov-set "^.." '(face (:background "#ff9900") aaa t))
(ov-set "..$" '(face (:background "#7700ff") bbb t))
(ov-next)         ; => #<overlay from 436 to 438 in *scratch*>
(goto-char (ov-beg (ov-next nil 'aaa)))
(goto-char (ov-end (ov-next nil 'bbb t)))

(ov-next 'aaa)
(ov-next 'aaa t)
(ov-next 300 'aaa)
(ov-next (point) 'aaa t)
```

#### ov-prev `(&optional point-or-prop prop-or-val val)`

Get the previous overlay satisfying a condition.

If `point-or-prop` is a symbol, get the previous overlay with this
property being non-nil.

If `prop-or-val` is non-nil, the property should have this value.

If `point-or-prop` is a number, get the previous overlay after this
point.

If `prop-or-val` and `val` are also specified, get the previous
overlay after `point-or-prop` having property `prop-or-val` set to
`val` (with `val` unspecified, only the presence of property is
tested).

Return: `overlay`

Arguments pattern:

```
(ov-prev POINT PROPERTY VALUE)
(ov-prev PROPERTY VALUE)
(ov-prev PROPERTY)
(ov-prev)
```

```cl
(ov-set (ov-match "o") '(face (:box t) my-char o))
(ov-set (ov-match "t") '(face (:box t) my-char t))
(ov-prev)         ; => #<overlay from 482 to 483 in *scratch*>
(goto-char (ov-beg (ov-prev (point) 'face)))
(goto-char (ov-end (ov-prev nil 'my-char 'o)))

(ov-prev 'my-char)
(ov-prev 'my-char 'o)
(ov-prev 300 'my-char)
(ov-prev (point) 'my-char 'o)
```

#### ov-goto-next `(&optional point-or-prop prop-or-point val)`

Move cursor to the end of the next overlay.
The arguments are the same as for `ov-next`.

```cl
(ov-goto-next)
(ov-goto-next 'face)
(ov-goto-next 'face 'warning)
(ov-goto-next 300 'face 'warning)
```

#### ov-goto-prev `(&optional point-or-prop prop-or-point val)`

Move cursor to the beginning of previous overlay.
The arguments are the same as for `ov-prev`.

```cl
(ov-goto-prev)
(ov-goto-prev 'face)
(ov-goto-prev 'face 'warning)
(ov-goto-prev 300 'face 'warning)
```

#### ov-keymap `(ov-or-ovs-or-id &rest keybinds)`

Set `keybinds` to an overlay or a list of overlays.

If `ov-or-ovs-or-id` is a symbol, the `keybinds` will be enabled for
the entire buffer and the property represented by the symbol to `t`.

The overlay is expanded if new inputs are inserted at the
beginning or end of the buffer.

Return: `overlay list` or `entire buffer overlay`

```cl
(setq ov1 (ov-match "ov-"))
(ov-set ov1 'face 'warning 'my-ov1 t)
(ov-keymap ov1
  "M-n" '(if (ov-goto-next 'my-ov1) (backward-char 1))
  "M-p" '(ov-goto-prev 'my-ov1))

(setq ov2 (ov-line))
(ov-set ov2 'face '(:box t))
(ov-keymap ov2
  "RET" '(let ((o (ov-at)))
           (if (memq :box (ov-val o 'face))
               (ov-set o 'face '(:underline t))
             (ov-set o 'face '(:box t)))))

(ov-keymap (ov-insert "{Press [C-t] here}") "C-t" 'describe-text-properties)

;; Enable keybind to the whole buffer
(ov-keymap 'my-ov-test1
  "M-n" 'move-end-of-line
  "M-p" 'move-beginning-of-line)
(ov-clear 'my-ov-test1)

;; Multiple keybinds to a command
(ov-keymap (ov-insert "HERE")
 '("a" "b") '(message "[a] or [b] is pressed")
 `(,(kbd "<mouse-1>") ,(kbd "M-c") "c") '(message "Clicked or [M-c] or c is pressed"))
```

#### ov-read-only `(ov-or-ovs &optional insert-in-front insert-behind)`

Implement a read-only like feature for overlay or list of overlays.

If `insert-in-front` is non-nil, inserting in front of each overlay is prevented.

If `insert-behind` is non-nil, inserting behind of each overlay is prevented.

Note that it allows modifications from out of range of a read-only overlay.

Return: `overlay list`

```cl
(setq ov1 (ov-match "setq"))
(ov-read-only ov1)

(ov-read-only (ov-insert "ReadOnly"))

;; Prevent inserting in front and behind of an overlay
(setq ov2 (ov-regexp "^;;"))
(ov-read-only ov2 t t)
```

#### ov-placeholder

Set a placeholder feature for overlay or list of overlays.

Each overlay deletes its string and overlay, when it is modified.

Return: `overlay list`

```cl
(ov-placeholder (ov-match ";; Try to insert or delete chars below"))
;; Try to insert or delete chars below

(ov-placeholder (ov-insert "[Placeholder]"))
```

#### ov-smear `(regexp-or-list &optional match-end base-color color-range)`

Set background color overlays to the current buffer.
Each background color is randomly determined based on BASE-COLOR or the default background color.

If REGEXP-OR-LIST is regexp
   Set overlays between matches of a regexp.

If REGEXP-OR-LIST is list
   Set overlays between point pairs in a list.

```cl
;; List
(ov-smear '((1 . 200) (200 . 450) (600 . 750)))

;; Regexp
(ov-smear "^;;" nil "#ff0000" 60)
(ov-smear "\n\n" t) ;; 2 returns and use match-end
(ov-smear "^#")     ;; for markdown-mode
(ov-smear "^\\*")   ;; for org-mode
;; for objc-mode
(ov-smear "^@\\(interface\\|implementation\\|end\\)\\|^#pragma")
```

![ov-smear](https://raw.githubusercontent.com/ShingoFukuyama/images/master/ov-smear.png)

## Useful examples

#### Sticky overlay

Sticky overlays will be inherited by inserting at both sides of each one.

```cl
(let ((ov-sticky-front t)
      (ov-sticky-rear t))
  (ov-set "ov-[^\s]+" 'face 'warning))
```

#### Evaporative overlay

When you modify one of the overlaid text, all their overlays will be evaporated.
`modification-hooks` requires function to specify 5 arguments.

```cl
(defun my-ov-evaporate-ov1 (_ov _after _beg _end &optional _length)
  (let ((inhibit-modification-hooks t))
    (if _after (ov-clear 'ov1))))
(ov-set "ov-" 'face 'warning
              'ov1 t
              'modification-hooks '(my-ov-evaporate-ov1))
```

## Contribute

Add new features or improve functions is welcome!

#### Add new functions

It would be helpful if you follow:

* "ov-" prefixed function name
* Simpler function name is preferable. (e.g "beg" > "beginning", "prop" > "property")
* Accept single overlay and multiple overlays in one argument, such as `ov-or-ovs` in existing functions
* Write examples and documents in README.md
* Write tests in /test/ov-test.el
* Use spaces as the indent instead of tabs

## Contributor

* [Matus Goljer](https://github.com/Fuco1) contributed to overhaul documents, and a lot of suggestions.

## Change

###### 2014/07/02
* Add [ov-smear](#ov-smear)
###### 2014/06/05
* Change `ov-keymap`'s keymapping property from `local-map` to `keymap`. By doing so, override the buffer local keymap instead of totaly replacing it.
###### 2014/06/05
* Change return value type of `ov-set`
* Add `ov-length` by Matus Goljer

## Reference

* :link: [Overlay Properties](http://www.gnu.org/software/emacs/manual/html_node/elisp/Overlay-Properties.html)
* :link: [Face Attributes](http://www.gnu.org/software/emacs/manual/html_node/elisp/Face-Attributes.html)
* :link: [Managing Overlays](http://www.gnu.org/software/emacs/manual/html_node/elisp/Managing-Overlays.html)
* :link: [comint read-only prompt](http://lists.gnu.org/archive/html/emacs-devel/2002-08/msg00428.html)



[melpa-link]: http://melpa.org/#/ov
[melpa-stable-link]: http://stable.melpa.org/#/ov
[melpa-badge]: http://melpa.org/packages/ov-badge.svg
[melpa-stable-badge]: http://stable.melpa.org/packages/ov-badge.svg
