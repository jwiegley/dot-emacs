;;; hexrgb.el --- Functions to manipulate colors, including RGB hex strings.
;;
;; Filename: hexrgb.el
;; Description: Functions to manipulate colors, including RGB hex strings.
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 2004-2012, Drew Adams, all rights reserved.
;; Created: Mon Sep 20 22:58:45 2004
;; Version: 21.0
;; Last-Updated: Sat Mar 17 19:00:37 2012 (-0700)
;;           By: dradams
;;     Update #: 897
;; URL: http://www.emacswiki.org/cgi-bin/wiki/hexrgb.el
;; Keywords: number, hex, rgb, color, background, frames, display
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x
;;
;; Features that might be required by this library:
;;
;;   None
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;  Functions to manipulate colors, including RGB hex strings.
;;
;;  This library provides functions for converting between RGB (red,
;;  green, blue) color components and HSV (hue, saturation, value)
;;  color components.  It helps you convert among Emacs color
;;  components (whole numbers from 0 through 65535), RGB and HSV
;;  floating-point components (0.0 through 1.0), Emacs color-name
;;  strings (such as "blue"), and hex RGB color strings (such as
;;  "#FC43A7912").
;;
;;  An RGB hex string, such as used as a frame `background-color'
;;  property, is a string of 1 + (3 * n) characters, the first of
;;  which is "#".  The other characters are hexadecimal digits, in
;;  three groups representing (from the left): red, green, and blue
;;  hex codes.
;;
;;  Constants defined here:
;;
;;    `hexrgb-defined-colors', `hexrgb-defined-colors-alist',
;;    `hexrgb-defined-colors-no-dups',
;;    `hexrgb-defined-colors-no-dups-alist'.
;;
;;  Options defined here:
;;
;;    `hexrgb-canonicalize-defined-colors-flag'.
;;
;;  Commands defined here:
;;
;;    `hexrgb-blue', `hexrgb-complement', `hexrgb-green',
;;    `hexrgb-hue', `hexrgb-read-color', `hexrgb-red',
;;    `hexrgb-saturation', `hexrgb-value'.
;;
;;  Non-interactive functions defined here:
;;
;;    `hexrgb-approx-equal', `hexrgb-canonicalize-defined-colors',
;;    `hexrgb-color-name-to-hex', `hexrgb-color-values-to-hex',
;;    `hexrgb-color-value-to-float', `hexrgb-defined-colors',
;;    `hexrgb-defined-colors-alist',
;;    `hexrgb-delete-whitespace-from-string',
;;    `hexrgb-float-to-color-value', `hexrgb-hex-char-to-integer',
;;    `hexrgb-hex-to-color-values', `hexrgb-hex-to-hex',
;;    `hexrgb-hex-to-hsv', `hexrgb-hex-to-rgb', `hexrgb-hsv-to-hex',
;;    `hexrgb-hex-to-int', `hexrgb-hsv-to-rgb',
;;    `hexrgb-increment-blue', `hexrgb-increment-equal-rgb',
;;    `hexrgb-increment-green', `hexrgb-increment-hex',
;;    `hexrgb-increment-red', `hexrgb-int-to-hex', `hexrgb-blue-hex',
;;    `hexrgb-green-hex', `hexrgb-red-hex', `hexrgb-rgb-hex-string-p',
;;    `hexrgb-rgb-hex-to-rgb-hex', `hexrgb-rgb-to-hex',
;;    `hexrgb-rgb-to-hsv'.
;;
;;
;;  Add this to your initialization file (~/.emacs or ~/_emacs):
;;
;;    (require 'hexrgb)
;;
;;  Do not try to use this library without a window manager.
;;  That is, do not use this with `emacs -nw'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change Log:
;;
;; 2012/03/17 dadams
;;     Added: hexrgb-(red|green|blue-hex, hexrgb-rgb-hex-to-rgb-hex, hexrgb-hex-to-hex.
;; 2012/01/05 dadams
;;     hexrgb-complement: Added optional arg MSG-P.
;;     Some doc-string cleanup.
;; 2011/11/26 dadams
;;     hexrgb-read-color: Changed arg order to match vanilla Emacs read-color.  Added MSGP.
;;     *** THIS IS AN INCOMPATIBLE CHANGE.  IF YOU USE THIS FUNCTION THEN UPDATE YOUR CODE. ***
;; 2011/02/16 dadams
;;     hexrgb-increment-hex: INCOMPATIBLE CHANGE:
;;                           Swapped order of args NB-DIGITS, INCREMENT, to fit other functions.
;;     hexrgb-increment-*: Took the change to hexrgb-increment-hex into account.
;;     Improved various doc strings.
;; 2011/01/08 dadams
;;     Restored autoload cookie for eval-and-compile hexrgb-canonicalize-defined-colors.
;; 2011/01/03 dadams
;;     Removed autoload cookies from non-interactive functions.
;; 2010/12/18 dadams
;;     hexrgb-canonicalize-defined-colors: Added autoload cookie.  Thx to Richard Kim.
;; 2010/12/06 dadams
;;     hexrgb-hex-to-color-values: Correct start offset for blue.  Thx to "Linda" on Emacs Wiki.
;; 2009/11/14 dadams
;;    hexrgb-rgb-to-hsv: Corrected hue when > 1.0.  Use strict inequality for hue limit tests.
;;    hexrgb-approx-equal: Convert RFUZZ and AFUZZ to their absolute values.
;; 2009/11/03 dadams
;;    Added: hexrgb-delete-whitespace-from-string, hexrgb-canonicalize-defined-colors,
;;           hexrgb-defined-colors(-no-dups)(-alist), hexrgb-canonicalize-defined-colors-flag.
;;    hexrgb-read-color: Use function hexrgb-defined-colors-alist, not the constant.
;; 2008/12/25 dadams
;;    hexrgb-rgb-to-hsv:
;;      Replace (not (equal 0.0e+NaN saturation)) by standard test (= saturation saturation).
;;      Thx to  Michael Heerdegen for the bug report.
;; 2008-10-17 dadams
;;    hexrgb-defined-colors(-alist): Prevent load-time error if user tries to use emacs -nw.
;; 2007/12/30 dadams
;;    Added: hexrgb-hex-to-color-values.
;; 2007/10/20 dadams
;;    hexrgb-read-color: Treat pseudo colors too (e.g. *point foreground*).
;; 2007/01/21 dadams
;;    hexrgb-read-color: Error if empty string (and not allow-empty-name-p).
;; 2006/06/06 dadams
;;    Added: hexrgb-defined-colors(-alist).  Use instead of (x-defined-colors).
;;    hexrgb-(red|green|blue): Added interactive specs.
;; 2006/06/04 dadams
;;    hexrgb-read-color: Added optional arg allow-empty-name-p.
;; 2006/06/02 dadams
;;    Added: hexrgb-rgb-hex-string-p.  Used it.
;; 2006/05/30 dadams
;;    Added: hexrgb-hex-to-(hsv|rgb), hexrgb-hsv-to-hex, hexrgb-color-name-to-hex,
;;           hexrgb-complement, hexrgb-read-color, hexrgb-hue, hexrgb-saturation,
;;           hexrgb-value, hexrgb-red, hexrgb-blue, hexrgb-green.
;;    approx-equal: Add optional fuzz factor arguments.  Changed the algorithm.
;;    Renamed: approx-equal to hexrgb-approx-equal.
;;    hexrgb-rgb-to-hsv: Changed test from < to <=: (when (<= hue 0.0)...).
;;    hexrgb-hsv-to-rgb: Treat hue = 0.0 (int 0) the same as hue = 1.0 (int 6).
;;    hexrgb-rgb-to-hex, hexrgb-increment-hex: Corrected doc strings.
;; 2006/05/22 dadams
;;    Added: hexrgb-hsv-to-hex, hexrgb-rgb-to-hex.  Require cl.el when byte-compile.
;; 2005/08/09 dadams
;;    hexrgb-rgb-to-hsv: Side-stepped Emacs-20 bug in comparing NaN.
;;    hexrgb-increment-*: Added optional arg wrap-p.
;;    hexrgb-increment-hex: Prevent wrap if not wrap-p.
;; 2005/08/02 dadams
;;    hexrgb-rgb-to-hes: Bug fix: If delta is zero, then so are hue and saturation.
;; 2005/06/24 dadams
;;    hexrgb-rgb-to-hsv: Bug fix: test for NaN (e.g. on divide by zero).
;; 2005/02/08 dadams
;;    hexrgb-hsv-to-rgb: Bug fix (typo: p, q -> pp, qq; added ww).
;; 2005/01/09 dadams
;;    hexrgb-int-to-hex: Fixed bug in hexrgb-int-to-hex: nb-digits not respected.
;;    Added: hexrgb-hsv-to-rgb, hexrgb-rgb-to-hsv, approx-equal.
;;    Renamed old hexrgb-increment-value to hexrgb-increment-equal-rgb.
;; 2005/01/05 dadams
;;    hexrgb-int-to-hex: Used a suggestion from Juri Linkov.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(eval-when-compile (require 'cl)) ;; case

;; Unless you first load `hexrgb.el', then either `palette.el' or `eyedropper.el', you will get
;; warnings about variables and functions with prefix `eyedrop-' when you byte-compile
;; `hexrgb.el'.  You can ignore these warnings.

(defvar eyedrop-picked-foreground)
(defvar eyedrop-picked-background)

;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;###autoload
(eval-and-compile
 (defun hexrgb-canonicalize-defined-colors (list)
   "Copy of LIST with color names canonicalized.
LIST is a list of color names (strings).
Canonical names are lowercase, with no whitespace.
There are no duplicate names."
   (let ((tail  list)
         this new)
     (while tail
       (setq this  (car tail)
             this  (hexrgb-delete-whitespace-from-string (downcase this) 0 (length this)))
       (unless (member this new) (push this new))
       (pop tail))
     (nreverse new)))

 (defun hexrgb-delete-whitespace-from-string (string &optional from to)
   "Remove whitespace from substring of STRING from FROM to TO.
If FROM is nil, then start at the beginning of STRING (FROM = 0).
If TO is nil, then end at the end of STRING (TO = length of STRING).
FROM and TO are zero-based indexes into STRING.
Character FROM is affected (possibly deleted).  Character TO is not."
   (setq from  (or from 0)
         to    (or to (length string)))
   (with-temp-buffer
     (insert string)
     (goto-char (+ from (point-min)))
     (let ((count  from)
           char)
       (while (and (not (eobp))  (< count to))
         (setq char  (char-after))
         (if (memq char '(?\  ?\t ?\n))  (delete-char 1)  (forward-char 1))
         (setq count  (1+ count)))
       (buffer-string)))))

;;;###autoload
(defconst hexrgb-defined-colors (eval-when-compile (and window-system (x-defined-colors)))
  "List of all supported colors.")

;;;###autoload
(defconst hexrgb-defined-colors-no-dups
    (eval-when-compile
     (and window-system (hexrgb-canonicalize-defined-colors (x-defined-colors))))
  "List of all supported color names, with no duplicates.
Names are all lowercase, without any spaces.")

;;;###autoload
(defconst hexrgb-defined-colors-alist
    (eval-when-compile (and window-system (mapcar #'list (x-defined-colors))))
  "Alist of all supported color names, for use in completion.
See also `hexrgb-defined-colors-no-dups-alist', which is the same
thing, but without any duplicates, such as \"light blue\" and
\"LightBlue\".")

;;;###autoload
(defconst hexrgb-defined-colors-no-dups-alist
    (eval-when-compile
     (and window-system
          (mapcar #'list (hexrgb-canonicalize-defined-colors (x-defined-colors)))))
  "Alist of all supported color names, with no duplicates, for completion.
Names are all lowercase, without any spaces.")

;;;###autoload
(defcustom hexrgb-canonicalize-defined-colors-flag t
  "*Non-nil means remove duplicate color names.
Names are considered duplicates if they are the same when abstracting
from whitespace and letter case."
  :type 'boolean
  :group 'Icicles :group 'doremi-frame-commands :group 'faces :group 'convenience)

;; You should use these two functions, not the constants, so users can change
;; the behavior by customizing `hexrgb-canonicalize-defined-colors-flag'.

(defun hexrgb-defined-colors ()
  "List of supported color names.
If `hexrgb-canonicalize-defined-colors-flag' is non-nil, then names
are lowercased, whitespace is removed, and there are no duplicates."
  (if hexrgb-canonicalize-defined-colors-flag
      hexrgb-defined-colors-no-dups
    hexrgb-defined-colors))

(defun hexrgb-defined-colors-alist ()
  "Alist of supported color names.  Usable for completion.
If `hexrgb-canonicalize-defined-colors-flag' is non-nil, then names
are lowercased, whitespace is removed, and there are no duplicates."
  (if hexrgb-canonicalize-defined-colors-flag
      hexrgb-defined-colors-no-dups-alist
    hexrgb-defined-colors-alist))

;; RMS added this function to Emacs (23) as `read-color', with some feature loss.
;;;###autoload
(defun hexrgb-read-color (&optional prompt convert-to-RGB-p allow-empty-name-p msgp)
  "Read a color name or hex RGB hexadecimal color value #RRRRGGGGBBBB.
Completion is available for color names, but not for RGB hex strings.
If you input an RGB hex string, it must have the form #XXXXXXXXXXXX or
XXXXXXXXXXXX, where each X is a hex digit.  The number of Xs must be a
multiple of 3, with the same number of Xs for each of red, green, and
blue.  The order is red, green, blue.

Color names that are normally considered equivalent are canonicalized:
They are lowercased, whitespace is removed, and duplicates are
eliminated.  E.g. \"LightBlue\" and \"light blue\" are both replaced
by \"lightblue\".  If you do not want this behavior, but want to
choose names that might contain whitespace or uppercase letters, then
customize option `hexrgb-canonicalize-defined-colors-flag' to nil.

In addition to standard color names and RGB hex values, the following
are available as color candidates.  In each case, the corresponding
color is used.

* `*copied foreground*'  - last copied foreground, if available
* `*copied background*'  - last copied background, if available
* `*mouse-2 foreground*' - foreground where you click `mouse-2'
* `*mouse-2 background*' - background where you click `mouse-2'
* `*point foreground*'   - foreground under the cursor
* `*point background*'   - background under the cursor

\(You can copy a color using eyedropper commands such as
`eyedrop-pick-foreground-at-mouse'.)

Optional arg PROMPT is the prompt - nil means use a default prompt.

Checks input to be sure it represents a valid color.  If not, raises
an error (but see exception for empty input with non-nil
ALLOW-EMPTY-NAME-P).

Interactively, or with optional arg CONVERT-TO-RGB-P non-nil, converts
an input color name to an RGB hex string.  Returns the RGB hex string.

Optional arg ALLOW-EMPTY-NAME-P controls what happens if you enter an
empty color name (that is, you just hit `RET').  If non-nil, then
`hexrgb-read-color' returns an empty color name, \"\".  If nil, then
it raises an error.  Calling programs must test for \"\" if
ALLOW-EMPTY-NAME-P is non-nil.  They can then perform an appropriate
action in case of empty input.

Interactively, or with non-nil MSGP, show color name in the echo area."
  (interactive "i\np\ni\np")             ; Always convert to RGB interactively.
  (let* ((completion-ignore-case  t)
         ;; Free variables here: `eyedrop-picked-foreground', `eyedrop-picked-background'.
         ;; They are defined in library `palette.el' or library `eyedropper.el'.
         (colors                  (if (fboundp 'eyedrop-foreground-at-point)
                                      (append (and eyedrop-picked-foreground
                                                   '(("*copied foreground*")))
                                              (and eyedrop-picked-background
                                                   '(("*copied background*")))
                                              '(("*mouse-2 foreground*")
                                                ("*mouse-2 background*")
                                                ("*point foreground*") ("*point background*"))
                                              (hexrgb-defined-colors-alist))
                                    (hexrgb-defined-colors-alist)))
         (color                   (completing-read (or prompt "Color (name or #R+G+B+): ")
                                                   colors))
         hex-string)
    (when (fboundp 'eyedrop-foreground-at-point)
      (cond ((string= "*copied foreground*" color) (setq color  eyedrop-picked-foreground))
            ((string= "*copied background*" color) (setq color  eyedrop-picked-background))
            ((string= "*point foreground*" color)  (setq color  (eyedrop-foreground-at-point)))
            ((string= "*point background*" color)  (setq color  (eyedrop-background-at-point)))
            ((string= "*mouse-2 foreground*" color)
             (setq color  (prog1 (eyedrop-foreground-at-mouse
                                  (read-event "Click `mouse-2' to choose foreground color - "))
                            (read-event)))) ; Discard mouse up event.
            ((string= "*mouse-2 background*" color)
             (setq color  (prog1 (eyedrop-background-at-mouse
                                  (read-event "Click `mouse-2' to choose background color - "))
                            (read-event)))))) ; Discard mouse up event.
    (setq hex-string  (or (string-match "^#\\([a-fA-F0-9][a-fA-F0-9][a-fA-F0-9]\\)+$" color)
                          (and (string-match "^\\([a-fA-F0-9][a-fA-F0-9][a-fA-F0-9]\\)+$" color)
                               t)))
    (if (and allow-empty-name-p (string= "" color))
        ""
      (when (and hex-string (not (eq 0 hex-string)))
        (setq color  (concat "#" color))) ; No #; add it.
      (unless hex-string
        (when (or (string= "" color)
                  (not (if (fboundp 'test-completion) ; Not defined in Emacs 20.
                           (test-completion color colors)
                         (try-completion color colors))))
          (error "No such color: %S" color))
        (when convert-to-RGB-p (setq color  (hexrgb-color-name-to-hex color))))
      (when msgp (message "Color: `%s'" color))
      color)))

(defun hexrgb-rgb-hex-string-p (color &optional laxp)
  "Non-nil if COLOR is an RGB string #XXXXXXXXXXXX.
Each X is a hex digit.  The number of Xs must be a multiple of 3, with
the same number of Xs for each of red, green, and blue.

Non-nil optional arg LAXP means that the initial `#' is optional.  In
that case, for a valid string of hex digits: when # is present 0 is
returned; otherwise, t is returned."
  (or (string-match "^#\\([a-fA-F0-9][a-fA-F0-9][a-fA-F0-9]\\)+$" color)
      (and laxp (string-match "^\\([a-fA-F0-9][a-fA-F0-9][a-fA-F0-9]\\)+$" color) t)))

;;;###autoload
(defun hexrgb-complement (color &optional msg-p)
  "Return the color that is the complement of COLOR.
Non-interactively, non-nil optional arg MSG-P means show a message
with the complement."
  (interactive (list (hexrgb-read-color) t))
  (setq color  (hexrgb-color-name-to-hex color))
  (let ((red    (hexrgb-red color))
        (green  (hexrgb-green color))
        (blue   (hexrgb-blue color)))
    (setq color  (hexrgb-rgb-to-hex (- 1.0 red) (- 1.0 green) (- 1.0 blue))))
  (when msg-p (message "Complement: `%s'" color))
  color)

;;;###autoload
(defun hexrgb-hue (color)
  "Return the hue component of COLOR, in range 0 to 1 inclusive.
COLOR is a color name or hex RGB string that starts with \"#\"."
  (interactive (list (hexrgb-read-color)))
  (setq color  (hexrgb-color-name-to-hex color))
  (car (hexrgb-rgb-to-hsv (hexrgb-red color) (hexrgb-green color) (hexrgb-blue color))))

;;;###autoload
(defun hexrgb-saturation (color)
  "Return the saturation component of COLOR, in range 0 to 1 inclusive.
COLOR is a color name or hex RGB string that starts with \"#\"."
  (interactive (list (hexrgb-read-color)))
  (setq color  (hexrgb-color-name-to-hex color))
  (cadr (hexrgb-rgb-to-hsv (hexrgb-red color) (hexrgb-green color) (hexrgb-blue color))))

;;;###autoload
(defun hexrgb-value (color)
  "Return the value component of COLOR, in range 0 to 1 inclusive.
COLOR is a color name or hex RGB string that starts with \"#\"."
  (interactive (list (hexrgb-read-color)))
  (setq color  (hexrgb-color-name-to-hex color))
  (caddr (hexrgb-rgb-to-hsv (hexrgb-red color) (hexrgb-green color) (hexrgb-blue color))))

;;;###autoload
(defun hexrgb-red (color)
  "Return the red component of COLOR, in range 0 to 1 inclusive.
COLOR is a color name or hex RGB string that starts with \"#\"."
  (interactive (list (hexrgb-read-color)))
  (setq color  (hexrgb-color-name-to-hex color))
  (/ (hexrgb-hex-to-int (substring color 1 (1+ (/ (1- (length color)) 3))))
     (expt 16.0 (/ (1- (length color)) 3.0))))

;;;###autoload
(defun hexrgb-green (color)
  "Return the green component of COLOR, in range 0 to 1 inclusive.
COLOR is a color name or hex RGB string that starts with \"#\"."
  (interactive (list (hexrgb-read-color)))
  (setq color  (hexrgb-color-name-to-hex color))
  (let* ((len    (/ (1- (length color)) 3))
         (start  (1+ len)))
    (/ (hexrgb-hex-to-int (substring color start (+ start len)))
       (expt 16.0 (/ (1- (length color)) 3.0)))))

;;;###autoload
(defun hexrgb-blue (color)
  "Return the blue component of COLOR, in range 0 to 1 inclusive.
COLOR is a color name or hex RGB string that starts with \"#\"."
  (interactive (list (hexrgb-read-color)))
  (setq color  (hexrgb-color-name-to-hex color))
  (let* ((len    (/ (1- (length color)) 3))
         (start  (+ 1 len len)))
    (/ (hexrgb-hex-to-int (substring color start (+ start len)))
       (expt 16.0 (/ (1- (length color)) 3.0)))))

(defun hexrgb-rgb-to-hsv (red green blue)
  "Convert RED, GREEN, BLUE components to HSV (hue, saturation, value).
Each input component is 0.0 to 1.0, inclusive.
Returns a list of HSV components of value 0.0 to 1.0, inclusive."
  (let* ((min    (min red green blue))
         (max    (max red green blue))
         (value  max)
         (delta  (- max min))
         hue saturation)
    (if (hexrgb-approx-equal 0.0 delta)
        (setq hue         0.0
              saturation  0.0)          ; Gray scale - no color; only value.
      (if (and (condition-case nil
                   (setq saturation  (/ delta max))
                 (arith-error nil))
               ;; Must be a number, not a NaN.  The standard test for a NaN is (not (= N N)),
               ;; but an Emacs 20 bug makes (= N N) return t for a NaN also.
               (or (< emacs-major-version 21) (= saturation saturation)))                
          (if (hexrgb-approx-equal 0.0 saturation)
              (setq hue         0.0
                    saturation  0.0)    ; Again, no color; only value.
            ;; Color
            (setq hue  (if (hexrgb-approx-equal red max)
                           (/ (- green blue) delta) ; Between yellow & magenta.
                         (if (hexrgb-approx-equal green max)
                             (+ 2.0 (/ (- blue red) delta)) ; Between cyan & yellow.
                           (+ 4.0 (/ (- red green) delta)))) ; Between magenta & cyan.
                  hue  (/ hue 6.0))
            ;; (when (<= hue 0.0) (setq hue  (+ hue 1.0)))  ; $$$$$$
            ;; (when (>= hue 1.0) (setq hue  (- hue 1.0)))) ; $$$$$$
            (when (< hue 0.0) (setq hue  (+ hue 1.0)))
            (when (> hue 1.0) (setq hue  (- hue 1.0))))
        (setq hue         0.0           ; Div by zero (max=0): H:=0, S:=0. (Hue undefined.)
              saturation  0.0)))
    (list hue saturation value)))

(defun hexrgb-hsv-to-rgb (hue saturation value)
  "Convert HUE, SATURATION, VALUE components to RGB (red, green, blue).
Each input component is 0.0 to 1.0, inclusive.
Returns a list of RGB components of value 0.0 to 1.0, inclusive."
  (let (red green blue int-hue fract pp qq tt ww)
    (if (hexrgb-approx-equal 0.0 saturation)
        (setq red    value
              green  value
              blue   value)             ; Gray
      (setq hue      (* hue 6.0)        ; Sectors: 0 to 5
            int-hue  (floor hue)
            fract    (- hue int-hue)
            pp       (* value (- 1 saturation))
            qq       (* value (- 1 (* saturation fract)))
            ww       (* value (- 1 (* saturation (- 1 (- hue int-hue))))))
      (case int-hue
        ((0 6) (setq red    value
                     green  ww
                     blue   pp))
        (1 (setq red    qq
                 green  value
                 blue   pp))
        (2 (setq red    pp
                 green  value
                 blue   ww))
        (3 (setq red    pp
                 green  qq
                 blue   value))
        (4 (setq red    ww
                 green  pp
                 blue   value))
        (otherwise (setq red    value
                         green  pp
                         blue   qq))))
    (list red green blue)))

(defun hexrgb-hsv-to-hex (hue saturation value)
  "Return the hex RBG color string for inputs HUE, SATURATION, VALUE.
The inputs are each in the range 0 to 1.
The output string is of the form \"#RRRRGGGGBBBB\"."
  (hexrgb-color-values-to-hex
   (mapcar (lambda (x) (floor (* x 65535.0))) (hexrgb-hsv-to-rgb hue saturation value))))

(defun hexrgb-rgb-to-hex (red green blue)
  "Return the hex RBG color string for inputs RED, GREEN, BLUE.
The inputs are each in the range 0 to 1.
The output string is of the form \"#RRRRGGGGBBBB\"."
  (hexrgb-color-values-to-hex
   (mapcar (lambda (x) (floor (* x 65535.0))) (list red green blue))))

(defun hexrgb-hex-to-hsv (color)
  "Return a list of HSV (hue, saturation, value) color components.
Each component is a value from 0.0 to 1.0, inclusive.
COLOR is a color name or a hex RGB string that starts with \"#\" and
is followed by an equal number of hex digits for red, green, and blue
components."
  (let ((rgb-components  (hexrgb-hex-to-rgb color)))
    (apply #'hexrgb-rgb-to-hsv rgb-components)))

(defun hexrgb-hex-to-rgb (color)
  "Return a list of RGB (red, green, blue) color components.
Each component is a value from 0.0 to 1.0, inclusive.
COLOR is a color name or a hex RGB string that starts with \"#\" and
is followed by an equal number of hex digits for red, green, and blue
components."
  (unless (hexrgb-rgb-hex-string-p color) (setq color  (hexrgb-color-name-to-hex color)))
  (let ((len  (/ (1- (length color)) 3)))
    (list (/ (hexrgb-hex-to-int (substring color 1 (1+ len))) 65535.0)
          (/ (hexrgb-hex-to-int (substring color (1+ len) (+ 1 len len))) 65535.0)
          (/ (hexrgb-hex-to-int (substring color (+ 1 len len))) 65535.0))))

(defun hexrgb-color-name-to-hex (color)
  "Return the RGB hex string for the COLOR name, starting with \"#\".
If COLOR is already a string starting with \"#\", then just return it."
  (let ((components  (x-color-values color)))
    (unless components (error "No such color: %S" color))
    (unless (hexrgb-rgb-hex-string-p color)
      (setq color  (hexrgb-color-values-to-hex components))))
  color)

;; Color "components" would be better in the name than color "value"
;; but this name follows the Emacs tradition (e.g. `x-color-values',
;; 'ps-color-values', `ps-e-x-color-values').
(defun hexrgb-color-values-to-hex (components)
  "Convert list of rgb color COMPONENTS to a hex string, #XXXXXXXXXXXX.
Each X in the string is a hexadecimal digit.
Input COMPONENTS is as for the output of `x-color-values'."
;; Just hard-code 4 as the number of hex digits, since `x-color-values'
;; seems to produce appropriate integer values for `4'.
  (concat "#" (hexrgb-int-to-hex (nth 0 components) 4) ; red
          (hexrgb-int-to-hex (nth 1 components) 4) ; green
          (hexrgb-int-to-hex (nth 2 components) 4))) ; blue

(defun hexrgb-hex-to-color-values (color)
  "Convert hex COLOR to a list of RGB color components.
COLOR is a hex rgb color string, #XXXXXXXXXXXX
Each X in the string is a hexadecimal digit.  There are 3N X's, N > 0.
The output list is as for `x-color-values'."
  (let* ((hex-strgp  (string-match
                      "^\\(#\\)?\\(\\([a-fA-F0-9][a-fA-F0-9][a-fA-F0-9]\\)+\\)$"
                      color))
         (ndigits    (/ (if (eq (match-beginning 1) (match-end 1))
                            (length color)
                          (1- (length color)))
                        3))
         red green blue)
    (unless hex-strgp (error "Invalid RGB color string: %s" color))
    (setq color  (substring color (match-beginning 2) (match-end 2))
          red    (hexrgb-hex-to-int (substring color 0 ndigits))
          green  (hexrgb-hex-to-int (substring color ndigits (* 2 ndigits)))
          blue   (hexrgb-hex-to-int (substring color (* 2 ndigits) (* 3 ndigits))))
    (list red green blue)))
    
(defun hexrgb-increment-red (hex nb-digits increment &optional wrap-p)
  "Increment red component of rgb string HEX by INCREMENT.
String HEX starts with \"#\".  Each color is NB-DIGITS hex digits long.
If optional arg WRAP-P is non-nil then the result wraps around zero.
  For example, with NB-DIGITS 3, incrementing \"#fffffffff\" by 1
  causes it to wrap around to \"#000ffffff\"."
  (concat "#"
          (hexrgb-increment-hex (substring hex 1 (1+ nb-digits)) nb-digits increment wrap-p)
          (substring hex (1+ nb-digits) (1+ (* nb-digits 2)))
          (substring hex (1+ (* nb-digits 2)))))

(defun hexrgb-increment-green (hex nb-digits increment &optional wrap-p)
  "Increment green component of rgb string HEX by INCREMENT.
String HEX starts with \"#\".  Each color is NB-DIGITS hex digits long.
If optional arg WRAP-P is non-nil then the result wraps around zero.
  For example, with NB-DIGITS 3, incrementing \"#fffffffff\" by 1
  causes it to wrap around to \"#fff000fff\"."
  (concat
   "#" (substring hex 1 (1+ nb-digits))
   (hexrgb-increment-hex (substring hex (1+ nb-digits) (1+ (* nb-digits 2)))
                         nb-digits
                         increment
                         wrap-p)
   (substring hex (1+ (* nb-digits 2)))))

(defun hexrgb-increment-blue (hex nb-digits increment &optional wrap-p)
  "Increment blue component of rgb string HEX by INCREMENT.
String HEX starts with \"#\".  Each color is NB-DIGITS hex digits long.
If optional arg WRAP-P is non-nil then the result wraps around zero.
  For example, with NB-DIGITS 3, incrementing \"#fffffffff\" by 1
  causes it to wrap around to \"#ffffff000\"."
  (concat "#" (substring hex 1 (1+ (* nb-digits 2)))
          (hexrgb-increment-hex (substring hex (1+ (* nb-digits 2)))
                                nb-digits
                                increment
                                wrap-p)))

(defun hexrgb-increment-equal-rgb (hex nb-digits increment &optional wrap-p)
  "Increment each color component (r,g,b) of rgb string HEX by INCREMENT.
String HEX starts with \"#\".  Each color is NB-DIGITS hex digits long.
If optional arg WRAP-P is non-nil then the result wraps around zero.
  For example, with NB-DIGITS 3, incrementing \"#fffffffff\" by 1
  causes it to wrap around to \"#000000000\"."
  (concat
   "#"
   (hexrgb-increment-hex (substring hex 1 (1+ nb-digits)) nb-digits increment wrap-p)
   (hexrgb-increment-hex (substring hex (1+ nb-digits) (1+ (* nb-digits 2)))
                         nb-digits
                         increment
                         wrap-p)
   (hexrgb-increment-hex (substring hex (1+ (* nb-digits 2))) nb-digits increment wrap-p)))

(defun hexrgb-increment-hex (hex nb-digits increment &optional wrap-p)
  "Increment hexadecimal-digits string HEX by INCREMENT.
Only the first NB-DIGITS of HEX are used.
If optional arg WRAP-P is non-nil then the result wraps around zero.
  For example, with NB-DIGITS 3, incrementing \"fff\" by 1 causes it
  to wrap around to \"000\"."
  (let* ((int      (hexrgb-hex-to-int hex))
         (new-int  (+ increment int)))
    (if (or wrap-p
            (and (>= int 0)             ; Not too large for the machine.
                 (>= new-int 0)         ; For the case where increment < 0.
                 (<= (length (format (concat "%X") new-int)) nb-digits))) ; Not too long.
        (hexrgb-int-to-hex new-int nb-digits) ; Use incremented number.
      hex)))                            ; Don't increment.

(defun hexrgb-hex-to-int (hex)
  "Convert HEX string argument to an integer.
The characters of HEX must be hex characters."
  (let* ((factor  1)
         (len     (length hex))
         (indx    (1- len))
         (int     0))
    (while (>= indx 0)
      (setq int     (+ int (* factor (hexrgb-hex-char-to-integer (aref hex indx))))
            indx    (1- indx)
            factor  (* 16 factor)))
    int))

;; From `hexl.el'.  This is the same as `hexl-hex-char-to-integer' defined there.
(defun hexrgb-hex-char-to-integer (character)
  "Take a CHARACTER and return its value as if it were a hex digit."
  (if (and (>= character ?0) (<= character ?9))
      (- character ?0)
    (let ((ch  (logior character 32)))
      (if (and (>= ch ?a) (<= ch ?f))
          (- ch (- ?a 10))
        (error "Invalid hex digit `%c'" ch)))))

;; Originally, I used the code from `int-to-hex-string' in `float.el'.
;; This version is thanks to Juri Linkov <juri@jurta.org>.
;;
(defun hexrgb-int-to-hex (int &optional nb-digits)
  "Convert integer argument INT to a #XXXXXXXXXXXX format hex string.
Each X in the output string is a hexadecimal digit.
NB-DIGITS is the number of hex digits.  If INT is too large to be
represented with NB-DIGITS, then the result is truncated from the
left.  So, for example, INT=256 and NB-DIGITS=2 returns \"00\", since
the hex equivalent of 256 decimal is 100, which is more than 2 digits."
  (setq nb-digits  (or nb-digits 4))
  (substring (format (concat "%0" (int-to-string nb-digits) "X") int) (- nb-digits)))

;; Inspired by Elisp Info manual, node "Comparison of Numbers".
(defun hexrgb-approx-equal (x y &optional rfuzz afuzz)
  "Return non-nil if numbers X and Y are approximately equal.
RFUZZ is a relative fuzz factor.  AFUZZ is an absolute fuzz factor.
RFUZZ defaults to 1.0e-8.  AFUZZ defaults to (/ RFUZZ 10).
RFUZZ and AFUZZ are converted to their absolute values.
The algorithm is:
 (< (abs (- X Y)) (+ AFUZZ (* RFUZZ (+ (abs X) (abs Y)))))."
  (setq rfuzz  (or rfuzz 1.0e-8)
        rfuzz  (abs rfuzz)
        afuzz  (or afuzz (/ rfuzz 10))
        afuzz  (abs afuzz))
  (< (abs (- x y)) (+ afuzz (* rfuzz (+ (abs x) (abs y))))))

(defun hexrgb-color-value-to-float (n)
  "Return the floating-point equivalent of color-component value N.
N must be an integer between 0 and 65535, or else an error is raised."
  (unless (and (wholenump n) (<= n 65535))
    (error "Not a whole number less than 65536"))
  (/ (float n) 65535.0))

(defun hexrgb-hex-to-hex (hex nb-digits)
  "Return a hex string of NB-DIGITS digits, rounded from hex string HEX.
Raise an error if HEX represents a number > `most-positive-fixnum'
HEX is a hex string, not an RGB string.  It does not start with `#'."
  (let* ((len      (length hex))
         (digdiff  (- nb-digits len)))
    (cond ((zerop digdiff)
           hex)
          ((natnump digdiff)
           (let ((int  (hexrgb-hex-to-int hex)))
             (unless (natnump int) (error "HEX number is too large"))
             (format (concat "%0" (int-to-string len) "X" (make-string digdiff ?0)) int)))
          (t
           (let ((over  (substring hex digdiff)))
             (setq hex  (substring hex 0 nb-digits))
             (if (> (string-to-number over 16)
                    (string-to-number (make-string (- digdiff) ?7) 16))
                 (hexrgb-increment-hex hex nb-digits 1) ; Round up.
               hex))))))

(defun hexrgb-rgb-hex-to-rgb-hex (hex nb-digits)
  "Trim or expand hex RGB string HEX to NB-DIGITS digits.
HEX can optionally start with `#'.
In that case, so does the return value."
  (let* ((nb-sign-p  (eq ?# (aref hex 0)))
         (hex+       (or (and nb-sign-p  hex)  (concat "#" hex)))
         (red        (hexrgb-red-hex   hex+))
         (green      (hexrgb-green-hex hex+))
         (blue       (hexrgb-blue-hex  hex+)))
    (format "%s%s%s%s"
            (if nb-sign-p "#" "")
            (hexrgb-hex-to-hex red   nb-digits)
            (hexrgb-hex-to-hex green nb-digits)
            (hexrgb-hex-to-hex blue  nb-digits))))

(defun hexrgb-red-hex (hex)
  "Return the red hex component for RGB string HEX.
HEX can optionally start with `#'.  The return value does not."
  (let* ((nb-sign-p  (eq ?# (aref hex 0)))
         (hex-       (or (and nb-sign-p  (substring hex 1))  hex)))
    (substring hex- 0 (/ (length hex-) 3))))

(defun hexrgb-green-hex (hex)
  "Return the green hex component for RGB string HEX.
HEX can optionally start with `#'.  The return value does not."
  (let* ((nb-sign-p  (eq ?# (aref hex 0)))
         (hex-       (or (and nb-sign-p  (substring hex 1))  hex))
         (len        (/ (length hex-) 3)))
    (substring hex- len (* 2 len))))

(defun hexrgb-blue-hex (hex)
  "Return the blue hex component for RGB string HEX.
HEX can optionally start with `#'.  The return value does not."
  (let* ((nb-sign-p  (eq ?# (aref hex 0)))
         (hex-       (or (and nb-sign-p  (substring hex 1))  hex))
         (len        (/ (length hex-) 3)))
    (substring hex- (* 2 len))))

(defun hexrgb-float-to-color-value (x)
  "Return the color-component value equivalent of floating-point number X.
X must be between 0.0 and 1.0, or else an error is raised."
  (unless (and (numberp x) (<= 0.0 x) (<= x 1.0))
    (error "Not a floating-point number between 0.0 and 1.0"))
  (floor (* x 65535.0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide 'hexrgb)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; hexrgb.el ends here
