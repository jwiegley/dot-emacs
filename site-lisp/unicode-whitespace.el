;;; unicode-whitespace.el --- teach whitespace-mode about fancy characters
;;
;; Copyright (c) 2012 Roland Walker
;;
;; Author: Roland Walker <walker@pobox.com>
;; Homepage: http://github.com/rolandwalker/unicode-whitespace
;; URL: http://raw.github.com/rolandwalker/unicode-whitespace/master/unicode-whitespace.el
;; Version: 0.2.3
;; Last-Updated: 14 Sep 2012
;; EmacsWiki: UnicodeWhitespace
;; Package-Requires: ((ucs-utils "0.7.2") (persistent-soft "0.8.6") (pcache "0.2.3"))
;; Keywords: faces, wp, interface
;;
;; Simplified BSD License
;;
;;; Commentary:
;;
;; Quickstart
;;
;;     (require 'unicode-whitespace)
;;
;;     (unicode-whitespace-setup 'subdued-faces)
;;
;;     M-x whitespace-mode RET
;;
;; Explanation
;;
;; Unicode-whitespace makes `whitespace-mode' Unicode-aware in two
;; different ways:
;;
;;     1. Recognizing Unicode whitespace characters in your buffer,
;;        such as "No-Break Space" or "Hair Space".
;;
;;     2. Displaying Unicode characters such as "Paragraph Sign"
;;        (pilcrow) in place of whitespace.
;;
;; This library also makes some minor adjustments to the default
;; settings of `whitespace-mode', and exposes character-by-character
;; display substitution mappings in customize.
;;
;; To use unicode-whitespace, place the unicode-whitespace.el library
;; somewhere Emacs can find it, and add the following to your ~/.emacs
;; file:
;;
;;     (require 'unicode-whitespace)
;;     (unicode-whitespace-setup 'subdued-faces)  ; 'subdued-faces is optional
;;
;; Then invoke `whitespace-mode' as usual.
;;
;; The display of newlines is changed from the default.  Newlines are
;; not displayed unless one of the following conditions is met:
;;
;;     1. `truncate-lines' is non-nil
;;
;;     2. `word-wrap' is non-nil
;;
;;     3. The major mode of the buffer is listed in
;;        `unicode-whitespace-newline-mark-modes'.
;;
;; A new `whitespace-style' is provided: 'echo causes the name of the
;; whitespace character under the point to be displayed in the echo
;; area.  This is not enabled by default.
;;
;; Two interactive commands are provided to manipulate these settings
;; when `whitespace-mode' is active:
;;
;;     `unicode-whitespace-toggle-newlines'
;;     `unicode-whitespace-toggle-echo'
;;
;; See Also
;;
;;     M-x customize-group RET unicode-whitespace RET
;;     M-x customize-group RET whitespace RET
;;
;; Notes
;;
;;     If the extended characters used to represent whitespace do
;;     not display correctly on your system, install unicode-fonts.el
;;     and/or read the setup tips therein.
;;
;;     Be aware when setting customizable variables for `whitespace-mode'
;;     that unicode-whitespace works by overwriting those same variables.
;;
;;     Unicode-whitespace causes alternative line terminators such as
;;     "Line Separator" to visually break lines so long as
;;     `whitespace-mode' is on.  Extra newline characters are not
;;     inserted.  This is a visual effect only, which ceases when
;;     `whitespace-mode' is turned off.
;;
;;     Unicode-whitespace turns off the long-line indicators built
;;     into whitespace-mode because of a font-lock bug.  To reverse
;;     this, do
;;
;;         (add-to-list 'whitespace-styles 'lines)
;;
;;     or use a separate long-lines detection package.
;;
;; Compatibility and Requirements
;;
;;     GNU Emacs version 24.3-devel     : yes, at the time of writing
;;     GNU Emacs version 24.1 & 24.2    : yes
;;     GNU Emacs version 23.3           : yes
;;     GNU Emacs version 22.3 and lower : no
;;
;;     Requires ucs-utils.el
;;
;;     Uses if present: unicode-fonts.el
;;
;; Bugs
;;
;;     Gray faces won't look good on a gray background such as that
;;     used by Zenburn color theme.  Does Zenburn set background to
;;     light or dark?  Provide a way to force faces?
;;
;;     The face for alternative line terminators is often incorrect;
;;     font-lock overrides the settings from unicode-whitespace.  This
;;     is because `whitespace-display-char-on' hardcodes \n as the
;;     line terminator.
;;
;;     Calling alternative line terminators 'space-mark is a hack to
;;     make it possible to toggle display of standard newlines
;;     without affecting the alternates.  They really should all be
;;     called newline-mark.  whitespace.el could be updated to
;;     allow this.
;;
;;     Trailing space that ends with \r or \f sometimes does not get
;;     fontified -- though it usually get picked up after some
;;     typing.  This could be because of some assumptions in the
;;     post-command-hook of whitespace.el.
;;
;;
;; TODO
;;
;;     There should be separate faces for each of these classes, would
;;     need to patch or override whitespace.el
;;
;;         unicode-whitespace-tab-names
;;         unicode-whitespace-tab-set-names
;;         unicode-whitespace-soft-space-names
;;         unicode-whitespace-hard-space-names
;;         unicode-whitespace-pseudo-space-names
;;         unicode-whitespace-standard-line-terminator-names
;;         unicode-whitespace-alternative-line-terminator-names
;;         form feed
;;
;;     There are probably more nonprinting characters to include as
;;     pseudo-spaces by default.  A list of glyphless chars could be
;;     gotten from variable `glyphless-char-display'.
;;
;;     Regexps should probably be redone with only \t for certain
;;     things.
;;
;;     A whitespace-cycle command could turn on the mode and cycle
;;     through a few levels of visibility.
;;
;;     Add a test function that dumps an extended example to scratch
;;     buffer.
;;
;;     Consistent marker symbol for thin spaces, and a way to see the
;;     intersection between thin and nonbreaking - maybe nonbreaking
;;     should be a consistent face and thin a consistent symbol.
;;
;;     The tab-visibility bug in whitespace.el could probably be fixed
;;     with an overlay.  Also, stipple can show tabs as arrows without
;;     changing display, seen here (http://emacswiki.org/emacs/BlankMode).
;;     However, the stipple face is dependent on frame-char-width/height.
;;
;;; License
;;
;; Simplified BSD License:
;;
;; Redistribution and use in source and binary forms, with or
;; without modification, are permitted provided that the following
;; conditions are met:
;;
;;    1. Redistributions of source code must retain the above
;;       copyright notice, this list of conditions and the following
;;       disclaimer.
;;
;;    2. Redistributions in binary form must reproduce the above
;;       copyright notice, this list of conditions and the following
;;       disclaimer in the documentation and/or other materials
;;       provided with the distribution.
;;
;; This software is provided by Roland Walker "AS IS" and any express
;; or implied warranties, including, but not limited to, the implied
;; warranties of merchantability and fitness for a particular
;; purpose are disclaimed.  In no event shall Roland Walker or
;; contributors be liable for any direct, indirect, incidental,
;; special, exemplary, or consequential damages (including, but not
;; limited to, procurement of substitute goods or services; loss of
;; use, data, or profits; or business interruption) however caused
;; and on any theory of liability, whether in contract, strict
;; liability, or tort (including negligence or otherwise) arising in
;; any way out of the use of this software, even if advised of the
;; possibility of such damage.
;;
;; The views and conclusions contained in the software and
;; documentation are those of the authors and should not be
;; interpreted as representing official policies, either expressed
;; or implied, of Roland Walker.
;;
;;; Code:
;;

;;; requires

(require 'whitespace)

(autoload 'ucs-utils-char                "ucs-utils"    "Return the character corresponding to NAME, a UCS name.")
(autoload 'ucs-utils-string              "ucs-utils"    "Return a string corresponding to SEQUENCE of UCS names or characters.")
(autoload 'ucs-utils-pretty-name         "ucs-utils"    "Return a prettified UCS name for CHAR.")
(autoload 'ucs-utils-first-existing-char "ucs-utils"    "Return the first existing element in SEQUENCE of character names.")

;;; variables

(defvar unicode-whitespace-saved-show-trailing nil "Hold the value of `show-trailing-whitespace'.")
(make-variable-buffer-local 'unicode-whitespace-saved-show-trailing)

(defvar unicode-whitespace-last-point nil "Track the point to avoid needless echo.")
(make-variable-buffer-local 'unicode-whitespace-last-point)

(defvar unicode-whitespace-all-whitespace-regexp nil "Regexp matching any type of whitespace.")

(defvar unicode-whitespace-subdued-empty             'unicode-whitespace-subdued-empty             "Face variable to make font-lock happy.")
(defvar unicode-whitespace-subdued-trailing          'unicode-whitespace-subdued-trailing          "Face variable to make font-lock happy.")
(defvar unicode-whitespace-subdued-indentation       'unicode-whitespace-subdued-indentation       "Face variable to make font-lock happy.")
(defvar unicode-whitespace-subdued-space-after-tab   'unicode-whitespace-subdued-space-after-tab   "Face variable to make font-lock happy.")
(defvar unicode-whitespace-subdued-space-before-tab  'unicode-whitespace-subdued-space-before-tab  "Face variable to make font-lock happy.")
(defvar unicode-whitespace-subdued-tab               'unicode-whitespace-subdued-tab               "Face variable to make font-lock happy.")
(defvar unicode-whitespace-subdued-space             'unicode-whitespace-subdued-space             "Face variable to make font-lock happy.")
(defvar unicode-whitespace-subdued-hspace            'unicode-whitespace-subdued-hspace            "Face variable to make font-lock happy.")
(defvar unicode-whitespace-subdued-newline           'unicode-whitespace-subdued-newline           "Face variable to make font-lock happy.")
(defvar unicode-whitespace-subdued-line              'unicode-whitespace-subdued-line              "Face variable to make font-lock happy.")

;;; customizable variables

;;;###autoload
(defgroup unicode-whitespace nil
  "Teach whitespace-mode about fancy characters."
  :version "0.2.3"
  :link '(emacs-commentary-link "unicode-whitespace")
  :prefix "unicode-whitespace-"
  :group 'i18n
  :group 'faces)

;;;###autoload
(defgroup unicode-whitespace-definitions nil
  "Define character groups recognized by unicode-whitespace"
  :group 'unicode-whitespace)

(defcustom unicode-whitespace-tab-names
  '("Character Tabulation With Justification"
    "Character Tabulation")             ; ordinary tab
  "Names of tab characters used by unicode-whitespace."
  :type '(repeat string)
  :group 'unicode-whitespace-definitions)

(defcustom unicode-whitespace-tab-set-names
  '("Character Tabulation Set"
    "Line Tabulation Set")
  "Names of tab-set characters used by unicode-whitespace."
  :type '(repeat string)
  :group 'unicode-whitespace-definitions)

(defcustom unicode-whitespace-soft-space-names
  '("Space"                             ; ordinary space
    "Em Quad"
    "Em Space"
    "En Quad"
    "En Space"
    "Figure Space"
    "Four-Per-Em Space"
    "Hair Space"
    "Ideographic Space"
    "Medium Mathematical Space"
    ;; typically is already visible, but unicode defines as space
    "Mongolian Vowel Separator"
    ;; typically is already visible, but unicode defines as space
    "Ogham Space Mark"
    "Punctuation Space"
    "Six-Per-Em Space"
    ;; already visible when whitespace-mode is off, might be bug, acquires cursor color
    "Tag Space"
    "Thin Space"
    "Three-Per-Em Space"
    ;; already visible when whitespace-mode is off, might be bug, acquires cursor color
    "Zero Width Space")
  "Names of soft space characters used by unicode-whitespace."
  :type '(repeat string)
  :group 'unicode-whitespace-definitions)

(defcustom unicode-whitespace-hard-space-names
  '("Narrow No-Break Space"
    ;; already visible when whitespace-mode is off, according to `nobreak-char-display'
    "No-Break Space"
    ;; zero-width, general punctuation block
    "Word Joiner"
    ;; already visible when whitespace-mode is off, might be bug, acquires cursor color
    "Zero Width No-Break Space")
  "Names of hard (non-breaking) space characters used by unicode-whitespace."
  :type '(repeat string)
  :group 'unicode-whitespace-definitions)

(defcustom unicode-whitespace-pseudo-space-names
  '("Combining Grapheme Joiner"     ; Combining Diacritical Marks block
    "Tifinagh Consonant Joiner"     ; Tifinagh block
    "Zero Width Joiner"             ; General Punctuation block
    "Zero Width Non-Joiner")        ; General Punctuation block
  "Names of pseudo-space characters used by unicode-whitespace.

Pseudo-spaces are treated as space for the purpose of
visualization by this library, but not officially defined as
space in the Unicode 6.1 specification."
  :type '(repeat string)
  :group 'unicode-whitespace-definitions)

(defcustom unicode-whitespace-standard-line-terminator-names
  '("Line Feed (LF)")
  "Names of line-terminator characters used by unicode-whitespace.

By default, only \"Line Feed (LF)\" is included here.  Alternative line
terminators are set in `unicode-whitespace-alternative-line-terminator-names'."
  :type '(repeat string)
  :group 'unicode-whitespace-definitions)

(defcustom unicode-whitespace-alternative-line-terminator-names
  '("Carriage Return (CR)"
    ;; According to the Unicode spec, formfeed should be a line
    ;; terminator on its own, but existing code (including
    ;; Emacs source) already has a tradition of writing "\f+\n".
    ;; So Form Feed (FF) is commented out.
    ;; "Form Feed (FF)"
    "Line Separator"
    "Line Tabulation"               ; ordinary \v
    "Next Line (NEL)"
    "Paragraph Separator")
  "Names of alternative line-terminator characters used by unicode-whitespace.

\"Line Feed (LF)\" should not be included in this list of
alternative terminators; LF is found in the list of standard line
terminators at `unicode-whitespace-standard-line-terminator-names'."
  :type '(repeat string)
  :group 'unicode-whitespace-definitions)

;;;###autoload
(defgroup unicode-whitespace-mappings nil
  "Mappings for characters to display instead of whitespace."
  :group 'unicode-whitespace)

;; alternatives to Middle Dot:
;;    Shouldered Open Box
;;    Symbol for Space
;;    Blank Symbol
;;    Open Box
;;    Eight Teardrop-Spoked Propeller Asterisk
;;    White Concave-Sided Diamond
;;    Square Lozenge
(defcustom unicode-whitespace-soft-space-mappings
  '(("Space"                                       ("Middle Dot"                  "."))
    ("Em Quad"                                     ("Circled Bullet" "Middle Dot" "."))
    ("Em Space"                                    ("Circled Bullet" "Middle Dot" "."))
    ("En Quad"                                     ("Circled Bullet" "Middle Dot" "."))
    ("En Space"                                    ("Circled Bullet" "Middle Dot" "."))
    ("Figure Space"                                ("Circled Bullet" "Middle Dot" "."))
    ("Four-Per-Em Space"                           ("Circled Bullet" "Middle Dot" "."))
    ("Hair Space"                                  ("Circled Bullet" "Middle Dot" "."))
    ("Ideographic Space"                           ("Circled Bullet" "Middle Dot" "."))
    ("Medium Mathematical Space"                   ("Circled Bullet" "Middle Dot" "."))
    ("Mongolian Vowel Separator"                   ("Circled Bullet" "Middle Dot" "."))
    ("Ogham Space Mark"                            ("Circled Bullet" "Middle Dot" "."))
    ("Punctuation Space"                           ("Circled Bullet" "Middle Dot" "."))
    ("Six-Per-Em Space"                            ("Circled Bullet" "Middle Dot" "."))
    ("Tag Space"                                   ("Circled Bullet" "Middle Dot" "."))
    ("Thin Space"                                  ("Circled Bullet" "Middle Dot" "."))
    ("Three-Per-Em Space"                          ("Circled Bullet" "Middle Dot" "."))
    ("Zero Width Space"                            ("Circled Bullet" "Middle Dot" ".")))
  "Display substitutions for soft space characters when `whitespace-mode' is on.

Each character name is tried in turn until a displayable character
is found.  Character names may be full UCS names or a string of
a single character."
  :type '(alist :key-type string :value-type (group (repeat :tag "Character Names" (string :tag ""))))
  :options unicode-whitespace-soft-space-names
  :group 'unicode-whitespace-mappings)

;; alternative character:
;;    Currency Sign
(defcustom unicode-whitespace-hard-space-mappings
  '(("Narrow No-Break Space"                     ("Black Diamond" "Middle Dot" "."))
    ("No-Break Space"                            ("Black Diamond" "Middle Dot" "."))
    ("Word Joiner"                               ("Black Diamond" "Middle Dot" "."))
    ("Zero Width No-Break Space"                 ("Black Diamond" "Middle Dot" ".")))
  "Display substitutions for hard space characters when `whitespace-mode' is on.

Each character name is tried in turn until a displayable character
is found.  Character names may be full UCS names or a string of
a single character."
  :type '(alist :key-type string :value-type (group (repeat :tag "Character Names" (string :tag ""))))
  :options unicode-whitespace-hard-space-names
  :group 'unicode-whitespace-mappings)

(defcustom unicode-whitespace-pseudo-space-mappings
  '(("Combining Grapheme Joiner"                   ("Black Medium Small Square" "Middle Dot" "."))
    ("Tifinagh Consonant Joiner"                   ("Black Medium Small Square" "Middle Dot" "."))
    ("Zero Width Joiner"                           ("Black Medium Small Square" "Middle Dot" "."))
    ("Zero Width Non-Joiner"                       ("Black Medium Small Square" "Middle Dot" ".")))
  "Display substitutions for pseudo-space characters when `whitespace-mode' is on.

Each character name is tried in turn until a displayable character
is found.  Character names may be full UCS names or a string of
a single character."
  :type '(alist :key-type string :value-type (group (repeat :tag "Character Names" (string :tag ""))))
  :options unicode-whitespace-pseudo-space-names
  :group 'unicode-whitespace-mappings)

(defcustom unicode-whitespace-standard-line-terminator-mappings
  '(("Line Feed (LF)"  ("Paragraph Sign" "$")))
  "Display substitutions for newline characters when `whitespace-mode' is on.

Each character name is tried in turn until a displayable character
is found.  Character names may be full UCS names or a string of
a single character."
  :type '(alist :key-type string :value-type (group (repeat :tag "Character Names" (string :tag ""))))
  :options unicode-whitespace-standard-line-terminator-names
  :group 'unicode-whitespace-mappings)

(defcustom unicode-whitespace-alternative-line-terminator-mappings
  '(("Carriage Return (CR)" ("Downwards Arrow With Corner Leftwards" "\r"))
    ("Next Line (NEL)"      ("Downwards Arrow"                       "$" ))
    ("Line Separator"       ("Downwards Arrow"                       "$" ))
    ("Paragraph Separator"  ("Downwards Arrow"                       "$" ))
    ("Line Tabulation"      ("Downwards Arrow"                       "$" )))
  "Display substitutions for alternative line-terminator characters in `whitespace-mode'.

Each character name is tried in turn until a displayable character
is found.  Character names may be full UCS names or a string of
a single character."
  :type '(alist :key-type string :value-type (group (repeat :tag "Character Names" (string :tag ""))))
  :options unicode-whitespace-alternative-line-terminator-names
  :group 'unicode-whitespace-mappings)

(defcustom unicode-whitespace-tab-mappings
  '(("Character Tabulation With Justification" ("Black Rightwards Arrowhead" ".")))
  "Display substitutions for tab characters in `whitespace-mode'.

Tab characters are already highlighted with a face.  It is best
not to activate mappings here for the standard Tab character,
because \(due to a limitation of Emacs\) indentation will
sometimes be broken.

Each character name is tried in turn until a displayable character
is found.  Character names may be full UCS names or a string of
a single character."
  :type '(alist :key-type string :value-type (group (repeat :tag "Character Names" (string :tag ""))))
  :options unicode-whitespace-tab-names
  :group 'unicode-whitespace-mappings)

(defcustom unicode-whitespace-tab-set-mappings
  '(("Character Tabulation Set"  ("Rightwards Arrow To Bar" "."))
    ("Line Tabulation Set"       ("Downwards Arrow To Bar"  ".")))
  "Display substitutions for tab-set characters in `whitespace-mode'.

Each character name is tried in turn until a displayable character
is found.  Character names may be full UCS names or a string of
a single character."
  :type '(alist :key-type string :value-type (group (repeat :tag "Character Names" (string :tag ""))))
  :options unicode-whitespace-tab-set-names
  :group 'unicode-whitespace-mappings)

(defcustom unicode-whitespace-form-feed-mappings
  '(("Form Feed (FF)"  ("Box Drawings Heavy Horizontal" "\f")))
  "Display substitutions for form-feed characters in `whitespace-mode'.

This mapping is treated specially: if the name matches the
string \"box drawing\", it is extended to a series of 20
characters.

Each character name is tried in turn until a displayable character
is found.  Character names may be full UCS names or a string of
a single character."
  :type '(alist :key-type string :value-type (group (repeat :tag "Character Names" (string :tag ""))))
  :options '("Form Feed (FF)")
  :group 'unicode-whitespace-mappings)

;;;###autoload
(defgroup unicode-whitespace-faces nil
  "Faces for `unicode-whitespace'."
  :group 'unicode-whitespace)

(defface unicode-whitespace-subdued-empty
  '((((background dark))  (:background "LightYellow"     :foreground "Black"))
    (((background light)) (:background "LightGoldenrod2" :foreground "Black")))
  "Unicode-whitespace face for empty lines at end and beginning of buffer."
  :group 'unicode-whitespace-faces)

(defface unicode-whitespace-subdued-trailing
  '((((background dark))  (:inherit unicode-whitespace-subdued-empty))
    (((background light)) (:inherit unicode-whitespace-subdued-empty)))
  "Unicode-whitespace face for trailing space."
  :group 'unicode-whitespace-faces)

(defface unicode-whitespace-subdued-space-after-tab
  '((((background dark))  (:inherit unicode-whitespace-subdued-empty))
    (((background light)) (:inherit unicode-whitespace-subdued-empty)))
  "Unicode-whitespace face for 8 or more spaces after a tab."
  :group 'unicode-whitespace-faces)

(defface unicode-whitespace-subdued-space-before-tab
  '((((background dark))  (:inherit unicode-whitespace-subdued-empty))
    (((background light)) (:inherit unicode-whitespace-subdued-empty)))
  "Unicode-whitespace face for space before tab at start of line."
  :group 'unicode-whitespace-faces)

(defface unicode-whitespace-subdued-tab
  '((((background dark))  (:foreground "DarkGray" :background "Gray20"))
    (((background light)) (:foreground "Black"    :background "Gray80")))
  "Unicode-whitespace face for tab characters."
  :group 'unicode-whitespace-faces)

(defface unicode-whitespace-subdued-indentation
  '((((background dark))  (:inherit unicode-whitespace-subdued-tab))
    (((background light)) (:inherit unicode-whitespace-subdued-tab)))
  "Unicode-whitespace face for indentation."
  :group 'unicode-whitespace-faces)

(defface unicode-whitespace-subdued-space
  '((((background dark))  (:foreground "Gray30"))
    (((background light)) (:foreground "Gray70")))
  "Unicode-whitespace face for soft space characters."
  :group 'unicode-whitespace-faces)

(defface unicode-whitespace-subdued-hspace
  '((((background dark))  (:foreground "Gray40"))
    (((background light)) (:foreground "Gray60")))
  "Unicode-whitespace face for hard space characters."
  :group 'unicode-whitespace-faces)

(defface unicode-whitespace-subdued-newline
  '((((background dark))  (:inherit unicode-whitespace-subdued-space))
    (((background light)) (:inherit unicode-whitespace-subdued-space)))
  "Unicode-whitespace face for newline characters."
  :group 'unicode-whitespace-faces)

(defface unicode-whitespace-subdued-line
  '((((background dark))  nil)
    (((background light)) nil))
  "Unicode-whitespace face for long lines."
  :group 'unicode-whitespace-faces)

;; end of faces customization group

(defcustom unicode-whitespace-newline-mark-modes '(
                                                   indented-text-mode
                                                   makefile-automake-mode
                                                   makefile-bsdmake-mode
                                                   makefile-gmake-mode
                                                   makefile-imake-mode
                                                   makefile-makepp-mode
                                                   makefile-mode
                                                   markdown-mode
                                                   org-mode
                                                   snippet-mode
                                                   text-mode
                                                   )
  "Major modes in which to enable newline visualization by default."
  :type '(repeat symbol)
  :group 'unicode-whitespace)

(defcustom unicode-whitespace-echo-level t
  "Which names to print when the 'echo style is in effect.

See `unicode-whitespace-toggle-echo' to activate."
  :type '(choice
          (const :tag "Non-ASCII whitespace"  non-ascii)
          (const :tag "All whitespace"        t))
  :group 'unicode-whitespace)

;;; macros

(defmacro unicode-whitespace-called-interactively-p (&optional kind)
  "A backward-compatible version of `called-interactively-p'.

Optional KIND is as documented at `called-interactively-p'
in GNU Emacs 24.1 or higher."
  (if (eq 0 (cdr (subr-arity (symbol-function 'called-interactively-p))))
      '(called-interactively-p)
    `(called-interactively-p ,kind)))

;;; utility functions

(defun unicode-whitespace-echo ()
  "If the point is on whitespace, identify that character in the echo area."
  (when (and unicode-whitespace-all-whitespace-regexp
             (not (eq (point) unicode-whitespace-last-point))
             (looking-at-p unicode-whitespace-all-whitespace-regexp)
             (or (not (eq unicode-whitespace-echo-level 'non-ascii))
                 (not (looking-at-p "[ \t\r\f\v]"))))
    (message "%s"
             (replace-regexp-in-string "\\`Character Tabulation" "Tab"
                                       (ucs-utils-pretty-name (char-after)))))
    (setq unicode-whitespace-last-point (point)))

(defun unicode-whitespace-hook-func ()
  "Enable newline marks by default only in certain cases.
Newline marked are enabled when `word-wrap' or `truncate-lines'
is set, or when the major mode of the buffer is listed in
`unicode-whitespace-newline-mark-modes'.

Newline marks can be toggled interactively with
`unicode-whitespace-toggle-newlines'.

Also (an unrelated bugfix) turn off `show-trailing-whitespace'
temporarily when `whitespace-mode' is on and restore the original
value for the buffer when turning off `whitespace-mode'.  This is
needed because show-trailing-whitespace overrides on the face for
trailing tabs."
  (cond
    ((not whitespace-mode)
     (set (make-local-variable 'whitespace-active-style) nil)
     (setq show-trailing-whitespace unicode-whitespace-saved-show-trailing))
    (t
     (setq unicode-whitespace-saved-show-trailing show-trailing-whitespace)
     (setq show-trailing-whitespace nil)
     (when (or word-wrap
               truncate-lines
               (memq major-mode unicode-whitespace-newline-mark-modes))
       ;; the way to set whitespace-style is a little fussy, because it is
       ;; not buffer-local, and the whitespace library looks at both variables
       (let ((whitespace-style whitespace-style))
         (add-to-list 'whitespace-style 'newline-mark)
         (set (make-local-variable 'whitespace-active-style) (copy-sequence whitespace-style))
         (whitespace-display-char-off)
         (whitespace-display-char-on))))))

(defun unicode-whitespace-recognize-extended-characters ()
  "Configure `whitespace-mode' to recognize Unicode whitespace characters."
  (let* ((tabs                  (ucs-utils-string unicode-whitespace-tab-names          'drop))
         (tab-sets              (ucs-utils-string unicode-whitespace-tab-set-names      'drop))
         (official-soft-spaces  (ucs-utils-string unicode-whitespace-soft-space-names   'drop))
         (hard-spaces           (ucs-utils-string unicode-whitespace-hard-space-names   'drop))
         (pseudo-spaces         (ucs-utils-string unicode-whitespace-pseudo-space-names 'drop))
         (alt-line-terms        (ucs-utils-string unicode-whitespace-alternative-line-terminator-names 'drop))
         (all-spaces            (concat hard-spaces official-soft-spaces pseudo-spaces tab-sets))
         (all-soft-spaces       (concat             official-soft-spaces pseudo-spaces tab-sets))
         (tabs-class                    (concat "[" tabs                 "]"))
         (tab-sets-class                (concat "[" tab-sets             "]"))
         (pseudo-spaces-class           (concat "[" pseudo-spaces        "]"))
         (official-soft-spaces-class    (concat "[" official-soft-spaces "]"))
         (hard-spaces-class             (concat "[" hard-spaces          "]"))
         (alt-line-terms-class          (concat "[" alt-line-terms       "]"))
         (all-spaces-class              (concat "[" all-spaces           "]"))
         (all-soft-spaces-class         (concat "[" all-soft-spaces      "]")))
    (setq whitespace-tab-regexp              (concat "\\(" tabs-class            "+\\)"))
    (setq whitespace-space-regexp            (concat "\\(" all-soft-spaces-class "+\\)"))
    (setq whitespace-hspace-regexp           (concat "\\(" hard-spaces-class     "+\\)"))
    (setq whitespace-space-before-tab-regexp (concat "\\(" all-spaces-class      "+\\)" whitespace-tab-regexp))
    (setq whitespace-trailing-regexp         (concat "\\([" tabs all-spaces alt-line-terms "]+\f*"
                                                        "[" tabs all-spaces alt-line-terms "\f" "]*\\)$"))
    (setq whitespace-space-after-tab-regexp
          (cons (concat tabs-class "+" "\\(" all-spaces-class "\\{%d,\\}\\)")
                (concat whitespace-tab-regexp all-spaces-class "+")))
    (setq whitespace-empty-at-bob-regexp    (concat "^\\(\\([" tabs all-spaces alt-line-terms "\f" "]*\n\\)+\\)"))
    (setq whitespace-empty-at-eob-regexp    (concat "^\\(["    tabs all-spaces alt-line-terms "\f" "\n" "]+\\)"))
    ;; todo Not certain about alt-line-terms here. Should we pretend they always start the line fresh?
    (setq whitespace-indentation-regexp
          (cons (concat "^" tabs-class "*" "\\([" all-spaces alt-line-terms "\f" "]\\{%d,\\}\\)" "[^" "\n" tabs "]")
                (concat "^[" all-spaces alt-line-terms "\f" "]*" "\\(" tabs-class "+\\)" "[^\n]")))
    (setq unicode-whitespace-all-whitespace-regexp (concat "[" tabs all-spaces alt-line-terms "\f" "\n" "]"))))

(defun unicode-whitespace-display-extended-characters ()
  "Configure `whitespace-mode' to display Unicode characters."
  (setq whitespace-display-mappings nil)
  (let ((case-fold-search t)
        (form-feed-names (mapcar 'car unicode-whitespace-form-feed-mappings)))
    (dolist (cell (append unicode-whitespace-soft-space-mappings
                          unicode-whitespace-hard-space-mappings
                          unicode-whitespace-pseudo-space-mappings
                          unicode-whitespace-tab-mappings
                          unicode-whitespace-tab-set-mappings
                          unicode-whitespace-form-feed-mappings))
      (let ((from-charname (car cell))
            (to-charnames (mapcar #'(lambda (x)
                                      (if (= 1 (length x))
                                          (aref x 0)
                                        x)) (cadr cell)))
            (mark-type 'space-mark)
            (display-len 1))
        (when (and (member from-charname form-feed-names)
                   (string-match-p "box drawing"
                                   (ucs-utils-pretty-name
                                    (ucs-utils-first-existing-char to-charnames 'cdp))))
          (setq display-len 20))
        (when (member from-charname unicode-whitespace-tab-names)
          (setq mark-type 'tab-mark))
        (push (list mark-type
                    (ucs-utils-char from-charname 'error)
                    (make-vector display-len (ucs-utils-first-existing-char to-charnames 'cdp)))
              whitespace-display-mappings)))

    (dolist (cell (append unicode-whitespace-standard-line-terminator-mappings
                          unicode-whitespace-alternative-line-terminator-mappings))
      (let ((from-charname (car cell))
            (to-charnames (mapcar #'(lambda (x)
                                  (if (= 1 (length x))
                                      (aref x 0)
                                    x)) (cadr cell)))
            (mark-type 'space-mark))
        (when (member from-charname unicode-whitespace-standard-line-terminator-names)
          ;; Calling alternative line-terminators "space-mark" is a hack
          ;; to make it possible to toggle display of standard newlines
          ;; without affecting these characters. They really should all
          ;; be called newline-mark.
          (setq mark-type 'newline-mark))
        (push (list mark-type
                    (ucs-utils-char from-charname 'error)
                    (if (eq (ucs-utils-char from-charname 'error) (ucs-utils-char "Carriage Return (CR)" 'error))
                        (vector (ucs-utils-first-existing-char to-charnames 'cdp))
                      ;; note below, a newline is placed in the vector and displayed in the substitution
                      (vector (ucs-utils-first-existing-char to-charnames 'cdp) ?\n)))
              whitespace-display-mappings)))))

(defun unicode-whitespace-configure-styles ()
  "Configure `whitespace-mode' styles."

  ;; add a new style - 'echo
  (add-to-list 'whitespace-style-value-list 'echo)

  ;; support the 'echo style
  (defadvice whitespace-post-command-hook (after whitespace-post-command-hook-echo activate)
    "Identify the whitespace character under the point in the echo area."
    (when (memq 'echo whitespace-active-style)
      (unicode-whitespace-echo)))

  ;; special handing for newline style and show-trailing-whitespace
  ;; workaround
  (add-hook 'whitespace-mode-hook 'unicode-whitespace-hook-func)

  ;; remove long-line indications (because it breaks normal font-lock)
  ;; remove newline-mark (re-enable in mode-dependent way)
  ;; add ::tab suffixes (seems like it should be ::space)
  (setq whitespace-style '(
                           empty
                           face
                           indentation               ; changes depending on the setting of indent-tabs-mode
                           newline
                           space-after-tab::tab      ; highlight spaces around tabs, rather than tabs themselves
                           space-before-tab::tab     ; highlight spaces around tabs, rather than tabs themselves
                           space-mark
                           spaces
                           tab-mark
                           tabs
                           trailing
                           )))

;;; interactive commands

;;;###autoload
(defun unicode-whitespace-subdued-faces (&optional arg)
  "Change the faces used by `whitespace-mode' to subdued coloring.

With negative prefix ARG, sets faces back to default values."
  (interactive "p")
  (if (< (prefix-numeric-value arg) 0)
      (progn
        (setq whitespace-empty             'whitespace-empty           )
        (setq whitespace-trailing          'whitespace-trailing        )
        (setq whitespace-indentation       'whitespace-indentation     )
        (setq whitespace-space-after-tab   'whitespace-space-after-tab )
        (setq whitespace-space-before-tab  'whitespace-space-before-tab)
        (setq whitespace-tab               'whitespace-tab             )
        (setq whitespace-space             'whitespace-space           )
        (setq whitespace-hspace            'whitespace-hspace          )
        (setq whitespace-newline           'whitespace-newline         )
        (setq whitespace-line              'whitespace-line            ))
    ;; else
    (setq whitespace-empty             'unicode-whitespace-subdued-empty           )
    (setq whitespace-trailing          'unicode-whitespace-subdued-trailing        )
    (setq whitespace-indentation       'unicode-whitespace-subdued-indentation     )
    (setq whitespace-space-after-tab   'unicode-whitespace-subdued-space-after-tab )
    (setq whitespace-space-before-tab  'unicode-whitespace-subdued-space-before-tab)
    (setq whitespace-tab               'unicode-whitespace-subdued-tab             )
    (setq whitespace-space             'unicode-whitespace-subdued-space           )
    (setq whitespace-hspace            'unicode-whitespace-subdued-hspace          )
    (setq whitespace-newline           'unicode-whitespace-subdued-newline         )
    (setq whitespace-line              'unicode-whitespace-subdued-line            )))

;;;###autoload
(defun unicode-whitespace-setup (&optional subdued-faces)
  "Configure `whitespace-mode' to be aware of extended characters.

This only needs to be run once per session.

When optional FACES is non-nil, change whitespace faces to
subdued coloring, on the theory that the new display glyphs
are sufficient to distinguish whitespace."
  (interactive "P")
  (unicode-whitespace-recognize-extended-characters)
  (unicode-whitespace-display-extended-characters)
  (unicode-whitespace-configure-styles)
  (when subdued-faces
    (unicode-whitespace-subdued-faces 1)))

;;;###autoload
(defun unicode-whitespace-toggle-echo ()
  "Toggle `whitespace-mode' echo-area feedback on/off."
  (interactive)
  (when (and (boundp 'whitespace-mode) whitespace-mode)
    (add-to-list 'whitespace-style-value-list 'echo)
    (let ((whitespace-style (whitespace-toggle-list t 'echo whitespace-active-style)))
      (whitespace-mode 0)
      (whitespace-mode 1)
      (when (unicode-whitespace-called-interactively-p 'interactive)
        (message "echo feedback %s" (if (memq 'echo whitespace-style) "enabled" "disabled"))))))

;;;###autoload
(defun unicode-whitespace-toggle-newlines ()
  "Toggle `whitespace-mode' newline visibility on/off."
  (interactive)
  (when (and (boundp 'whitespace-mode) whitespace-mode)
    (let ((whitespace-style (whitespace-toggle-list t 'newline-mark whitespace-active-style)))
      (whitespace-mode 0)
      (whitespace-mode 1)
      (when (unicode-whitespace-called-interactively-p 'interactive)
        (message "newline marks %s" (if (memq 'newline-mark whitespace-style) "enabled" "disabled"))))))

(provide 'unicode-whitespace)

;;
;; Emacs
;;
;; Local Variables:
;; indent-tabs-mode: nil
;; mangle-whitespace: t
;; require-final-newline: t
;; coding: utf-8
;; byte-compile-warnings: (not cl-functions redefine)
;; End:
;;
;; LocalWords: UnicodeWhitespace ARGS alist nonbreak glyphless
;; LocalWords: LightYellow nonbreaking LightGoldenrod Zenburn
;;

;;; unicode-whitespace.el ends here
