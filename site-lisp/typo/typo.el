;;; typo.el --- Minor mode for typographic editing

;; Copyright (C) 2012 Jorgen Schaefer

;; Version: 1.1
;; Author: Jorgen Schaefer <forcer@forcix.cx>
;; URL: https://github.com/jorgenschaefer/typoel
;; Created: 6 Feb 2012
;; Keywords: convenience, wp

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301  USA

;;; Commentary:

;; typo.el includes two modes, `typo-mode` and `typo-global-mode`.
;;
;; `typo-mode` is a buffer-specific minor mode that will change a number
;; of normal keys to make them insert typographically useful unicode
;; characters. Some of those keys can be used repeatedly to cycle through
;; variations. This includes in particular quotation marks and dashes.
;;
;; `typo-global-mode` introduces a global minor mode which adds the
;; `C-c 8` prefix to complement Emacs’ default `C-x 8` prefix map.
;;
;; See the documentation of `typo-mode` and `typo-global-mode` for
;; further details.
;;
;; ## Quotation Marks
;;
;; > “He said, ‘leave me alone,’ and closed the door.”
;;
;; All quotation marks in this sentence were added by hitting the " key
;; exactly once each. typo.el guessed the correct glyphs to use from
;; context. If it gets it wrong, you can just repeat hitting the " key
;; until you get the quotation mark you wanted.
;;
;; `M-x typo-change-language` lets you change which quotation marks to
;; use. This is also configurable, in case you want to add your own.
;;
;; ## Dashes and Dots
;;
;; The hyphen key will insert a default hyphen-minus glyph. On repeated
;; use, though, it will cycle through the en-dash, em-dash, and a number
;; of other dash-like glyphs available in Unicode. This means that typing
;; two dashes inserts an en-dash and typing three dashes inserts an
;; em-dash, as would be expected. The name of the currently inserted dash
;; is shown in the minibuffer.
;;
;; The full stop key will self-insert as usual. When three dots are
;; inserted in a row, though, they are replaced by a horizontal ellipsis
;; glyph.
;;
;; ## Other Keys
;;
;; Tick and backtick keys insert the appropriate quotation mark as well.
;; The less-than and greater-than signs cycle insert the default glyphs
;; on first use, but cycle through double and single guillemets on
;; repeated use.
;;
;; ## Prefix Map
;;
;; In addition to the above, typo-global-mode also provides a
;; globally-accessible key map under the `C-c 8` prefix (akin to Emacs’
;; default `C-x 8` prefix map) to insert various Unicode characters.
;;
;; In particular, `C-c 8 SPC` will insert a no-break space. Continued use
;; of SPC after this will cycle through half a dozen different space
;; types available in Unicode.
;;
;; Check the mode’s documentation for more details.

;;; Code:

;; For some reason, Emacs default has these as parentheses. This is
;; completely confusing when mixing this with normal parentheses,
;; and gets e.g. the following code wrong, even. Punctuation syntax
;; results in much more intuitive behavior.
(modify-syntax-entry ?» ".")
(modify-syntax-entry ?« ".")
;; Sorry for the intrusion.

(defgroup typo nil
  "*Typography mode for Emacs"
  :prefix "typo-"
  :group 'convenience)

(defcustom typo-quotation-marks
  '(("Czech"                 "„" "“" "‚" "‘")
    ("Czech (Guillemets)"    "»" "«" "›" "‹")
    ("English"               "“" "”" "‘" "’")
    ("German"                "„" "“" "‚" "‘")
    ("German (Guillemets)"   "»" "«" "›" "‹")
    ("French"                "«" "»" "‹" "›")
    ;; Finnish does not work THAT well because they use the same
    ;; quotation mark on both sides. En ymmärrä suomalaisen.
    ("Finnish"               "”" "”" "’" "’")
    ("Finnish (Guillemets)"  "»" "»" "›" "›")
    ("Russian"               "«" "»" "„" "“")
    ("Italian"               "«" "»" "“" "”"))
  "*Quotation marks per language."
  :type '(repeat (list (string :tag "Language")
                       (string :tag "Double Opening Quotation Mark")
                       (string :tag "Double Closing Quotation Mark")
                       (string :tag "Single Opening Quotation Mark")
                       (string :tag "Single Closing Quotation Mark")))
  :group 'typo)


(defcustom typo-language "English"
  "*The default language typo-mode should use."
  :type '(string :tag "Default Language")
  :group 'typo)
(make-variable-buffer-local 'typo-language)
(put 'typo-language 'safe-local-variable 'stringp)

(defcustom typo-disable-electricity-functions '(typo-in-xml-tag)
  "*A list of functions to call before an electric key binding is
used. If one of the functions returns non-nil, the key
self-inserts.

This can be used to disable the electric keys in e.g. XML tags."
  :type 'hook
  :options '(typo-in-xml-tag)
  :group 'typo)

(defvar typo-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "\"") 'typo-insert-quotation-mark)
    (define-key map (kbd "'") 'typo-cycle-right-single-quotation-mark)
    (define-key map (kbd "`") 'typo-cycle-left-single-quotation-mark)
    (define-key map (kbd "-") 'typo-cycle-dashes)
    (define-key map (kbd ".") 'typo-cycle-ellipsis)
    (define-key map (kbd "<") 'typo-cycle-left-angle-brackets)
    (define-key map (kbd ">") 'typo-cycle-right-angle-brackets)
    map)
  "The keymap for `typo-mode'.")

(defvar typo-global-mode-map
  (let ((gmap (make-sparse-keymap))
        (map (make-sparse-keymap)))
    (define-key gmap (kbd "C-c 8") map)
    (define-key map (kbd "\"") 'typo-insert-quotation-mark)
    (define-key map (kbd "'") 'typo-cycle-right-single-quotation-mark)
    (define-key map (kbd "`") 'typo-cycle-left-single-quotation-mark)
    (define-key map (kbd "--") 'typo-cycle-dashes)
    (define-key map (kbd ".") 'typo-cycle-ellipsis)
    (define-key map (kbd "<<") 'typo-cycle-left-angle-brackets)
    (define-key map (kbd ">>") 'typo-cycle-right-angle-brackets)
    (define-key map (kbd "*") 'typo-cycle-multiplication-signs)
    (define-key map (kbd "SPC") 'typo-cycle-spaces)
    (define-key map (kbd "?") 'typo-cycle-question-mark)
    (define-key map (kbd "!") 'typo-cycle-exclamation-mark)
    (define-key map (kbd "/=") "≠")
    (define-key map (kbd "//") "÷")
    (define-key map (kbd ">=") "≥")
    (define-key map (kbd "<=") "≤")
    (define-key map (kbd "=<") "⇐")
    (define-key map (kbd "=>") "⇒")
    (define-key map (kbd "<-") "←")
    (define-key map (kbd "-<") "←")
    (define-key map (kbd "->") "→")
    (define-key map (kbd "-^") "↑")
    (define-key map (kbd "=^") "⇑")
    (define-key map (kbd "-v") "↓")
    (define-key map (kbd "=v") "⇓")
    (define-key map (kbd "T")  "™")
    gmap)
  "The keymap for `typo-global-mode'.")

;;;###autoload
(define-minor-mode typo-mode
  "Minor mode for typographic editing.

This mode changes some default keybindings to enter typographic
glyphs. In particular, this changes how quotation marks, the
dash, the dot, and the angle brackets work.

Most keys will cycle through various options when used
repeatedly.

\\{typo-mode-map}"
  :group 'typo
  :lighter " Typo"
  :keymap typo-mode-map)

;;;###autoload
(define-minor-mode typo-global-mode
  "Minor mode for typographic editing.

This mode provides a prefix map under C-c 8 which complements the
default C-x 8 prefix map.

\\{typo-global-mode-map}"
  :group 'typo
  :global t
  :keymap typo-global-mode-map)

(defun typo-change-language (language)
  "Change the current language used for quotation marks."
  (interactive (list (completing-read
                      "Quotation marks: "
                      typo-quotation-marks
                      )))
  (when (not (assoc-string language typo-quotation-marks))
    (error "Unknown language %s (see `typo-quotation-marks')" language))
  (setq typo-language language))

(defun typo-open-double-quotation-mark ()
  "Return the opening double quotation marks for the current language."
  (nth 1 (assoc-string typo-language typo-quotation-marks)))

(defun typo-close-double-quotation-mark ()
  "Return the closing double quotation marks for the current language."
  (nth 2 (assoc-string typo-language typo-quotation-marks)))

(defun typo-open-single-quotation-mark ()
  "Return the opening single quotation marks for the current language."
  (nth 3 (assoc-string typo-language typo-quotation-marks)))

(defun typo-close-single-quotation-mark ()
  "Return the closing single quotation marks for the current language."
  (nth 4 (assoc-string typo-language typo-quotation-marks)))

(defun typo-in-xml-tag ()
  "Return non-nil if point is inside an XML tag."
  (save-excursion
    (and (re-search-backward "[<>]"
                             ;; If you have an XML tag that spans more
                             ;; than 25 lines, you should be shot.
                             (max (point-min)
                                  (- (point)
                                     (* 80 25)))
                             t)
         ;; < without a word char is a math formula
         (looking-at "<\\w"))))

(defun typo-electricity-disabled-p ()
  "Return non-nil if electricity is disabled at point.

See `typo-disable-electricity-functions'."
  ;; Only if this happened from a non-prefix variable
  (and (= (length (this-single-command-keys)) 1)
       (run-hook-with-args-until-success 'typo-disable-electricity-functions)))

(defun typo-quotation-needs-closing (open close)
  "Return non-nil if the last occurrence of either OPEN and CLOSE
in the current buffer is OPEN, i.e. if this pair still needs
closing.

This does not support nested, equal quotation marks."
  (save-excursion
    (if (re-search-backward (regexp-opt (list open close))
                            nil t)
        (equal open (match-string 0))
      nil)))

(defun typo-insert-quotation-mark (arg)
  "Insert quotation marks.

This command tries to be intelligent. Opening quotation marks are
closed. If you repeat the command after a quotation mark, that
mark is cycled through various variants.

After a closing double quotation mark, the next variant is an
opening single quotation mark. So when this command is issued
inside a quotation, it will first close the quotation. On the
second time, it will open an inner quotation.

After an opening double quotation mark, the next variant is the
typewriter quotation mark, making it possible in the usual case
to simple issue this command twice to get a typewriter quotation
mark (use C-q \" or C-o \" to force inserting one).

If used with a numeric prefix argument, only typewriter quotation
marks will be inserted."
  (interactive "P")
  (if (or (typo-electricity-disabled-p) arg)
      (call-interactively 'self-insert-command)
    (let* ((double-open (typo-open-double-quotation-mark))
           (double-close (typo-close-double-quotation-mark))
          (double-needs-closing (typo-quotation-needs-closing
                                 double-open double-close))

          (single-open (typo-open-single-quotation-mark))
          (single-close (typo-close-single-quotation-mark))
          (single-needs-closing (typo-quotation-needs-closing
                                 single-open single-close))

          (after-any-opening (looking-back (regexp-opt (list double-open
                                                             single-open)))))
     (cond
      ;; Inside a single quotation, if we're not directly at the
      ;; opening one, we close it.
      ((and single-needs-closing
            (not after-any-opening))
       (insert single-close))
      ;; Inside a double quotation, if we're not directly at the
      ;; opening one ...
      ((and double-needs-closing
            (not after-any-opening))
       ;; ... if we are after a space, we open an inner quotation.
       ;;
       ;; (This misses the situation where we start a quotation with an
       ;; inner quotation, but that's indistinguishable from cycling
       ;; through keys, and the latter is more common.)
       (if (looking-back "\\s-")
           (insert single-open)
         ;; Otherwise, close the double one
         (insert double-close)))
      ;; Nothing is open, or we are directly at an opening quote. If
      ;; this is a repetition of a this command, start cycling.
      ((eq this-command last-command)
       (delete-char -1)
       (typo-insert-cycle (list "\""
                                double-open double-close
                                single-open single-close)))
      ;; Otherwise, just open a double quotation mark.
      ;;
      ;; This can actually happen if we open a quotation, then move
      ;; point, then go back to directly after the quotation, and then
      ;; call this again. Opening another double quotation there is
      ;; weird, but I'm not sure what else to do then, either.
      (t
       (insert double-open))))))

(defun typo-cycle-ellipsis (arg)
  "Add periods. The third period will add an ellipsis.

If used with a numeric prefix argument N, N periods will be inserted."
  (interactive "P")
  (if (or (typo-electricity-disabled-p) arg)
      (call-interactively 'self-insert-command)
    (if (looking-back "\\.\\.")
        (replace-match "…")
      (call-interactively 'self-insert-command))))

(defmacro define-typo-cycle (name docstring cycle)
  "Define a typo command that cycles through various options.

If used with a numeric prefix argument N, N standard characters will be
inserted instead of cycling.

NAME is the name of the command to define.
DOCSTRING is the docstring for that command.

CYCLE is a list of strings to cycle through."
  (declare (indent 1) (doc-string 2))
  `(defun ,name (arg)
     ,docstring
     (interactive "P")
     (if (or (typo-electricity-disabled-p) arg)
         (call-interactively 'self-insert-command)
       (typo-insert-cycle ',cycle))))

;; This event cycling loop is from `kmacro-call-macro'
(defun typo-insert-cycle (cycle)
  "Insert the strings in CYCLE"
  (let ((i 0)
        (repeat-key last-input-event)
        repeat-key-str)
    (insert (nth i cycle))
    (setq repeat-key-str (format-kbd-macro (vector repeat-key) nil))
    (while repeat-key
      (message "(Inserted %s; type %s for other options)"
               (typo-char-name (nth i cycle))
               repeat-key-str)
      (if (equal repeat-key (read-event))
          (progn
            (clear-this-command-keys t)
            (delete-char (- (length (nth i cycle))))
            (setq i (% (+ i 1)
                       (length cycle)))
            (insert (nth i cycle))
            (setq last-input-event nil))
        (setq repeat-key nil)))
    (when last-input-event
      (clear-this-command-keys t)
      (setq unread-command-events (list last-input-event)))))

(defun typo-char-name (string)
  "Return the Unicode name of the first char in STRING."
  (let ((char-code (elt string 0))
        name)
    (setq name (get-char-code-property char-code 'name))
    (when (or (not name)
              (= ?< (elt name 0)))
      (setq name (get-char-code-property char-code 'old-name)))
    name))

(define-typo-cycle typo-cycle-right-single-quotation-mark
  "Cycle through the right quotation mark and the typewriter apostrophe.

If used with a numeric prefix argument N, N typewriter apostrophes
will be inserted."
  ("’" "'"))

(define-typo-cycle typo-cycle-left-single-quotation-mark
  "Cycle through the left single quotation mark and the backtick.

If used with a numeric prefix argument N, N backticks will be inserted."
  ("‘" "`"))

(define-typo-cycle typo-cycle-dashes
  "Cycle through various dashes."
  ("-" ; HYPHEN-MINUS
   "–" ; EN DASH
   "—" ; EM DASH
   "−" ; MINUS SIGN
   "‐" ; HYPHEN
   "‑" ; NON-BREAKING HYPHEN
  ))

(define-typo-cycle typo-cycle-left-angle-brackets
  "Cycle through the less-than sign and guillemet quotation marks.

If used with a numeric prefix argument N, N less-than signs will be inserted."
  ("<" "«" "‹"))

(define-typo-cycle typo-cycle-right-angle-brackets
  "Cycle through the greater-than sign and guillemet quotation marks.

If used with a numeric prefix argument N, N greater-than signs will be inserted."
  (">" "»" "›"))

(define-typo-cycle typo-cycle-multiplication-signs
  "Cycle through the asterisk and various multiplication signs"
  ("×" "·"))

(define-typo-cycle typo-cycle-spaces
  "Cycle through various spaces"
  (" " ; NO-BREAK SPACE
   " " ; THIN SPACE
   "‌" ; ZERO WIDTH NON-JOINER
   "‍" ; ZERO WIDTH JOINER
   " " ; MEDIUM MATHEMATICAL SPACE
   " " ; HAIR SPACE
   ;; " " ; EM SPACE
   ;; " " ; EN SPACE
   " " ; SPACE
  ))

(define-typo-cycle typo-cycle-question-mark
  "Cycle through various interrogatory marks."
  ("?" "¿" "‽" "⸘" "⸮"))

(define-typo-cycle typo-cycle-exclamation-mark
  "Cycle through various exclamatory marks."
  ("!" "¡" "‽" "⸘"))

(provide 'typo)
;;; typo.el ends here
