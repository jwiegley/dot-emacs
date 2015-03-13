;;; muse-colors.el --- coloring and highlighting used by Muse

;; Copyright (C) 2004, 2005, 2006, 2007, 2008, 2009, 2010
;;   Free Software Foundation, Inc.

;; Author: John Wiegley (johnw AT gnu DOT org)
;; Keywords: hypermedia
;; Date: Thu 11-Mar-2004

;; This file is part of Emacs Muse.  It is not part of GNU Emacs.

;; Emacs Muse is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; Emacs Muse is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Emacs Muse; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;;; Contributors:

;; Lan Yufeng (nlany DOT web AT gmail DOT com) found an error where
;; headings were being given the wrong face, contributing a patch to
;; fix this.

;; Sergey Vlasov (vsu AT altlinux DOT ru) fixed an issue with coloring
;; links that are in consecutive lines.

;; Jim Ottaway ported the <lisp> tag from emacs-wiki.

;; Per B. Sederberg (per AT med DOT upenn DOT edu) contributed the
;; viewing of inline images.

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Emacs Muse Highlighting
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-mode)
(require 'muse-regexps)
(require 'font-lock)

(defgroup muse-colors nil
  "Options controlling the behavior of Emacs Muse highlighting.
See `muse-colors-buffer' for more information."
  :group 'muse-mode)

(defcustom muse-colors-autogen-headings t
  "Specify whether the heading faces should be auto-generated.
The default is to scale them.

Choosing 'outline will copy the colors from the outline-mode
headings.

If you want to customize each of the headings individually, set
this to nil."
  :type '(choice (const :tag "Default (scaled) headings" t)
                 (const :tag "Use outline-mode headings" outline)
                 (const :tag "Don't touch the headings" nil))
  :group 'muse-colors)

(defcustom muse-colors-evaluate-lisp-tags t
  "Specify whether to evaluate the contents of <lisp> tags at
display time.  If nil, don't evaluate them.  If non-nil, evaluate
them.

The actual contents of the buffer are not changed, only the
displayed text."
  :type 'boolean
  :group 'muse-colors)

(defcustom muse-colors-inline-images t
  "Specify whether to inline images inside the Emacs buffer.  If
nil, don't inline them.  If non-nil, an image link will be
replaced by the image.

The actual contents of the buffer are not changed, only whether
an image is displayed."
  :type 'boolean
  :group 'muse-colors)

(defcustom muse-colors-inline-image-method 'default-directory
  "Determine how to locate inline images.
Setting this to 'default-directory uses the current directory of
the current Muse buffer.

Setting this to a function calls that function with the filename
of the image to be inlined.  The value that is returned will be
used as the filename of the image."
  :type '(choice (const :tag "Current directory" default-directory)
                 (const :tag "Publishing directory"
                        muse-colors-use-publishing-directory)
                 (function :tag "Custom function"))
  :group 'muse-colors)

(defvar muse-colors-region-end nil
  "Indicate the end of the region that is currently being font-locked.")
(make-variable-buffer-local 'muse-colors-region-end)

;;;###autoload
(defun muse-colors-toggle-inline-images ()
  "Toggle display of inlined images on/off."
  (interactive)
  ;; toggle the custom setting
  (if (not muse-colors-inline-images)
      (setq muse-colors-inline-images t)
    (setq muse-colors-inline-images nil))
  ;; reprocess the buffer
  (muse-colors-buffer)
  ;; display informative message
  (if muse-colors-inline-images
      (message "Images are now displayed inline")
    (message "Images are now displayed as links")))

(defvar muse-colors-outline-faces-list
  (if (facep 'outline-1)
      '(outline-1 outline-2 outline-3 outline-4 outline-5)
    ;; these are equivalent in coloring to the outline faces
    '(font-lock-function-name-face
      font-lock-variable-name-face
      font-lock-keyword-face
      font-lock-builtin-face
      font-lock-comment-face))
  "Outline faces to use when assigning Muse header faces.")

(defun muse-make-faces-default (&optional later)
  "Generate the default face definitions for headers."
  (dolist (num '(1 2 3 4 5))
    (let ((newsym (intern (concat "muse-header-" (int-to-string num))))
          (docstring (concat
                      "Muse header face.  See "
                      "`muse-colors-autogen-headings' before changing it.")))
      ;; put in the proper group and give documentation
      (if later
          (unless (featurep 'xemacs)
            (muse-copy-face 'variable-pitch newsym)
            (set-face-attribute newsym nil :height (1+ (* 0.1 (- 5 num)))
                                :weight 'bold))
        (if (featurep 'xemacs)
            (eval `(defface ,newsym
                     '((t (:size
                           ,(nth (1- num)
                                 '("24pt" "18pt" "14pt" "12pt" "11pt"))
                           :bold t)))
                     ,docstring
                     :group 'muse-colors))
          (eval `(defface ,newsym
                   '((t (:height ,(1+ (* 0.1 (- 5 num)))
                                 :inherit variable-pitch
                                 :weight bold)))
                   ,docstring
                   :group 'muse-colors)))))))

(progn (muse-make-faces-default))

(defun muse-make-faces (&optional frame)
  "Generate face definitions for headers based the user's preferences."
  (cond
   ((not muse-colors-autogen-headings)
    nil)
   ((eq muse-colors-autogen-headings t)
    (muse-make-faces-default t))
   (t
    (dolist (num '(1 2 3 4 5))
      (let ((newsym (intern (concat "muse-header-" (int-to-string num)))))
        ;; copy the desired face definition
        (muse-copy-face (nth (1- num) muse-colors-outline-faces-list)
                        newsym))))))

;; after displaying the Emacs splash screen, the faces are wiped out,
;; so recover from that
(add-hook 'window-setup-hook #'muse-make-faces)
;; ditto for when a new frame is created
(when (boundp 'after-make-frame-functions)
  (add-hook 'after-make-frame-functions #'muse-make-faces))

(defface muse-link
  '((((class color) (background light))
     (:foreground "blue" :underline "blue" :bold t))
    (((class color) (background dark))
     (:foreground "cyan" :underline "cyan" :bold t))
    (t (:bold t)))
  "Face for Muse cross-references."
  :group 'muse-colors)

(defface muse-bad-link
  '((((class color) (background light))
     (:foreground "red" :underline "red" :bold t))
    (((class color) (background dark))
     (:foreground "coral" :underline "coral" :bold t))
    (t (:bold t)))
  "Face for bad Muse cross-references."
  :group 'muse-colors)

(defface muse-verbatim
  '((((class color) (background light))
     (:foreground "slate gray"))
    (((class color) (background dark))
     (:foreground "gray")))
  "Face for verbatim text."
  :group 'muse-colors)

(defface muse-emphasis-1
  '((t (:italic t)))
  "Face for italic emphasized text."
  :group 'muse-colors)

(defface muse-emphasis-2
  '((t (:bold t)))
  "Face for bold emphasized text."
  :group 'muse-colors)

(defface muse-emphasis-3
  '((t (:bold t :italic t)))
  "Face for bold italic emphasized text."
  :group 'muse-colors)

(muse-copy-face 'italic 'muse-emphasis-1)
(muse-copy-face 'bold 'muse-emphasis-2)
(muse-copy-face 'bold-italic 'muse-emphasis-3)

(defcustom muse-colors-buffer-hook nil
  "A hook run after a region is highlighted.
Each function receives three arguments: BEG END VERBOSE.
BEG and END mark the range being highlighted, and VERBOSE specifies
whether progress messages should be displayed to the user."
  :type 'hook
  :group 'muse-colors)

(defvar muse-colors-highlighting-registry nil
  "The rules for highlighting Muse and Muse-derived buffers.
This is automatically generated when using font-lock in Muse buffers.

This an alist of major-mode symbols to `muse-colors-rule' objects.")

(defun muse-colors-make-highlighting-struct ()
  (list nil nil nil))
(defconst muse-colors-highlighting.regexp 0
  "Regexp matching each car of the markup of the current rule.")
(defconst muse-colors-highlighting.vector 1
  "Vector of all characters that are part of the markup of the current rule.
This is composed of the 2nd element of each markup entry.")
(defconst muse-colors-highlighting.remaining 2
  "Expressions for highlighting a buffer which have no corresponding
entry in the vector.")

(defsubst muse-colors-highlighting-entry (mode)
  "Return the highlighting rules for MODE."
  (assq mode muse-colors-highlighting-registry))

(defun muse-colors-find-highlighting (mode)
  "Return the highlighting rules to be used for MODE.
If MODE does not have highlighting rules, check its parent modes."
  (let ((seen nil))
    (catch 'rules
      (while (and mode (not (memq mode seen)))
        (let ((entry (muse-colors-highlighting-entry mode)))
          (when entry (throw 'rules (cdr entry))))
        (setq seen (cons mode seen))
        (setq mode (get mode 'derived-mode-parent)))
      nil)))

(defun muse-colors-define-highlighting (mode markup)
  "Create or update the markup rules for MODE, using MARKUP.

See `muse-colors-markup' for an explanation of the format that MARKUP
should take."
  (unless (and (symbolp mode) mode (consp markup))
    (error "Invalid arguments"))
  (let* ((highlighting-entry (muse-colors-highlighting-entry mode))
         (struct (cdr highlighting-entry))
         (regexp nil)
         (vector nil)
         (remaining nil))
    ;; Initialize struct
    (if struct
        (setq vector (nth muse-colors-highlighting.vector struct))
      (setq struct (muse-colors-make-highlighting-struct)))
    ;; Initialize vector
    (if vector
        (let ((i 0))
          (while (< i 128)
            (aset vector i nil)
            (setq i (1+ i))))
      (setq vector (make-vector 128 nil)))
    ;; Determine vector, regexp, remaining
    (let ((regexps nil)
          (rules nil))
      (dolist (rule markup)
        (let ((value (cond ((symbolp (car rule))
                            (symbol-value (car rule)))
                           ((stringp (car rule))
                            (car rule))
                           (t nil))))
          (when value
            (setq rules (cons rule rules))
            (setq regexps (cons value regexps)))))
      (setq regexps (nreverse regexps))
      (setq regexp (concat "\\(" (mapconcat #'identity regexps "\\|") "\\)"))
      (dolist (rule rules)
        (if (eq (nth 1 rule) t)
            (setq remaining (cons (cons (nth 0 rule) (nth 2 rule))
                                  remaining))
          (aset vector (nth 1 rule)
                (cons (cons (nth 0 rule) (nth 2 rule))
                      (aref vector (nth 1 rule)))))))
    ;; Update the struct
    (setcar (nthcdr muse-colors-highlighting.regexp struct) regexp)
    (setcar (nthcdr muse-colors-highlighting.vector struct) vector)
    (setcar (nthcdr muse-colors-highlighting.remaining struct) remaining)
    ;; Update entry for mode in muse-colors-highlighting-registry
    (if highlighting-entry
        (setcdr highlighting-entry struct)
      (setq muse-colors-highlighting-registry
            (cons (cons mode struct)
                  muse-colors-highlighting-registry)))))

(defun muse-configure-highlighting (sym val)
  "Extract color markup information from VAL and set to SYM.
This is usually called with `muse-colors-markup' as both arguments."
  (muse-colors-define-highlighting 'muse-mode val)
  (set sym val))

(defun muse-colors-emphasized ()
  "Color emphasized text and headings."
  ;; Here we need to check four different points - the start and end
  ;; of the leading *s, and the start and end of the trailing *s.  We
  ;; allow the outsides to be surrounded by whitespace or punctuation,
  ;; but no word characters, and the insides must not be surrounded by
  ;; whitespace or punctuation.  Thus the following are valid:
  ;;
  ;; " *foo bar* "
  ;; "**foo**,"
  ;; and the following is invalid:
  ;; "** testing **"
  (let* ((beg (match-beginning 0))
         (e1 (match-end 0))
         (leader (- e1 beg))
         b2 e2 multiline)
    (unless (or (eq (get-text-property beg 'invisible) 'muse)
                (get-text-property beg 'muse-comment)
                (get-text-property beg 'muse-directive))
      ;; check if it's a header
      (if (eq (char-after e1) ?\ )
          (when (or (= beg (point-min))
                    (eq (char-before beg) ?\n))
            (add-text-properties
             (muse-line-beginning-position) (muse-line-end-position)
             (list 'face (intern (concat "muse-header-"
                                         (int-to-string leader))))))
        ;; beginning of line or space or symbol
        (when (or (= beg (point-min))
                  (eq (char-syntax (char-before beg)) ?\ )
                  (memq (char-before beg)
                        '(?\- ?\[ ?\< ?\( ?\' ?\` ?\" ?\n)))
          (save-excursion
            (skip-chars-forward "^*<>\n" muse-colors-region-end)
            (when (eq (char-after) ?\n)
              (setq multiline t)
              (skip-chars-forward "^*<>" muse-colors-region-end))
            (setq b2 (point))
            (skip-chars-forward "*" muse-colors-region-end)
            (setq e2 (point))
            ;; Abort if space exists just before end
            ;; or bad leader
            ;; or no '*' at end
            ;; or word constituent follows
            (unless (or (> leader 5)
                        (not (eq leader (- e2 b2)))
                        (eq (char-syntax (char-before b2)) ?\ )
                        (not (eq (char-after b2) ?*))
                        (and (not (eobp))
                             (eq (char-syntax (char-after (1+ b2))) ?w)))
              (add-text-properties beg e1 '(invisible muse))
              (add-text-properties
               e1 b2 (list 'face (cond ((= leader 1) 'muse-emphasis-1)
                                       ((= leader 2) 'muse-emphasis-2)
                                       ((= leader 3) 'muse-emphasis-3))))
              (add-text-properties b2 e2 '(invisible muse))
              (when multiline
                (add-text-properties
                 beg e2 '(font-lock-multiline t))))))))))

(defun muse-colors-underlined ()
  "Color underlined text."
  (let ((start (match-beginning 0))
        multiline)
    (unless (or (eq (get-text-property start 'invisible) 'muse)
                (get-text-property start 'muse-comment)
                (get-text-property start 'muse-directive))
      ;; beginning of line or space or symbol
      (when (or (= start (point-min))
                (eq (char-syntax (char-before start)) ?\ )
                (memq (char-before start)
                      '(?\- ?\[ ?\< ?\( ?\' ?\` ?\" ?\n)))
        (save-excursion
          (skip-chars-forward "^_<>\n" muse-colors-region-end)
          (when (eq (char-after) ?\n)
            (setq multiline t)
            (skip-chars-forward "^_<>" muse-colors-region-end))
          ;; Abort if space exists just before end
          ;; or no '_' at end
          ;; or word constituent follows
          (unless (or (eq (char-syntax (char-before (point))) ?\ )
                      (not (eq (char-after (point)) ?_))
                      (and (not (eobp))
                           (eq (char-syntax (char-after (1+ (point)))) ?w)))
            (add-text-properties start (1+ start) '(invisible muse))
            (add-text-properties (1+ start) (point) '(face underline))
            (add-text-properties (point)
                                 (min (1+ (point)) (point-max))
                                 '(invisible muse))
            (when multiline
              (add-text-properties
               start (min (1+ (point)) (point-max))
               '(font-lock-multiline t)))))))))

(defun muse-colors-verbatim ()
  "Render in teletype and suppress further parsing."
  (let ((start (match-beginning 0))
        multiline)
    (unless (or (eq (get-text-property start 'invisible) 'muse)
                (get-text-property start 'muse-comment)
                (get-text-property start 'muse-directive))
      ;; beginning of line or space or symbol
      (when (or (= start (point-min))
                (eq (char-syntax (char-before start)) ?\ )
                (memq (char-before start)
                      '(?\- ?\[ ?\< ?\( ?\' ?\` ?\" ?\n)))
        (let ((pos (point)))
          (skip-chars-forward "^=\n" muse-colors-region-end)
          (when (eq (char-after) ?\n)
            (setq multiline t)
            (skip-chars-forward "^=" muse-colors-region-end))
          ;; Abort if space exists just before end
          ;; or no '=' at end
          ;; or word constituent follows
          (unless (or (eq (char-syntax (char-before (point))) ?\ )
                      (not (eq (char-after (point)) ?=))
                      (and (not (eobp))
                           (eq (char-syntax (char-after (1+ (point)))) ?w)))
            (setq pos (min (1+ (point)) (point-max)))
            (add-text-properties start (1+ start) '(invisible muse))
            (add-text-properties (1+ start) (point) '(face muse-verbatim))
            (add-text-properties (point)
                                 (min (1+ (point)) (point-max))
                                 '(invisible muse))
            (when multiline
              (add-text-properties
               start (min (1+ (point)) (point-max))
               '(font-lock-multiline t))))
          (goto-char pos))))))

(defcustom muse-colors-markup
  `(;; make emphasized text appear emphasized
    ("\\*\\{1,5\\}" ?* muse-colors-emphasized)

    ;; make underlined text appear underlined
    (,(concat "_[^" muse-regexp-blank "_\n]")
     ?_ muse-colors-underlined)

    ("^#title " ?\# muse-colors-title)

    (muse-explicit-link-regexp ?\[ muse-colors-explicit-link)

    ;; render in teletype and suppress further parsing
    (,(concat "=[^" muse-regexp-blank "=\n]") ?= muse-colors-verbatim)

    ;; highlight any markup tags encountered
    (muse-tag-regexp ?\< muse-colors-custom-tags)

    ;; display comments
    (,(concat "^;[" muse-regexp-blank "]") ?\; muse-colors-comment)

    ;; this has to come later since it doesn't have a special
    ;; character in the second cell
    (muse-url-regexp t muse-colors-implicit-link)
    )
  "Expressions to highlight an Emacs Muse buffer.
These are arranged in a rather special fashion, so as to be as quick as
possible.

Each element of the list is itself a list, of the form:

  (LOCATE-REGEXP TEST-CHAR MATCH-FUNCTION)

LOCATE-REGEXP is a partial regexp, and should be the smallest possible
regexp to differentiate this rule from other rules.  It may also be a
symbol containing such a regexp.  The buffer region is scanned only
once, and LOCATE-REGEXP indicates where the scanner should stop to
look for highlighting possibilities.

TEST-CHAR is a char or t.  The character should match the beginning
text matched by LOCATE-REGEXP.  These chars are used to build a vector
for fast MATCH-FUNCTION calling.

MATCH-FUNCTION is the function called when a region has been
identified.  It is responsible for adding the appropriate text
properties to change the appearance of the buffer.

This markup is used to modify the appearance of the original text to
make it look more like the published HTML would look (like making some
markup text invisible, inlining images, etc).

font-lock is used to apply the markup rules, so that they can happen
on a deferred basis.  They are not always accurate, but you can use
\\[font-lock-fontifty-block] near the point of error to force
fontification in that area."
  :type '(repeat
          (list :tag "Highlight rule"
                (choice (regexp :tag "Locate regexp")
                        (symbol :tag "Regexp symbol"))
                (choice (character :tag "Confirm character")
                        (const :tag "Default rule" t))
                function))
  :set 'muse-configure-highlighting
  :group 'muse-colors)

;; XEmacs users don't have `font-lock-multiline'.
(unless (boundp 'font-lock-multiline)
  (defvar font-lock-multiline nil))

(defun muse-use-font-lock ()
  "Set up font-locking for Muse."
  (muse-add-to-invisibility-spec 'muse)
  (set (make-local-variable 'font-lock-multiline) 'undecided)
  (set (make-local-variable 'font-lock-defaults)
       `(nil t nil nil beginning-of-line
         (font-lock-fontify-region-function . muse-colors-region)
         (font-lock-unfontify-region-function
          . muse-unhighlight-region)))
  (set (make-local-variable 'font-lock-fontify-region-function)
       'muse-colors-region)
  (set (make-local-variable 'font-lock-unfontify-region-function)
       'muse-unhighlight-region)
  (muse-make-faces)
  (muse-colors-define-highlighting 'muse-mode muse-colors-markup)
  (font-lock-mode t))

(defun muse-colors-buffer ()
  "Re-highlight the entire Muse buffer."
  (interactive)
  (muse-colors-region (point-min) (point-max) t))

(defvar muse-colors-fontifying-p nil
  "Indicate whether Muse is fontifying the current buffer.")
(make-variable-buffer-local 'muse-colors-fontifying-p)

(defvar muse-colors-delayed-commands nil
  "Commands to be run immediately after highlighting a region.

This is meant to accommodate highlighting <lisp> in #title
directives after everything else.

It may be modified by Muse functions during highlighting, but not
the user.")
(make-variable-buffer-local 'muse-colors-delayed-commands)

(defun muse-colors-region (beg end &optional verbose)
  "Apply highlighting according to `muse-colors-markup'.
Note that this function should NOT change the buffer, nor should any
of the functions listed in `muse-colors-markup'."
  (let ((buffer-undo-list t)
        (inhibit-read-only t)
        (inhibit-point-motion-hooks t)
        (inhibit-modification-hooks t)
        (modified-p (buffer-modified-p))
        (muse-colors-fontifying-p t)
        (muse-colors-region-end (muse-line-end-position end))
        (muse-colors-delayed-commands nil)
        (highlighting (muse-colors-find-highlighting major-mode))
        regexp vector remaining
        deactivate-mark)
    (unless highlighting
      (error "No highlighting found for this mode"))
    (setq regexp (nth muse-colors-highlighting.regexp highlighting)
          vector (nth muse-colors-highlighting.vector highlighting)
          remaining (nth muse-colors-highlighting.remaining highlighting))
    (unwind-protect
        (save-excursion
          (save-restriction
            (widen)
            ;; check to see if we should expand the beg/end area for
            ;; proper multiline matches
            (when (and font-lock-multiline
                       (> beg (point-min))
                       (get-text-property (1- beg) 'font-lock-multiline))
              ;; We are just after or in a multiline match.
              (setq beg (or (previous-single-property-change
                             beg 'font-lock-multiline)
                            (point-min)))
              (goto-char beg)
              (setq beg (muse-line-beginning-position)))
            (when font-lock-multiline
              (setq end (or (text-property-any end (point-max)
                                               'font-lock-multiline nil)
                            (point-max))))
            (goto-char end)
            (setq end (muse-line-beginning-position 2))
            ;; Undo any fontification in the area.
            (font-lock-unfontify-region beg end)
            ;; And apply fontification based on `muse-colors-markup'
            (let ((len (float (- end beg)))
                  (case-fold-search nil)
                  markup-list)
              (goto-char beg)
              (while (and (< (point) end)
                          (re-search-forward regexp end t))
                (if verbose
                    (message "Highlighting buffer...%d%%"
                             (* (/ (float (- (point) beg)) len) 100)))
                (let ((ch (char-after (match-beginning 0))))
                  (when (< ch 128)
                    (setq markup-list (aref vector ch))))
                (unless markup-list
                  (setq markup-list remaining))
                (let ((prev (point)))
                  ;; backtrack and figure out which rule matched
                  (goto-char (match-beginning 0))
                  (catch 'done
                    (dolist (entry markup-list)
                      (let ((value (cond ((symbolp (car entry))
                                          (symbol-value (car entry)))
                                         ((stringp (car entry))
                                          (car entry))
                                         (t nil))))
                        (when (and (stringp value) (looking-at value))
                          (goto-char (match-end 0))
                          (when (cdr entry)
                            (funcall (cdr entry)))
                          (throw 'done t))))
                    ;; if no rule matched, which should never happen,
                    ;; return to previous position so that forward
                    ;; progress is ensured
                    (goto-char prev))))
              (dolist (command muse-colors-delayed-commands)
                (apply (car command) (cdr command)))
              (run-hook-with-args 'muse-colors-buffer-hook
                                  beg end verbose)
              (if verbose (message "Highlighting buffer...done")))))
      (set-buffer-modified-p modified-p))))

(defcustom muse-colors-tags
  '(("example"  t nil nil muse-colors-example-tag)
    ("code"     t nil nil muse-colors-example-tag)
    ("verbatim" t nil nil muse-colors-literal-tag)
    ("lisp"     t t   nil muse-colors-lisp-tag)
    ("literal"  t nil nil muse-colors-literal-tag))
  "A list of tag specifications for specially highlighting text.
XML-style tags are the best way to add custom highlighting to Muse.
This is easily accomplished by customizing this list of markup tags.

For each entry, the name of the tag is given, whether it expects
a closing tag and/or an optional set of attributes, whether it is
nestable, and a function that performs whatever action is desired
within the delimited region.

The function is called with three arguments, the beginning and
end of the region surrounded by the tags. If properties are
allowed, they are passed as a third argument in the form of an
alist. The `end' argument to the function is the last character
of the enclosed tag or region.

Functions should not modify the contents of the buffer."
  :type '(repeat (list (string :tag "Markup tag")
                       (boolean :tag "Expect closing tag" :value t)
                       (boolean :tag "Parse attributes" :value nil)
                       (boolean :tag "Nestable" :value nil)
                       function))
  :group 'muse-colors)

(defvar muse-colors-inhibit-tags-in-directives t
  "If non-nil, don't allow tags to be interpreted in directives.
This is used to delay highlighting of <lisp> tags in #title until later.")
(make-variable-buffer-local 'muse-colors-inhibit-tags-in-directives)

(defsubst muse-colors-tag-info (tagname &rest args)
  "Get tag info associated with TAGNAME, ignoring ARGS."
  (assoc tagname muse-colors-tags))

(defun muse-colors-custom-tags ()
  "Highlight `muse-colors-tags'."
  (let ((tag-info (muse-colors-tag-info (match-string 1))))
    (unless (or (not tag-info)
                (get-text-property (match-beginning 0) 'muse-comment)
                (and muse-colors-inhibit-tags-in-directives
                     (get-text-property (match-beginning 0) 'muse-directive)))
      (let ((closed-tag (match-string 3))
            (start (match-beginning 0))
            end attrs)
        (when (nth 2 tag-info)
          (let ((attrstr (match-string 2)))
            (while (and attrstr
                        (string-match (concat "\\([^"
                                              muse-regexp-blank
                                              "=\n]+\\)\\(=\""
                                              "\\([^\"]+\\)\"\\)?")
                                      attrstr))
              (let ((attr (cons (downcase
                                 (muse-match-string-no-properties 1 attrstr))
                                (muse-match-string-no-properties 3 attrstr))))
                (setq attrstr (replace-match "" t t attrstr))
                (if attrs
                    (nconc attrs (list attr))
                  (setq attrs (list attr)))))))
        (if (and (cadr tag-info) (not closed-tag))
            (if (muse-goto-tag-end (car tag-info) (nth 3 tag-info))
                (setq end (match-end 0))
              (setq tag-info nil)))
        (when tag-info
          (let ((args (list start end)))
            (if (nth 2 tag-info)
                (nconc args (list attrs)))
            (apply (nth 4 tag-info) args)))))))

(defun muse-unhighlight-region (begin end &optional verbose)
  "Remove all visual highlights in the buffer (except font-lock)."
  (let ((buffer-undo-list t)
        (inhibit-read-only t)
        (inhibit-point-motion-hooks t)
        (inhibit-modification-hooks t)
        (modified-p (buffer-modified-p))
        deactivate-mark)
    (unwind-protect
        (remove-text-properties
         begin end '(face nil font-lock-multiline nil end-glyph nil
                          invisible nil intangible nil display nil
                          mouse-face nil keymap nil help-echo nil
                          muse-link nil muse-directive nil muse-comment nil
                          muse-no-implicit-link nil muse-no-flyspell nil))
      (set-buffer-modified-p modified-p))))

(defun muse-colors-example-tag (beg end)
  "Strip properties and colorize with `muse-verbatim'."
  (muse-unhighlight-region beg end)
  (let ((multi (save-excursion
                 (goto-char beg)
                 (forward-line 1)
                 (> end (point)))))
    (add-text-properties beg end `(face muse-verbatim
                                   font-lock-multiline ,multi))))

(defun muse-colors-literal-tag (beg end)
  "Strip properties and mark as literal."
  (muse-unhighlight-region beg end)
  (let ((multi (save-excursion
                 (goto-char beg)
                 (forward-line 1)
                 (> end (point)))))
    (add-text-properties beg end `(font-lock-multiline ,multi))))

(defun muse-colors-lisp-tag (beg end attrs)
  "Color the region enclosed by a <lisp> tag."
  (if (not muse-colors-evaluate-lisp-tags)
      (muse-colors-literal-tag beg end)
    (muse-unhighlight-region beg end)
    (let (beg-lisp end-lisp)
      (save-match-data
        (goto-char beg)
        (setq beg-lisp (and (looking-at "<[^>]+>")
                            (match-end 0)))
        (goto-char end)
        (setq end-lisp (and (muse-looking-back "</[^>]+>")
                            (match-beginning 0))))
      (add-text-properties
       beg end
       (list 'font-lock-multiline t
             'display (muse-eval-lisp
                       (concat
                        "(progn "
                        (buffer-substring-no-properties beg-lisp end-lisp)
                        ")"))
             'intangible t)))))

(defvar muse-mode-local-map
  (let ((map (make-sparse-keymap)))
    (define-key map [return] 'muse-follow-name-at-point)
    (define-key map [(control ?m)] 'muse-follow-name-at-point)
    (define-key map [(shift return)] 'muse-follow-name-at-point-other-window)
    (if (featurep 'xemacs)
        (progn
          (define-key map [(button2)] 'muse-follow-name-at-mouse)
          (define-key map [(shift button2)]
            'muse-follow-name-at-mouse-other-window))
      (define-key map [(shift control ?m)]
        'muse-follow-name-at-point-other-window)
      (define-key map [mouse-2] 'muse-follow-name-at-mouse)
      (define-key map [(shift mouse-2)]
        'muse-follow-name-at-mouse-other-window)
      (unless (eq emacs-major-version 21)
        (set-keymap-parent map muse-mode-map)))
    map)
  "Local keymap used by Muse while on a link.")

(defvar muse-keymap-property
  (if (or (featurep 'xemacs)
          (>= emacs-major-version 21))
      'keymap
    'local-map)
  "The name of the keymap or local-map property.")

(defsubst muse-link-properties (help-str &optional face)
  "Determine text properties to use for a link."
  (append (if face
              (list 'face face 'mouse-face 'highlight 'muse-link t)
            (list 'invisible 'muse 'intangible t))
          (list 'help-echo help-str 'rear-nonsticky t
                muse-keymap-property muse-mode-local-map)))

(defun muse-link-face (link-name &optional explicit)
  "Return the type of LINK-NAME as a face symbol.
For EXPLICIT links, this is either a normal link or a bad-link
face.  For implicit links, it is either colored normally or
ignored."
  (save-match-data
    (let ((link (if explicit
                    (muse-handle-explicit-link link-name)
                  (muse-handle-implicit-link link-name))))
      (when link
        (cond ((string-match muse-url-regexp link)
               'muse-link)
              ((muse-file-remote-p link)
               'muse-link)
              ((string-match muse-file-regexp link)
               (when (string-match "/[^/]+#[^#./]+\\'" link)
                 ;; strip anchor from the end of a path
                 (setq link (substring link 0 (match-beginning 0))))
               (if (file-exists-p link)
                   'muse-link
                 'muse-bad-link))
              ((not (featurep 'muse-project))
               'muse-link)
              (t
               (if (string-match "#" link)
                   (setq link (substring link 0 (match-beginning 0))))
               (if (or (and (muse-project-of-file)
                            (muse-project-page-file
                             link muse-current-project t))
                       (file-exists-p link))
                   'muse-link
                 'muse-bad-link)))))))

(defun muse-colors-use-publishing-directory (link)
  "Make LINK relative to the directory where we will publish the
current file."
  (let ((style (car (muse-project-applicable-styles
                     link (cddr (muse-project)))))
        path)
    (when (and style
               (setq path (muse-style-element :path style)))
      (expand-file-name link path))))

(defun muse-colors-resolve-image-file (link)
  "Determine if we can create images and see if the link is an image
file."
  (save-match-data
    (and (or (fboundp 'create-image)
             (fboundp 'make-glyph))
         (not (string-match "\\`[uU][rR][lL]:" link))
         (string-match muse-image-regexp link))))

(defun muse-make-file-glyph (filename)
  "Given a file name, return a newly-created image glyph.
This is a hack for supporting inline images in XEmacs."
  (let ((case-fold-search nil))
    ;; Scan filename to determine image type
    (when (fboundp 'make-glyph)
      (save-match-data
        (cond ((string-match "jpe?g" filename)
               (make-glyph (vector 'jpeg :file filename) 'buffer))
              ((string-match "gif" filename)
               (make-glyph (vector 'gif :file filename) 'buffer))
              ((string-match "png" filename)
               (make-glyph (vector 'png :file filename) 'buffer)))))))

(defun muse-colors-insert-image (link beg end invis-props)
  "Create an image using create-image or make-glyph and insert it
in place of an image link defined by BEG and END."
  (setq link (expand-file-name link))
  (let ((image-file (cond
                     ((eq muse-colors-inline-image-method 'default-directory)
                      link)
                     ((functionp muse-colors-inline-image-method)
                      (funcall muse-colors-inline-image-method link))))
        glyph)
    (when (stringp image-file)
      (if (fboundp 'create-image)
          ;; use create-image and display property
          (let ((display-stuff (condition-case nil
                                   (create-image image-file)
                                 (error nil))))
            (when display-stuff
              (add-text-properties beg end (list 'display display-stuff))))
        ;; use make-glyph and invisible property
        (and (setq glyph (muse-make-file-glyph image-file))
             (progn
               (add-text-properties beg end invis-props)
               (add-text-properties beg end (list
                                             'end-glyph glyph
                                             'help-echo link))))))))

(defun muse-colors-explicit-link ()
  "Color explicit links."
  (when (and (eq ?\[ (char-after (match-beginning 0)))
             (not (get-text-property (match-beginning 0) 'muse-comment))
             (not (get-text-property (match-beginning 0) 'muse-directive)))
    ;; remove flyspell overlays
    (when (fboundp 'flyspell-unhighlight-at)
      (let ((cur (match-beginning 0)))
        (while (> (match-end 0) cur)
          (flyspell-unhighlight-at cur)
          (setq cur (1+ cur)))))
    (let* ((unesc-link (muse-get-link))
           (unesc-desc (muse-get-link-desc))
           (link (muse-link-unescape unesc-link))
           (desc (muse-link-unescape unesc-desc))
           (props (muse-link-properties desc (muse-link-face link t)))
           (invis-props (append props (muse-link-properties desc))))
      ;; see if we should try and inline an image
      (if (and muse-colors-inline-images
               (or (muse-colors-resolve-image-file link)
                   (and desc
                        (muse-colors-resolve-image-file desc)
                        (setq link desc))))
          ;; we found an image, so inline it
          (muse-colors-insert-image
           link
           (match-beginning 0) (match-end 0) invis-props)
        (if desc
            (progn
              ;; we put the normal face properties on the invisible
              ;; portion too, since emacs sometimes will position
              ;; the cursor on an intangible character
              (add-text-properties (match-beginning 0)
                                   (match-beginning 2) invis-props)
              (add-text-properties (match-beginning 2) (match-end 2) props)
              (add-text-properties (match-end 2) (match-end 0) invis-props)
              ;; in case specials were escaped, cause the unescaped
              ;; text to be displayed
              (unless (string= desc unesc-desc)
                (add-text-properties (match-beginning 2) (match-end 2)
                                     (list 'display desc))))
          (add-text-properties (match-beginning 0)
                               (match-beginning 1) invis-props)
          (add-text-properties (match-beginning 1) (match-end 0) props)
          (add-text-properties (match-end 1) (match-end 0) invis-props)
          (unless (string= link unesc-link)
            (add-text-properties (match-beginning 1) (match-end 1)
                                 (list 'display link))))
        (goto-char (match-end 0))
        (add-text-properties
         (match-beginning 0) (match-end 0)
         (muse-link-properties (muse-match-string-no-properties 0)
                               (muse-link-face link t)))))))

(defun muse-colors-implicit-link ()
  "Color implicit links."
  (unless (or (eq (get-text-property (match-beginning 0) 'invisible) 'muse)
              (get-text-property (match-beginning 0) 'muse-comment)
              (get-text-property (match-beginning 0) 'muse-directive)
              (get-text-property (match-beginning 0) 'muse-no-implicit-link)
              (eq (char-before (match-beginning 0)) ?\")
              (eq (char-after (match-end 0)) ?\"))
    ;; remove flyspell overlays
    (when (fboundp 'flyspell-unhighlight-at)
      (let ((cur (match-beginning 0)))
        (while (> (match-end 0) cur)
          (flyspell-unhighlight-at cur)
          (setq cur (1+ cur)))))
    ;; colorize link
    (let ((link (muse-match-string-no-properties 0))
          (face (muse-link-face (match-string 0))))
      (when face
        (add-text-properties (match-beginning 0) (match-end 0)
                             (muse-link-properties
                              (muse-match-string-no-properties 0) face))))))

(defun muse-colors-title ()
  "Color #title directives."
  (let ((beg (+ 7 (match-beginning 0))))
    (add-text-properties beg (muse-line-end-position) '(muse-directive t))
    ;; colorize <lisp> tags in #title after other <lisp> tags have had a
    ;; chance to run, so that we can have behavior that is consistent
    ;; with how the document is published
    (setq muse-colors-delayed-commands
          (cons (list 'muse-colors-title-lisp beg (muse-line-end-position))
                muse-colors-delayed-commands))))

(defun muse-colors-title-lisp (beg end)
  "Called after other highlighting is done for a region in order to handle
<lisp> tags that exist in #title directives."
  (save-restriction
    (narrow-to-region beg end)
    (goto-char (point-min))
    (let ((muse-colors-inhibit-tags-in-directives nil)
          (muse-colors-tags '(("lisp" t t nil muse-colors-lisp-tag))))
      (while (re-search-forward muse-tag-regexp nil t)
        (muse-colors-custom-tags))))
  (add-text-properties beg end '(face muse-header-1)))

(defun muse-colors-comment ()
  "Color comments."
  (add-text-properties (match-beginning 0) (muse-line-end-position)
                       (list 'face 'font-lock-comment-face
                             'muse-comment t)))


(provide 'muse-colors)

;;; muse-colors.el ends here
