;;; -*- Mode: Emacs-Lisp; outline-regexp: ";;;+ [^\n]\\|(" -*-
;;;;;; redshank.el --- Common Lisp Editing Extensions

;; Copyright (C) 2006, 2007  Michael Weber

;; Author: Michael Weber <michaelw@foldr.org>
;; Keywords: languages, lisp

;; Redshank, n.  A common Old World limicoline bird (Totanus
;;   calidris), having the legs and feet pale red. The spotted
;;   redshank (T. fuscus) is larger, and has orange-red legs.
;;   Called also redleg and _clee_.

;;;; Commentary
;;; Setup

;; Add this to your Emacs configuration:
;;
;;   (add-to-list 'load-path "/path/to/elisp/")
;;   (autoload 'redshank-mode "redshank"
;;     "Minor mode for editing and refactoring (Common) Lisp code."
;;     t)
;;   (add-hook '...-mode-hook (lambda () (redshank-mode +1)))
;;
;; Also, this mode can be enabled with M-x redshank-mode.
;; Customization of redshank can be accomplished with
;; M-x customize-group RET redshank RET, or with
;; `eval-after-load':
;;
;;   (eval-after-load 'redshank
;;     '(progn ...redefine keys, etc....))
;;
;; This code was tested with Paredit 20, and should run at least in
;; GNU Emacs 22 and later.

;;; To Do

;; * Unit tests; no really, there are just too many ways to mess up
;;   code and comments.

;;; Known Issues

;; `redshank-align-defclass-slots':
;; * Does not work if slot forms contain newlines
;; * Does not work well with #+ and #- reader conditionals
;; * Long slot options cause large columns (:documentation ...)

;;; Contact

;; Send questions, bug reports, comments and feature suggestions to
;; Michael Weber <michaelw+redshank@foldr.org>.  New versions can be
;; found at <http://www.foldr.org/~michaelw/lisp/redshank/>.

;;; Code:
(defconst redshank-version 0)

(require 'cl)
(require 'paredit)
(require 'skeleton)

;;;; Customizations
(defgroup redshank nil
  "Common Lisp Editing Extensions"
  :load 'redshank
  :group 'lisp)

(defface redshank-highlight-face
  '((t (:inherit highlight)))
    "Face used to highlight extracted binders."
  :group 'redshank)

(defcustom redshank-prefix-key "C-x C-r"
  "*Prefix key sequence for redshank-mode commands.
\\<redshank-mode-map>"
  :type  'string
  :group 'redshank)

(defcustom redshank-reformat-defclass-skeletons t
  "*Reformat DEFCLASS entries created with REDSHANK skeletons."
  :type  'boolean
  :group 'redshank)

(defcustom redshank-accessor-name-function
  'redshank-accessor-name/get
  "*Function which, given a slot-name, returns the accessor name."
  :type  '(radio
           (function-item redshank-accessor-name/get)
           (function-item redshank-accessor-name/of)
           (function :tag "Other"))
  :group 'redshank)

;;;; Minor Mode Definition
(defconst redshank-keys
  '(("A" . redshank-align-forms-as-columns)
    ("a" . redshank-align-defclass-slots)
    ("c" . redshank-condify-form)
    ("e" . redshank-eval-whenify-form)
    ("l" . redshank-letify-form-up)
    ("n" . redshank-rewrite-negated-predicate)
    ("p" . redshank-maybe-splice-progn)
    ("C" . redshank-defclass-skeleton)
    ("P" . redshank-defpackage-skeleton)
    ("S" . redshank-defclass-slot-skeleton))
  "Standard key bindings for the Redshank minor mode.")

(defvar redshank-mode-map
  (let ((map (make-sparse-keymap)))
    (dolist (spec redshank-keys map)
      (let* ((key-spec (concat redshank-prefix-key " " (car spec)))
             (key (read-kbd-macro key-spec)))
        (define-key map key (cdr spec)))))
  "Keymap for the Redshank minor mode.")

(define-minor-mode redshank-mode
  "Minor mode for editing and refactoring (Common) Lisp code."
  :lighter " Redshank"
  :keymap `(,(read-kbd-macro redshank-prefix-key) . redshank-mode-map))

(defun turn-on-redshank-mode ()
  "Turn on Redshank mode.  Please see function `redshank-mode'.

This function is designed to be added to hooks, for example:
  (add-hook 'lisp-mode-hook 'turn-on-redshank-mode)"
  (interactive)
  (redshank-mode +1))

;;;; Utility Functions
(defun redshank-accessor-name/get (slot-name)
  "GET-SLOT style accessor names."
  (concat "get-" slot-name))

(defun redshank-accessor-name/of (slot-name)
  "SLOT-OF style accessor names."
  (concat slot-name "-of"))

(defun redshank-accessor-name (slot-name)
  (if (or (null redshank-accessor-name-function)
          (functionp redshank-accessor-name-function))
      (funcall redshank-accessor-name-function slot-name)
    (redshank-accessor-name/get slot-name)))

(defun redshank--looking-at-or-inside (spec)
  (let ((form-regex (concat "(" spec "\\S_"))
        (here.point (point)))
    (unless (looking-at "(")
      (ignore-errors (backward-up-list)))
    (or (looking-at form-regex)
        (prog1 nil
          (goto-char here.point)))))

(defun redshank-maybe-splice-progn ()
  "Splice PROGN form at point into its surrounding form.
Nothing is done if point is not preceding a PROGN form."
  (interactive "*")
  (paredit-point-at-sexp-start)
  (when (redshank--looking-at-or-inside "progn")
    (paredit-forward-kill-word)
    (delete-region (prog1 (point) (paredit-skip-whitespace t))
                   (point))
    (paredit-splice-sexp-killing-backward)
    (paredit-point-at-sexp-start)))

(defun redshank-point-at-enclosing-let-form ()
  "Move point to enclosing LET/LET* form if existing.
Point is not moved across other binding forms \(e.g., DEFUN,
LABELS or FLET.)"
  (interactive)
  (let ((here.point (point)))
    (or (ignore-errors
          (block nil
            (backward-up-list)
            (while (not (looking-at "(let\\*?\\S_"))
              (when (looking-at "(\\(def\\s_*\\|labels\\|flet\\)\\S_")
                (return nil))
              (backward-up-list))
            (point)))
        (prog1 nil
          (goto-char here.point)))))

(defun redshank--symbol-namep (symbol)
  (and (stringp symbol)
       (not (string= symbol ""))))

(defun redshank--end-of-sexp-column ()
  "Move point to end of current form, neglecting trailing whitespace."
  (forward-sexp)
  (while (forward-comment +1))
  (skip-chars-backward "[:space:]"))

(defun redshank--sexp-column-widths ()
  "Return list of column widths for s-expression at point."
  (down-list)
  (loop do (while (forward-comment 1))
        until (or (looking-at ")") (eobp))
        collect (- (- (point)
                      (progn
                        (redshank--end-of-sexp-column)
                        (point))))
        finally (up-list)))

(defun redshank--max* (&rest args)
  (reduce #'max args :key (lambda (arg) (or arg 0))))

(defun redshank-align-sexp-columns (column-widths)
  "Align expressions in S-expression at point.
COLUMN-WIDTHS is expected to be a list."
  (down-list)
  (loop initially (while (forward-comment +1))
        for width in column-widths
        until (looking-at ")")
        do (let ((beg (point)))
             (redshank--end-of-sexp-column)
             (let ((used (- (point) beg)))
               (just-one-space (if (looking-at "[[:space:]]*)") 0
                                 (1+ (- width used))))))
        finally (up-list)))

;;; Highlighting
(defvar redshank-letify-overlay
  (let ((overlay (make-overlay 1 1)))
    (overlay-put overlay 'face 'redshank-highlight-face)
    overlay)
  "Overlay to highlight letified binders.")

(defun redshank-highlight-binder (beg end)
  (move-overlay redshank-letify-overlay beg end))

(defun redshank-unhighlight-binder ()
  (interactive)
  (delete-overlay redshank-letify-overlay))

;;;; Form Frobbing
(defun redshank-condify-form ()
  "Transform a Common Lisp IF form into an equivalent COND form."
  (interactive "*")
  (flet ((redshank--frob-cond-branch ()
            (paredit-wrap-sexp +2)
            (forward-sexp)                              
            (redshank-maybe-splice-progn)))
    (save-excursion
      (unless (redshank--looking-at-or-inside "if")
        (error "Cowardly refusing to mutilate other forms than IF"))
      (paredit-forward-kill-word)
      (insert "cond")
      (just-one-space)
      (redshank--frob-cond-branch)
      (up-list)
      (paredit-newline)
      (save-excursion (insert "t "))
      (redshank--frob-cond-branch))))

(defun redshank-letify-form (var)
  "Extract the form at point into a new LET binding.
The binding variable's name is requested in the mini-buffer."
  (interactive "*sVariable name: ")
  (when (redshank--symbol-namep var)
    (paredit-point-at-sexp-start)
    (paredit-wrap-sexp +1)              ; wrap with (LET ...)
    (insert "let ")
    (paredit-wrap-sexp +1)              ; wrap binders
    (let ((binder.start (point)))
      (paredit-wrap-sexp +1)
      (insert var " ")
      (up-list)
      (redshank-highlight-binder binder.start (point)))
    (up-list)                           ; point at LET body
    (paredit-newline)
    (save-excursion                     ; insert variable name
      (insert var))))

(defun redshank-letify-form-up (var &optional arg)
  "Extract the form at point into a (possibly enclosing) LET binding.
The binding variable's name is requested in the mini-buffer.
With prefix argument, or if no suitable binding can be found,
`redshank-letify-form' is executed instead."
  (interactive "*sVariable name: \nP")
  (let ((let.start (save-excursion
                     (redshank-point-at-enclosing-let-form))))
    (cond ((and (redshank--symbol-namep var)
                (not arg)
                let.start)
           (paredit-point-at-sexp-start)
           (let* ((form.start (prog1 (point) (forward-sexp)))
                  (form (delete-and-extract-region form.start (point))))
             (save-excursion
               (insert var)
               (goto-char let.start)
               (down-list)              ; move point from |(let ...
               (forward-sexp +2)        ; to behind last binder form
               (backward-down-list)   
               (paredit-newline)        ; insert new binder
               (let ((binder.start (point)))
                 (insert "(" var " " form ")")
                 (redshank-highlight-binder binder.start (point)))
               (backward-sexp)          ; ... and reindent it
               (indent-sexp))))
          (t (redshank-letify-form var)))))

(defun redshank-eval-whenify-form (&optional n)
  "Wraps top-level form at point with (EVAL-WHEN (...) ...).
With optional numeric argument, wrap N top-level forms."
  ;; A slightly modified version of `asf-eval-whenify' from
  ;; <http://boinkor.net/archives/2006/11/three_useful_emacs_hacks_for_l.html>
  (interactive "*p")
  (save-excursion
    (if (and (boundp 'slime-repl-input-start-mark)
             slime-repl-input-start-mark)
        (slime-repl-beginning-of-defun)
      (beginning-of-defun))
    (paredit-wrap-sexp n)
    (insert "eval-when (:compile-toplevel :load-toplevel :execute)\n")
    (backward-up-list)
    (indent-sexp)))

(defun redshank-rewrite-negated-predicate ()
  "Rewrite the negated predicate of a WHEN or UNLESS form at point."
  (interactive "*")
  (save-excursion
    (flet ((redshank--frob-form (new-head)
             (paredit-forward-kill-word)
             (insert new-head)
             (paredit-forward-kill-word)
             (paredit-splice-sexp-killing-backward)
             (just-one-space)))
      ;; Okay, I am cheating here...
      (cond ((redshank--looking-at-or-inside "when\\s-+(not")
             (redshank--frob-form "unless"))
            ((redshank--looking-at-or-inside "unless\\s-+(not")
             (redshank--frob-form "when"))
            (t 
             (error "Cowardly refusing to mutilate unknown form"))))))

(defun redshank-align-forms-as-columns (beg end)
  "Align S-expressions in region as columns.
Example:
  (define-symbol-macro MEM (mem-of *cpu*))
  (define-symbol-macro IP (ip-of *cpu*))
  (define-symbol-macro STACK (stack-of *cpu*))

is formatted as:

  (define-symbol-macro MEM   (mem-of *cpu*))
  (define-symbol-macro IP    (ip-of *cpu*))
  (define-symbol-macro STACK (stack-of *cpu*))" 
 (interactive "*r")
  (save-restriction
    (narrow-to-region beg end)
    (goto-char beg)
    (let* ((columns
            (loop do (while (forward-comment +1))
                  until (or (looking-at ")") (eobp))
                  collect (redshank--sexp-column-widths)))
           (max-column-widths
            (loop for cols = columns then (mapcar #'cdr cols)
                  while (some #'consp cols)
                  collect (apply #'redshank--max* (mapcar #'car cols)))))
      (goto-char beg)
      (loop do (while (forward-comment +1))
            until (or (looking-at ")") (eobp))
            do (redshank-align-sexp-columns max-column-widths)))))

(defun redshank-align-defclass-slots ()
  "Align slots of the Common Lisp DEFCLASS form at point.
Example (| denotes cursor position):
|(defclass identifier ()
   ((name :reader get-name :initarg :name)
    (location :reader get-location :initarg :location)
    (scope :accessor get-scope :initarg :scope)
    (definition :accessor get-definition :initform nil))
   (:default-initargs :scope *current-scope*))

is formatted to:

|(defclass identifier ()
   ((name       :reader   get-name       :initarg  :name)
    (location   :reader   get-location   :initarg  :location)
    (scope      :accessor get-scope      :initarg  :scope)
    (definition :accessor get-definition :initform nil))
   (:default-initargs :scope *current-scope*))"
  (interactive "*")
  (save-excursion
    (when (redshank--looking-at-or-inside "defclass")
      (down-list)
      (forward-sexp +3)                 ; move to slots definitions
      (let ((slots.end (save-excursion (forward-sexp) (point))))
        (redshank-align-forms-as-columns (progn (down-list) (point))
                                     slots.end)))))

;;;; Skeletons
(define-skeleton redshank-defpackage-skeleton
  "Inserts a Common Lisp DEFPACKAGE skeleton."
  (skeleton-read "Package: " (if v1
                                 (or (ignore-errors
                                       (file-name-sans-extension
                                        (file-name-nondirectory
                                         (buffer-file-name))))
                                     "TEMP")))
  (if (setq v1 (bobp)) ";;; -*- Mode:Lisp; Syntax:ANSI-Common-Lisp;")
  & (if buffer-file-coding-system
        (concat " Coding:"
                (symbol-name 
                 (coding-system-get buffer-file-coding-system 
                                    'mime-charset))))
  & " -*-"
  & \n
  & \n '(paredit-open-parenthesis) "defpackage #:" str
  \n '(paredit-open-parenthesis)
     ":nicknames" ("Nickname: " " #:" str)
   & '(paredit-close-parenthesis) & \n
   | '(progn
        (backward-up-list)
        (kill-sexp))
  '(paredit-open-parenthesis)
   ":use #:CL" ((slime-read-package-name "USEd package: ") " #:" str)
  '(paredit-close-parenthesis) 
  '(paredit-close-parenthesis)
  \n \n (if v1 "(in-package #:") & str & ")" & \n &
  \n
  _)

(define-skeleton redshank-defclass-skeleton
  "Inserts a Common Lisp DEFCLASS skeleton."
  "Class: "
  '(paredit-open-parenthesis)
  "defclass " str " "
  '(paredit-open-parenthesis)
   ((skeleton-read "Superclass: ") str " ") & -1
  '(paredit-close-parenthesis)
  \n '(paredit-open-parenthesis)
      ((skeleton-read "Slot: ")
       '(paredit-open-parenthesis)
        str " :accessor " (redshank-accessor-name str)
        " :initarg :" str
       '(paredit-close-parenthesis) \n) & '(join-line)
  '(paredit-close-parenthesis)
  ;; \n "(:default-initargs " - ")" ;; add to your liking...
  '(paredit-close-parenthesis) "\n" \n
  _)

(define-skeleton redshank-defclass-slot-skeleton
  "Inserts a Common Lisp DEFCLASS slot skeleton."
  "Slot: "
  ((skeleton-read "Slot: ")
   '(indent-according-to-mode)
   '(paredit-open-parenthesis)
    str " :accessor " (redshank-accessor-name str)
    " :initarg :" str
   '(paredit-close-parenthesis) \n) & '(join-line)
  _)

(defadvice redshank-defclass-skeleton
  (after redshank-format-defclass activate)
  "Align DEFCLASS slots."
  (when redshank-reformat-defclass-skeletons
    (save-excursion
      (backward-sexp)
      (redshank-align-defclass-slots))))

(defadvice redshank-defclass-slot-skeleton
  (after redshank-reformat-defclass activate)
  "Align DEFCLASS slots."
  (when redshank-reformat-defclass-skeletons
    (save-excursion
     (backward-up-list +2)
     (redshank-align-defclass-slots))))

;;;; Initialization
(add-hook 'pre-command-hook 'redshank-unhighlight-binder)
(provide 'redshank)

;;;; Licence

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation;

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.
