;;; nameless.el --- Hide package namespace in your emacs-lisp code  -*- lexical-binding: t; -*-

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Artur Malabarba <emacs@endlessparentheses.com>
;; URL: https://github.com/Malabarba/nameless
;; Keywords: convenience, lisp
;; Version: 0.5.1
;; Package-Requires: ((emacs "24.4"))

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Usage
;; ─────
;;
;;   To use this package add the following configuration to your Emacs init
;;   file.
;;
;;   ┌────
;;   │ (add-hook 'emacs-lisp-mode-hook #'nameless-mode)
;;   └────
;;
;;   You can configure a string to use instead of `:' by setting the
;;   `nameless-prefix', and the name of the face used is `nameless-face'.
;;
;;   While the mode is active, the `_' key inserts the package
;;   namespace if appropriate.

;;; Code:
(require 'lisp-mnt)

(defgroup nameless nil
  "Customization group for nameless."
  :group 'emacs)

(defcustom nameless-prefix ":"
  "Prefix displayed instead of package namespace."
  :type 'string)

(defcustom nameless-global-aliases '(("fl" . "font-lock"))
  "Alist from aliases to namespaces.
This alist is used everywhere.  It is designed for namespaces you
use commonly.  To apply aliases specific to a file, set the
`nameless-aliases' variable with `add-file-local-variable'.

Each element of this list should have the form (ALIAS . NAMESPACE),
both strings.  For example, if you set this variable to
          ((\"fl\" . \"font-lock\"))
then expressions like `(font-lock-add-keywords nil kwds)' will
displayed as `(fl/add-keywords nil kwds)' instead.

Furthermore typing `fl' followed by `\\[nameless-insert-name]' will
automatically insert `font-lock-'."
  :type '(alist string string))

(defvar nameless-aliases nil
  "Alist from aliases to namespaces.
This variable takes the same syntax and has the same effect as
`nameless-global-aliases'.  Aliases set here take priority over
those in `nameless-global-aliases'.
This variable is designed to be used as a file-local or dir-local
variable.")
(put 'nameless-aliases 'safe-local-variable
     (lambda (x) (ignore-errors
              (let ((safe t))
                (mapc (lambda (cell)
                        (unless (and (stringp (car cell))
                                     (stringp (cdr cell)))
                          (setq safe nil)))
                      x)
                safe))))

(defcustom nameless-discover-current-name t
  "If non-nil, discover package name automatically.
If nil, `nameless-current-name' must be set explicitly, or left as nil,
in which case only namespaces from `nameless-global-aliases' and
`nameless-aliases' are used."
  :type 'boolean)

(defface nameless-face
  '((t :inherit font-lock-type-face))
  "Face used on `nameless-prefix'")

(defcustom nameless-affect-indentation-and-filling 'outside-strings
  "If non-nil, code is indented and filled according to what you see.
If nil, code is indented and filled according to its actual content.
If the value is `outside-strings', behave like nil inside strings
and behave like t otherwise.

After changing this variable, you must reenable `nameless-mode'
for it to take effect."
  :type '(choice (const :tag "Always affect indentation" t)
                 (const :tag "Don't affect indentation" nil)
                 (const :tag "Only outside strings" outside-strings)))
(put 'nameless-current-name 'safe-local-variable #'symbolp)

(defcustom nameless-private-prefix nil
  "If non-nil, private symbols are displayed with a double prefix.
For instance, the function `foobar--internal-impl' will be
displayed as `::internal-impl', instead of `:-internal-impl'."
  :type 'boolean)

(defcustom nameless-separator "-"
  "Separator used between package prefix and rest of symbol.
The separator is hidden along with the package name.  For
instance, setting it to \"/\" means that `init/bio' will be
displayed as `:bio' (assuming `nameless-current-name' is
\"init\").  The default is \"-\", since this is the
separator recommended by the Elisp manual.

Value can also be nil, in which case the separator is never hidden."
  :type '(choice string (constant nil)))


;;; Font-locking
(defun nameless--make-composition (s)
  "Return a list that composes S if passed to `compose-region'."
  (cdr (apply #'append (mapcar (lambda (x) (list '(Br . Bl) x)) s))))

(defvar nameless-mode)
(defun nameless--compose-as (display)
  "Compose the matched region and return a face spec."
  (when (and nameless-mode
             (not (get-text-property (match-beginning 1) 'composition))
             (not (get-text-property (match-beginning 1) 'display)))
    (let ((compose (save-match-data
                     (and nameless-affect-indentation-and-filling
                          (or (not (eq nameless-affect-indentation-and-filling 'outside-strings))
                              (not (nth 3 (syntax-ppss)))))))
          (dis (concat display nameless-prefix))
          (beg (match-beginning 1))
          (end (match-end 1))
          (private-prefix (and nameless-private-prefix
                               (equal nameless-separator (substring (match-string 0) -1)))))
      (when private-prefix
        (setq beg (match-beginning 0))
        (setq end (match-end 0))
        (setq dis (concat dis nameless-prefix)))
      (if compose
          (compose-region beg end (nameless--make-composition dis))
        (add-text-properties beg end (list 'display dis)))
      '(face nameless-face))))

(defvar-local nameless--font-lock-keywords nil)

(defun nameless--ensure ()
  (save-excursion
    (font-lock-fontify-region (point-min) (point-max))))

(defun nameless--remove-keywords ()
  "Remove font-lock keywords set by `nameless--add-keywords'."
  (font-lock-remove-keywords nil nameless--font-lock-keywords)
  (setq nameless--font-lock-keywords nil)
  (nameless--ensure))

(defun nameless--add-keywords (&rest r)
  "Add font-lock keywords displaying ALIAS as DISPLAY.
ALIAS may be nil, in which case it refers to `nameless-current-name'.

\(fn (alias . display) [(alias . display) ...])"
  (setq-local font-lock-extra-managed-props
              `(composition display ,@font-lock-extra-managed-props))
  (let ((kws (mapcar (lambda (x) `(,(nameless--name-regexp (cdr x)) 1 (nameless--compose-as ,(car x)) prepend)) r)))
    (setq nameless--font-lock-keywords kws)
    (font-lock-add-keywords nil kws t))
  (nameless--ensure))


;;; Name and regexp
(defvar-local nameless-current-name nil)
(put 'nameless-current-name 'safe-local-variable #'stringp)

(defun nameless--in-arglist-p (l)
  "Is point L inside an arglist?"
  (save-excursion
    (goto-char l)
    (ignore-errors
      (backward-up-list)
      (or (progn (forward-sexp -1)
                 (looking-at-p "[a-z-]lambda\\_>"))
          (progn (forward-sexp -1)
                 (looking-at-p "\\(cl-\\)?def"))))))

(defun nameless-insert-name (&optional noerror)
  "Insert `nameless-current-name' or the alias at point.
If point is immediately after an alias configured in
`nameless-aliases' or `nameless-global-aliases', replace it with
the full name for that alias.
Otherwise, insert `nameless-current-name'.

If NOERROR is nil, signal an error if the alias at point is not
configured, or if `nameless-current-name' is nil."
  (interactive)
  (if (string-match (rx (or (syntax symbol)
                            (syntax word)))
                    (string (char-before)))
      (let* ((r (point))
             (l (save-excursion
                  (forward-sexp -1)
                  (skip-chars-forward "^[:alnum:]")
                  (point)))
             (alias (buffer-substring l r))
             (full-name (when alias
                          (cdr (or (assoc alias nameless-aliases)
                                   (assoc alias nameless-global-aliases))))))
        (if full-name
            (progn (delete-region l r)
                   (insert full-name "-")
                   t)
          (unless noerror
            (user-error "No name for alias `%s', see `nameless-aliases'" alias))))
    (if nameless-current-name
        (progn (insert nameless-current-name nameless-separator)
               t)
      (unless noerror
        (user-error "No name for current buffer, see `nameless-current-name'")))))

(defun nameless-insert-name-or-self-insert (&optional self-insert)
  "Insert the name of current package, with a hyphen."
  (interactive "P")
  (let ((l (point)))
    (call-interactively #'self-insert-command)
    (unless (or self-insert
                (not nameless-current-name)
                (eq (char-before l) ?\\)
                (nameless--in-arglist-p l))
      (undo-boundary)
      (delete-region l (point))
      (unless (nameless-insert-name 'noerror)
        (call-interactively #'self-insert-command)))))

(put 'nameless-insert-name-or-self-insert 'delete-selection t)

(defun nameless--name-regexp (name)
  "Return a regexp of the current name."
  (concat "\\_<@?\\(" (regexp-quote name)
          nameless-separator "\\)\\(\\s_\\|\\sw\\)"))

(defun nameless--filter-string (s)
  "Remove from string S any disply or composition properties.
Return S."
  (let ((length (length s)))
    (remove-text-properties 0 length '(composition nil display nil) s)
    s))


;;; Minor mode
;;;###autoload
(define-minor-mode nameless-mode
  nil nil " :" `((,(kbd "C-c C--") . nameless-insert-name))
  (if nameless-mode
      (progn
        (when (and (not nameless-current-name)
                   nameless-discover-current-name
                   (ignore-errors (string-match "\\.el\\'" (lm-get-package-name))))
          (setq nameless-current-name
                (replace-regexp-in-string "\\(-mode\\)?\\.[^.]*\\'" "" (lm-get-package-name))))
        (add-function :filter-return (local 'filter-buffer-substring-function)
                      #'nameless--filter-string)
        (apply #'nameless--add-keywords
               `(,@(when nameless-current-name
                     `((nil . ,nameless-current-name)))
                 ,@nameless-global-aliases
                 ,@nameless-aliases)))
    (remove-function (local 'filter-buffer-substring-function)
                     #'nameless--filter-string)
    (setq nameless-current-name nil)
    (nameless--remove-keywords)))

;;;###autoload
(defun nameless-mode-from-hook ()
  "Turn on `nameless-mode'.
Designed to be added to `emacs-lisp-mode-hook'.
Interactively, just invoke `nameless-mode' directly."
  (add-hook 'find-file-hook #'nameless-mode nil 'local))

;;;; ChangeLog:

;; 2015-10-14  Artur Malabarba  <bruce.connor.am@gmail.com>
;; 
;; 	Merge commit 'a3dfd7ecf9c58898241c8d1145eb8e0c875f5448'
;; 
;; 2015-09-13  Artur Malabarba  <bruce.connor.am@gmail.com>
;; 
;; 	Merge commit '29bfd8704b99f0b8600ea2bdc1f467df04c9e8bc'
;; 
;; 2015-09-13  Artur Malabarba  <bruce.connor.am@gmail.com>
;; 
;; 	Merge commit 'ea3958f45cb468be0f11e95c24d09e10a389fee0'
;; 
;; 2015-09-09  Artur Malabarba  <bruce.connor.am@gmail.com>
;; 
;; 	Merge commit '60873230991f7a0cd3175eb578fee34c7e238fb3'
;; 
;; 2015-09-07  Artur Malabarba  <bruce.connor.am@gmail.com>
;; 
;; 	Merge commit '6abd4f4fe740054d433d928d90fb1671cce6719c'
;; 
;; 2015-09-06  Artur Malabarba  <bruce.connor.am@gmail.com>
;; 
;; 	Merge commit '512b2ace3db9bf64e16f949ed90b78eb86c7fdda'
;; 
;; 2015-09-03  Artur Malabarba  <bruce.connor.am@gmail.com>
;; 
;; 	Add 'packages/nameless/' from commit
;; 	'c1dd76b972ab978884d5c1b2add43e83cc23134e'
;; 
;; 	git-subtree-dir: packages/nameless git-subtree-mainline:
;; 	4de23529e28c8c1ba5b970bda87463f3923ad362 git-subtree-split:
;; 	c1dd76b972ab978884d5c1b2add43e83cc23134e
;; 


(provide 'nameless)
;;; nameless.el ends here
