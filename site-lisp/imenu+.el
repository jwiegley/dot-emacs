;;; imenu+.el --- Extensions to `imenu.el'.
;;
;; Filename: imenu+.el
;; Description: Extensions to `imenu.el'.
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 1999-2011, Drew Adams, all rights reserved.
;; Created: Thu Aug 26 16:05:01 1999
;; Version: 21.0
;; Last-Updated: Fri May 27 08:56:55 2011 (-0700)
;;           By: dradams
;;     Update #: 665
;; URL: http://www.emacswiki.org/cgi-bin/wiki/imenu+.el
;; Keywords: tools, menus
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x
;;
;; Features that might be required by this library:
;;
;;   `imenu'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;; Extensions to `imenu.el'.
;;
;;   New functions defined here:
;;
;;    `imenu-add-defs-to-menubar', `imenu--sort-submenu',
;;    `toggle-imenu-sort'.
;;
;;   New user options (variables) defined here:
;;
;;    `emacs-lisp-imenu-generic-expression',
;;    `imenu-emacs-face-defn-regexp', `imenu-emacs-key-defn-regexp-1',
;;    `imenu-emacs-key-defn-regexp-2',
;;    `imenu-emacs-option-defn-regexp', `imenu-lisp-fn-defn-regexp',
;;    `imenu-lisp-macro-defn-regexp', `imenu-lisp-other-defn-regexp',
;;    `imenu-lisp-var-defn-regexp', `imenu-sort-function'.
;;
;;   Other variables defined here:
;;
;;    `imenu-last-sort-function'.
;;
;;
;;  ***** NOTE: The following functions defined in `imenu.el' have
;;              been REDEFINED HERE:
;;
;;  `imenu--mouse-menu', `imenu-update-menubar'.
;;
;;
;;  ***** NOTE: The following variable defined in `imenu.el' has
;;              been REDEFINED HERE:
;;
;;  `imenu-sort-function'.
;;
;;  ***** NOTE: The following variable defined in `lisp-mode.el' has
;;              been REDEFINED HERE:
;;
;;  `lisp-imenu-generic-expression'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change log:
;;
;; 2011/05/27 dadams
;;     imenu-lisp-var-defn-regexp:
;;       Corrected to allow \n after var name (\n is comment-end syntax, not whitespace, in Lisp).
;; 2011/05/08 dadams
;;     imenu-lisp-var-defn-regexp: Try not to create entries for vacuous defvars, e.g., (defvar foo).
;; 2011/03/18 dadams
;;     imenu-emacs-key-defn-regexp-[1|2]: Handle (kbd "...").
;;     emacs-lisp-imenu-generic-expression: Increased index from 4 to 5, to fit change for kbd.
;; 2011/01/04 dadams
;;     Removed autoload cookies from defvar, non-interactive fns.  Added for command.
;; 2007/01/16 dadams
;;     imenu-lisp-fn-defn-regexp: Updated for icicle-define-add-to-alist-command.
;; 2005/12/09 dadams
;;     imenu-lisp-fn-defn-regexp: Updated to include icicle-define*.
;;       Use regexp-opt for Emacs 20 version too.
;;       Moved Emacs 22 macro stuff to imenu-lisp-macro-defn-regexp.
;;     (emacs-)lisp-imenu-generic-expression:
;;       Updated Emacs 20 index to accomodate parens for icicle-define*.
;;     Added: imenu-emacs-(face|option)-defn-regexp, 
;;     Removed: imenu-lisp-struct-defn-regexp.
;;     Renamed: imenu-lisp-type-defn-regexp to imenu-lisp-other-defn-regexp.
;; 2005/05/17 dadams
;;     Updated to work with Emacs 22.x.
;; 2004/11/21 dadams
;;     imenu-lisp-type-defn-regexp, imenu-lisp-fn-defn-regexp,
;;     imenu-lisp-var-defn-regexp: Got rid of purecopy & eval-when-compile.
;; 2004/11/20 dadams
;;     Refined to deal with Emacs 21 < 21.3.50 (soon to be 22.x)
;; 2004/10/12 dadams
;;     Updated for Emacs 21.
;; 2001/01/05 dadams
;;     Unquoted mapcar lambda args.
;; 2000/11/01 dadams
;;     Put imenu-add-defs-to-menubar inside condition-case, in (*-)lisp-mode-hooks
;; 1999/08/30 dadams
;;     1. imenu-emacs-key-defn-regexp-2: Added define-key-after.
;;     2. Updated emacs-lisp-imenu-generic-expression (Keys in Maps).
;; 1999/08/27 dadams
;;     1. Corrected: imenu-lisp-fn-defn-regexp, imenu-lisp-macro-defn-regexp,
;;                   imenu-lisp-var-defn-regexp, imenu--sort-submenu,
;;                   imenu-emacs-key-defn-regexp-2.
;;     2. Added: imenu--sort-submenu, imenu-update-menubar, imenu--mouse-menu.
;;        Redefinition of originals: imenu-update-menubar, imenu--mouse-menu.
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

(and (< emacs-major-version 20) (eval-when-compile (require 'cl))) ;; cadr, when, unless

(require 'imenu)

;; Quiet the byte-compiler
(defvar imenu-menubar-modified-tick)

;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Customizable variables

(defconst imenu-sort-function 'imenu--sort-by-name)

;; For key definitions, we need to handle: strings and vectors, but also (kbd STRING).
;; We just match optional `(kbd ' followed by a string or a vector'.
(defvar imenu-emacs-key-defn-regexp-1 "(\\s-*\\(\\(global\\|local\\)-\\(un\\)?\
set-key\\|undefine-keys-bound-to\\)\\s-*\\((kbd\\s-*\\)?\\(\"[^\"]+\"\\|[[][^]]+[]]\\)"
  "*Regexp that recognizes Emacs key definitions.
See also `imenu-emacs-key-defn-regexp-2'.")

(defvar imenu-emacs-key-defn-regexp-2 "(\\s-*\\(define-key\\(-after\\)?\\s-+\
\\|substitute-key-definition\\s-+'\\)\\(\\S-+\\)\\s-*'?\\((kbd\\s-*\\)?\\(\"[^\"]+\"\\|[[][^]]+[]]\\)"
  "*Regexp that recognizes Emacs key definitions.
See also `imenu-emacs-key-defn-regexp-1'.")

(defvar imenu-lisp-other-defn-regexp
  (if (>= emacs-major-version 22)
      (concat "^\\s-*("
              (regexp-opt '("defgroup" "deftheme" "deftype" "defstruct"
                            "defclass" "define-condition" "define-widget"
                            "defpackage") t)
              "\\s-+'?\\(\\sw\\(\\sw\\|\\s_\\)+\\)")
    "(\\s-*def\\(type\\|class\\|ine-condition\\)\\s-+'?\\([^ \t()]+\\)")
  "*Regexp that recognizes other Lisp definitions.")

(defvar imenu-lisp-fn-defn-regexp
  (if (>= emacs-major-version 22)
      (concat "^\\s-*("
              (regexp-opt '("defun" "defun*" "defsubst" "defadvice"
                            "define-skeleton" "define-minor-mode"
                            "define-global-minor-mode" "define-globalized-minor-mode"
                            "define-derived-mode" "define-generic-mode" "defsetf"
                            "define-setf-expander" "define-method-combination"
                            "defgeneric" "defmethod" "icicle-define-command"
                            "icicle-define-file-command") t)
              "\\s-+\\(\\sw\\(\\sw\\|\\s_\\)+\\)")
    (concat "^\\s-*("
            (regexp-opt
             '("defun" "defun*" "defsubst" "defadvice" "define-skeleton"
               "define-derived-mode" "defsetf" "icicle-define-add-to-alist-command"
               "icicle-define-command" "icicle-define-file-command") t)
            "\\s-+\\(\\sw\\(\\sw\\|\\s_\\)+\\)"))
  "*Regexp that recognizes Lisp function definitions.")

(defvar imenu-lisp-macro-defn-regexp
  "(\\s-*\\(defmacro\\|define-compiler-macro\\|define-modify-macro\\)\\s-+\\([^ \t()]+\\)"
  "*Regexp that recognizes Lisp macro definitions.")

(defvar imenu-emacs-face-defn-regexp "(\\s-*\\(defface\\)\\s-+\\([^ \t()]+\\)"
  "*Regexp for Emacs face definitions (defface).")

(defvar imenu-emacs-option-defn-regexp "(\\s-*\\(defcustom\\)\\s-+\\([^ \t()]+\\)"
  "*Regexp for Emacs user option definitions (defcustom).")

(defvar imenu-lisp-var-defn-regexp
  (if (>= emacs-major-version 22)
      (concat "^\\s-*("
              (regexp-opt '("defvar" "defconst" "defconstant" "defcustom"
                            "defparameter" "define-symbol-macro") t)
              "\\s-+\\(\\sw\\(\\sw\\|\\s_\\)+\\)"
              "\\(\\s-\\|[\n]\\)+"      ; Because \n has char syntax `>', not whitespace.
              "[^) \t\n]")
    "(\\s-*def\\(var\\|const\\)\\s-+\\([^ \t()]+\\)")
  "*Regexp that recognizes global Lisp variable definitions.")


;; REPLACE ORIGINAL in `lisp-mode.el'.
;;
;; Add `Functions', `Macros', `Structures'.
;;
(defconst lisp-imenu-generic-expression
  (list
   (list "Other" imenu-lisp-other-defn-regexp 2)
   (list "Macros" imenu-lisp-macro-defn-regexp 2)
   (list "Functions" imenu-lisp-fn-defn-regexp (if (string-match "\\(?:\\)" "") 2 6))
   (list "Variables" imenu-lisp-var-defn-regexp 2)
   )
  "*Imenu generic expression for Lisp mode.
See `imenu-generic-expression'.")

(defvar emacs-lisp-imenu-generic-expression
  (list
   (list "Other" imenu-lisp-other-defn-regexp 2)
   (list "Keys in Maps" imenu-emacs-key-defn-regexp-2 5)
   (list "Keys" imenu-emacs-key-defn-regexp-1 5)
   (list "Macros" imenu-lisp-macro-defn-regexp 2)
   (list "Functions" imenu-lisp-fn-defn-regexp (if (string-match "\\(?:\\)" "") 2 6))
   (list "Variables" imenu-lisp-var-defn-regexp 2)
   (list "User Options" imenu-emacs-option-defn-regexp 2)
   (list "Faces" imenu-emacs-face-defn-regexp 2)
   )
  "*Imenu generic expression for Emacs Lisp mode.
See `imenu-generic-expression'.")

(add-hook 'lisp-mode-hook
          '(lambda ()
            (setq imenu-generic-expression lisp-imenu-generic-expression)
            (condition-case nil
                (imenu-add-defs-to-menubar)
              (error nil))))

(add-hook 'emacs-lisp-mode-hook
          '(lambda ()
             (setq imenu-generic-expression emacs-lisp-imenu-generic-expression)
             (condition-case nil
                 (imenu-add-defs-to-menubar)
               (error nil))))


;;; Internal variables

(defvar imenu-last-sort-function nil
  "The last non-nil value for `imenu-sort-function' during this session.")

;;;###autoload
(defalias 'toggle-imenu-sort 'imenu-toggle-sort)
;;;###autoload
(defun imenu-toggle-sort (force-p)
  "Toggle imenu between sorting menus and not.
Non-nil prefix FORCE-P => Sort iff FORCE-P >= 0."
  (interactive "P")
  (cond (imenu-sort-function
         (setq imenu-last-sort-function imenu-sort-function) ; Save it.
         (when (or (null force-p) (<= (prefix-numeric-value force-p) 0))
           (setq imenu-sort-function nil))) ; Don't sort.
        ((or (null force-p) (> (prefix-numeric-value force-p) 0)) ; Ask to sort
         (if imenu-last-sort-function  ; Sort using saved sort fn.
             (setq imenu-sort-function imenu-last-sort-function)
           (error "You first need to set `imenu-sort-function'"))))
  (imenu--menubar-select imenu--rescan-item)
  (if imenu-sort-function
      (message "Imenus are now being sorted via `%s'." imenu-sort-function)
    (message "Imenus are in buffer order (not sorted).")))

;;;###autoload
(defun imenu-add-defs-to-menubar ()
  "Add \"Defs\" imenu entry to menu bar for current local keymap.
See `imenu' for more information."
  (interactive)
  (imenu-add-to-menubar "Defs"))

(defun imenu--sort-submenu (submenu predicate)
  "Create an imenu SUBMENU, sorting with PREDICATE."
  (let ((menu-name (car submenu))
        (menu-items (cdr submenu)))
    (cons menu-name (if (and (consp menu-items)
                             (consp (cdr menu-items)))
                        (sort menu-items predicate)
                      menu-items))))


;; REPLACE ORIGINAL in `imenu.el'.
;;
;; Sort each submenu before splitting submenus, instead of sorting among submenus after.
;;
(defun imenu-update-menubar ()
  "Update the Imenu menu.  Use as `menu-bar-update-hook'."
  (when (and (current-local-map)
             (keymapp (lookup-key (current-local-map) [menu-bar index]))
             (or (not (boundp 'imenu-menubar-modified-tick))
                 (not (eq (buffer-modified-tick)
                          imenu-menubar-modified-tick))))
    (when (boundp 'imenu-menubar-modified-tick)
      (setq imenu-menubar-modified-tick (buffer-modified-tick)))
    (let ((index-alist (imenu--make-index-alist t)))
      ;; Don't bother updating if the index-alist has not changed
      ;; since the last time we did it.
      (unless (equal index-alist imenu--last-menubar-index-alist)
        (let (menu menu1 old)
          (setq imenu--last-menubar-index-alist index-alist)
          (setq index-alist
                (imenu--split-submenus
                 (if imenu-sort-function
                     (mapcar (lambda (sm) (imenu--sort-submenu sm imenu-sort-function))
                             index-alist)
                   index-alist)))
          (setq menu (imenu--split-menu index-alist (buffer-name)))
          (if (>= emacs-major-version 22)
              (setq menu1 (imenu--create-keymap (car menu)
                                                (cdr (if (< 1 (length (cdr menu)))
                                                         menu
                                                       (car (cdr menu))))
                                                'imenu--menubar-select))
            (setq menu1 (imenu--create-keymap-1 (car menu)
                                                (if (< 1 (length (cdr menu)))
                                                    (cdr menu)
                                                  (cdr (car (cdr menu))))
                                                t)))
          (setq old (lookup-key (current-local-map) [menu-bar index]))
          (setcdr old (cdr menu1)))))))



;; REPLACE ORIGINAL in `imenu.el'.
;;
;; Sort each submenu before splitting submenus, instead of sorting among submenus after.
;;
(defun imenu--mouse-menu (index-alist event &optional title)
  "Let the user select from a buffer index from a mouse menu.
INDEX-ALIST is the buffer index.
EVENT is a mouse event.
TITLE is the menu title.
Returns t for rescan, or else an element or subelement of INDEX-ALIST."
  (setq index-alist (imenu--split-submenus
                     (if imenu-sort-function
                         (mapcar (lambda (sm)
                                   (imenu--sort-submenu sm imenu-sort-function))
                                 index-alist)
                       index-alist)))
  (if (>= emacs-major-version 22)
      (let* ((menu (imenu--split-menu index-alist (or title (buffer-name))))
             (map (imenu--create-keymap (car menu)
                                        (cdr (if (< 1 (length (cdr menu)))
                                                 menu
                                               (car (cdr menu)))))))
        (popup-menu map event))
    (let* ((menu (imenu--split-menu index-alist (or title (buffer-name))))
           position)
      (setq menu (imenu--create-keymap-1 (car menu)
                                         (if (< 1 (length (cdr menu)))
                                             (cdr menu)
                                           (cdr (cadr menu)))))
      (setq position (x-popup-menu event menu))
      (cond ((eq position nil)
             position)
            ;; If one call to x-popup-menu handled the nested menus,
            ;; find the result by looking down the menus here.
            ((and (listp position)
                  (numberp (car position))
                  (stringp (nth (1- (length position)) position)))
             (let ((final menu))
               (while position
                 (setq final (assq (car position) final))
                 (setq position (cdr position)))
               (or (string= (car final) (car imenu--rescan-item))
                   (nthcdr 3 final))))
            ;; If x-popup-menu went just one level and found a leaf item,
            ;; return the INDEX-ALIST element for that.
            ((and (consp position)
                  (stringp (car position))
                  (null (cdr position)))
             (or (string= (car position) (car imenu--rescan-item))
                 (assq (car position) index-alist)))
            ;; If x-popup-menu went just one level
            ;; and found a non-leaf item (a submenu),
            ;; recurse to handle the rest.
            ((listp position)
             (imenu--mouse-menu position event
                                (if title
                                    (concat title imenu-level-separator
                                            (car (rassq position index-alist)))
                                  (car (rassq position index-alist)))))))))

;;;;;;;;;;;;;;;;;;

(provide 'imenu+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; imenu+.el ends here
