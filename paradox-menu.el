;;; paradox-menu.el --- defining the Packages menu -*- lexical-binding:t -*-

;; Copyright (C) 2014-2015 Artur Malabarba <bruce.connor.am@gmail.com>

;; Author: Artur Malabarba <bruce.connor.am@gmail.com>
;; Prefix: paradox
;; Separator: -

;;; License:
;;
;; This file is NOT part of GNU Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;

;;; Change Log:
;; 
;;; Code:
(require 'cl-lib)
(require 'package)
(require 'paradox-core)
(require 'paradox-github)
(require 'paradox-commit-list)
(require 'paradox-execute)

(defgroup paradox-menu nil
  "Paradox Packages Menu configurations."
  :prefix "paradox-"
  :package-version '(paradox . "2.0")
  :group 'paradox)


;;; Customization Variables
(defcustom paradox-column-width-package  18
  "Width of the \"Package\" column."
  :type 'integer
  :group 'paradox-menu
  :package-version '(paradox . "0.1"))

(defcustom paradox-column-width-version  9
  "Width of the \"Version\" column."
  :type 'integer
  :group 'paradox-menu
  :package-version '(paradox . "0.1"))

(defcustom paradox-column-width-status  10
  "Width of the \"Status\" column."
  :type 'integer
  :group 'paradox-menu
  :package-version '(paradox . "0.1"))

(defcustom paradox-column-width-star 4
  "Width of the \"Star\" column."
  :type 'integer
  :group 'paradox-menu
  :package-version '(paradox . "0.1"))

(defcustom paradox-column-width-download 4
  "Width of the \"Download Count\" column."
  :type 'integer
  :group 'paradox-menu
  :package-version '(paradox . "1.1"))

(defcustom paradox-display-star-count t
  "If non-nil, adds a \"Star\" column to the Package Menu."
  :type 'boolean
  :group 'paradox-menu
  :package-version '(paradox . "1.1"))

(defcustom paradox-display-download-count nil
  "If non-nil, adds a \"Download\" column to the Package Menu."
  :type 'boolean
  :group 'paradox-menu
  :package-version '(paradox . "1.2.3"))

(defface paradox-mode-line-face
  '((t :inherit mode-line-buffer-id :weight normal :foreground "Black"))
  "Face used on the package's name."
  :group 'paradox)
(defface paradox-name-face
  '((t :inherit link))
  "Face used on the package's name."
  :group 'paradox)
(defface paradox-homepage-button-face
  '((t :underline t :inherit font-lock-comment-face))
  "Face used on the homepage button."
  :group 'paradox)
;; (defface paradox-version-face
;;   '((t :inherit default))
;;   "Face used on the version column."
;;   :group 'paradox)
(defface paradox-archive-face
  '((t :inherit paradox-comment-face))
  "Face used on the archive column."
  :group 'paradox)
(defface paradox-star-face
  '((t :inherit font-lock-string-face))
  "Face used on the star column, for packages you haven't starred."
  :group 'paradox)
(defface paradox-starred-face
  '((t :inherit font-lock-variable-name-face))
  "Face used on the star column, for packages you have starred."
  :group 'paradox)
(defface paradox-download-face
  '((t :inherit font-lock-keyword-face))
  "Face used on the Downloads column."
  :group 'paradox)
(defface paradox-description-face
  '((t :inherit default))
  "Face used on the description column.
If `paradox-lines-per-entry' > 1, the face
`paradox-description-face-multiline' is used instead."
  :group 'paradox)
(defface paradox-description-face-multiline
  '((t :inherit font-lock-doc-face))
  "Face used on the description column when `paradox-lines-per-entry' > 1.
If `paradox-lines-per-entry' = 1, the face
`paradox-description-face' is used instead."
  :group 'paradox)

(defcustom paradox-status-face-alist
  '(("built-in"  . font-lock-builtin-face)
    ("available" . default)
    ("new"       . bold)
    ("held"      . font-lock-constant-face)
    ("disabled"  . font-lock-warning-face)
    ("installed" . font-lock-comment-face)
    ("dependency" . font-lock-comment-face)
    ("incompat"  . font-lock-comment-face)
    ("deleted"   . font-lock-comment-face)
    ("unsigned"  . font-lock-warning-face))
  "List of (\"STATUS\" . FACE) cons cells.
When displaying the package menu, FACE will be used to paint the
Version, Status, and Description columns of each package whose
status is STATUS."
  :type '(repeat (cons string face))
  :group 'paradox-menu
  :package-version '(paradox . "2.0"))

(defcustom paradox-homepage-button-string "h"
  "String used to for the link that takes you to a package's homepage."
  :type 'string
  :group 'paradox-menu
  :package-version '(paradox . "0.10"))

(defcustom paradox-use-homepage-buttons t
  "If non-nil a button will be added after the name of each package.
This button takes you to the package's homepage."
  :type 'boolean
  :group 'paradox-menu
  :package-version '(paradox . "0.10"))

(defcustom paradox-lines-per-entry 1
  "Number of lines used to display each entry in the Package Menu.
1 Gives you the regular package menu.
2 Displays the description on a separate line below the entry.
3+ Adds empty lines separating the entries."
  :type 'integer
  :group 'paradox-menu
  :package-version '(paradox . "0.10"))


;;; Internal
(defvar-local paradox--current-filter nil)

(defvar paradox--column-name-star
  (if (char-displayable-p ?\x2605) "\x2605" "*"))

(defvar paradox--column-name-download
  (if (char-displayable-p ?\x2193) "\x2193" "DC"))

(defvar paradox--upgradeable-packages nil)
(defvar paradox--upgradeable-packages-number nil)
(defvar paradox--upgradeable-packages-any? nil)

(defvar paradox--column-index-star nil)
(defvar paradox--column-index-download nil)

(defvar paradox--desc-suffix nil)
(defvar paradox--desc-prefix nil)

(defvar paradox--commit-list-buffer "*Package Commit List*")


;;; Building the packages buffer.
(defun paradox-refresh-upgradeable-packages ()
  "Refresh the list of upgradeable packages."
  (interactive)
  (setq paradox--upgradeable-packages (package-menu--find-upgrades))
  (setq paradox--upgradeable-packages-number
        (length paradox--upgradeable-packages))
  (setq paradox--upgradeable-packages-any?
        (> paradox--upgradeable-packages-number 0)))

(defun paradox--print-info (pkg)
  "Return a package entry suitable for `tabulated-list-entries'.
PKG has the form (PKG-DESC . STATUS).
Return (PKG-DESC [STAR NAME VERSION STATUS DOC])."
  (let* ((pkg-desc (car pkg))
         (status  (cdr pkg))
         (face (or (cdr (assoc-string status paradox-status-face-alist))
                   'font-lock-warning-face))
         (url (paradox--package-homepage pkg-desc))
         (name (symbol-name (package-desc-name pkg-desc)))
         (name-length (length name))
         (button-length (length paradox-homepage-button-string)))
    (paradox--incf status)
    (list pkg-desc
          `[,(concat
              (propertize name
                          'face 'paradox-name-face
                          'button t
                          'follow-link t
                          'help-echo (format "Package: %s" name)
                          'package-desc pkg-desc
                          'action 'package-menu-describe-package)
              (if (and paradox-use-homepage-buttons url
                       (< (+ name-length button-length) paradox-column-width-package))
                  (concat
                   (make-string (- paradox-column-width-package name-length button-length) ?\s)
                   (propertize paradox-homepage-button-string
                               'face 'paradox-homepage-button-face
                               'mouse-face 'custom-button-mouse
                               'help-echo (format "Visit %s" url)
                               'button t
                               'follow-link t
                               'action 'paradox-menu-visit-homepage))
                ""))
            ,(propertize (package-version-join
                          (package-desc-version pkg-desc))
                         'font-lock-face face)
            ,(propertize status 'font-lock-face face)
            ,@(if (cdr package-archives)
                  (list (propertize (or (package-desc-archive pkg-desc) "")
                                    'font-lock-face 'paradox-archive-face)))
            ,@(paradox--count-print (package-desc-name pkg-desc))
            ,(propertize
              (concat (propertize " " 'display paradox--desc-prefix)
                      (package-desc-summary pkg-desc)
                      (propertize " " 'display paradox--desc-suffix)) ;└╰
              'font-lock-face
              (if (> paradox-lines-per-entry 1)
                  'paradox-description-face-multiline
                'paradox-description-face))])))

(defun paradox--count-print (pkg)
  "Return counts of PKG as a package-desc list."
  (append
   (when (and paradox-display-star-count (listp paradox--star-count))
     (list (paradox--package-star-count pkg)))
   (when (and paradox-display-download-count (listp paradox--download-count))
     (list (paradox--package-download-count pkg)))))

(defun paradox--package-download-count (pkg)
  "Return propertized string with the download count of PKG."
  (let ((c (cdr-safe (assoc pkg paradox--download-count))))
    (propertize
     (if (numberp c)
         (if (> c 999) (format "%sK" (truncate c 1000)) (format "%s" c))
       " ")
     'face 'paradox-download-face
     'value (or c 0))))

(defun paradox--package-homepage (pkg)
  "PKG can be the package-name symbol or a package-desc object."
  (let* ((object   (if (symbolp pkg) (cadr (assoc pkg package-archive-contents)) pkg))
         (name     (if (symbolp pkg) pkg (package-desc-name pkg)))
         (extras   (package-desc-extras object))
         (homepage (and (listp extras) (cdr-safe (assoc :url extras)))))
    (or homepage
        (and (setq extras (cdr (assoc name paradox--package-repo-list)))
             (format "https://github.com/%s" extras)))))
(defun paradox--get-or-return-package (pkg)
  "Take a marker or package name PKG and return a package name."
  (if (or (markerp pkg) (null pkg))
      (if (derived-mode-p 'package-menu-mode)
          (package-desc-name (tabulated-list-get-id))
        (error "Not in Package Menu"))
    pkg))

(defun paradox--incf (status)
  "Increment the count for STATUS on `paradox--package-count'.
Also increments the count for \"total\"."
  (paradox--inc-count status)
  (unless (string= status "obsolete")
    (paradox--inc-count "total")))

(defun paradox--inc-count (string)
  "Increment the cdr of (assoc-string STRING paradox--package-count)."
  (let ((cons (assoc-string string paradox--package-count)))
    (setcdr cons (1+ (cdr cons)))))

(defun paradox--entry-star-count (entry)
  "Get the star count of the package in ENTRY."
  (paradox--package-star-count
   ;; The package symbol should be in the ID field, but that's not mandatory,
   (or (ignore-errors (elt (car entry) 1))
       ;; So we also try interning the package name.
       (intern (car (elt (cadr entry) 0))))))

(defun paradox--refresh-star-count ()
  "Download the star-count file and populate the respective variable."
  (interactive)
  (unwind-protect
      (with-current-buffer
          (url-retrieve-synchronously paradox--star-count-url)
        (when (search-forward "\n\n" nil t)
          (setq paradox--star-count (read (current-buffer)))
          (setq paradox--package-repo-list (read (current-buffer)))
          (setq paradox--download-count (read (current-buffer))))
        (kill-buffer))
    (unless (and (listp paradox--star-count)
                 (listp paradox--package-repo-list)
                 (listp paradox--download-count))
      (message "[Paradox] Error downloading the list of repositories.  This might be a proxy"))
    (unless (listp paradox--download-count)
      (setq paradox--download-count nil))
    (unless (listp paradox--package-repo-list)
      (setq paradox--package-repo-list nil))
    (unless (listp paradox--star-count)
      (setq paradox--star-count nil)))
  (when (stringp paradox-github-token)
    (paradox--refresh-user-starred-list)))

(defun paradox--package-star-count (package)
  "Get the star count of PACKAGE."
  (let ((count (cdr (assoc package paradox--star-count)))
        (repo (cdr-safe (assoc package paradox--package-repo-list))))
    (propertize
     (format "%s" (or count ""))
     'face
     (if (and repo (assoc-string repo paradox--user-starred-list))
         'paradox-starred-face
       'paradox-star-face))))

(defun paradox--star-predicate (A B)
  "Non-nil t if star count of A is larget than B."
  (> (string-to-number (elt (cadr A) paradox--column-index-star))
     (string-to-number (elt (cadr B) paradox--column-index-star))))
(defun paradox--download-predicate (A B)
  "Non-nil t if download count of A is larget than B."
  (> (get-text-property 0 'value (elt (cadr A) paradox--column-index-download))
     (get-text-property 0 'value (elt (cadr B) paradox--column-index-download))))

(defun paradox--generate-menu (remember-pos packages &optional keywords)
  "Populate the Package Menu, without hacking into the header-format.
If REMEMBER-POS is non-nil, keep point on the same entry.
PACKAGES should be t, which means to display all known packages,
or a list of package names (symbols) to display.

With KEYWORDS given, only packages with those keywords are
shown."
  (paradox-menu--refresh packages keywords)
  (setq paradox--current-filter
        (if keywords (mapconcat 'identity keywords ",")
          nil))
  (let ((idx (paradox--column-index "Package")))
    (setcar (elt tabulated-list-format idx)
            (if keywords
                (concat "Package[" paradox--current-filter "]")
              "Package")))
  (tabulated-list-print remember-pos)
  (tabulated-list-init-header)
  (paradox--update-mode-line))

(defun paradox-menu--refresh (&optional packages keywords)
  "Call `package-menu--refresh' retaining current filter.
PACKAGES and KEYWORDS are passed to `package-menu--refresh'.  If
KEYWORDS is nil and `paradox--current-filter' is non-nil, it is
used to define keywords."
  (mapc (lambda (x) (setf (cdr x) 0)) paradox--package-count)
  (let ((paradox--desc-prefix (if (> paradox-lines-per-entry 1) " \n      " ""))
        (paradox--desc-suffix (make-string (max 0 (- paradox-lines-per-entry 2)) ?\n)))
    (cond
     ((or packages keywords (not paradox--current-filter))
      (package-menu--refresh packages keywords)
      (paradox-refresh-upgradeable-packages))
     ((string= paradox--current-filter "Upgrade")
      (paradox-refresh-upgradeable-packages)
      (paradox-filter-upgrades))
     (t
      (paradox-menu--refresh
       packages (split-string paradox--current-filter ","))))))

(defun paradox--column-index (regexp)
  "Find the index of the column that matches REGEXP."
  (cl-position (format "\\`%s\\'" (regexp-quote regexp)) tabulated-list-format
               :test (lambda (x y) (string-match x (or (car-safe y) "")))))

(defun paradox--count-format ()
  "List of star/download counts to be used as part of the entry."
  (remove
   nil
   (list
    (when paradox-display-star-count
      (list paradox--column-name-star paradox-column-width-star
            'paradox--star-predicate :right-align t))
    (when paradox-display-download-count
      (list paradox--column-name-download paradox-column-width-download
            'paradox--download-predicate :right-align t)))))

(defun paradox--archive-format ()
  "List containing archive to be used as part of the entry."
  (when (cdr package-archives)
    (list (list "Archive"
                (apply 'max (mapcar 'length (mapcar 'car package-archives)))
                'package-menu--archive-predicate))))

(add-hook 'paradox-menu-mode-hook 'paradox-refresh-upgradeable-packages)


;;; Mode Definition
(define-derived-mode paradox-menu-mode tabulated-list-mode "Paradox Menu"
  "Major mode for browsing a list of packages.
Letters do not insert themselves; instead, they are commands.
\\<paradox-menu-mode-map>
\\{paradox-menu-mode-map}"
  (hl-line-mode 1)
  (paradox--update-mode-line)
  (setq tabulated-list-format
        `[("Package" ,paradox-column-width-package package-menu--name-predicate)
          ("Version" ,paradox-column-width-version nil)
          ("Status" ,paradox-column-width-status package-menu--status-predicate)
          ,@(paradox--archive-format)
          ,@(paradox--count-format)
          ("Description" 0 nil)])
  (setq paradox--column-index-star
        (paradox--column-index paradox--column-name-star))
  (setq paradox--column-index-download
        (paradox--column-index paradox--column-name-download))
  (setq tabulated-list-padding 2)
  (setq tabulated-list-sort-key (cons "Status" nil))
  (add-hook 'tabulated-list-revert-hook #'paradox-menu--refresh nil t)
  (add-hook 'tabulated-list-revert-hook #'paradox-refresh-upgradeable-packages nil t)
  ;; (add-hook 'tabulated-list-revert-hook #'paradox--refresh-star-count nil t)
  (add-hook 'tabulated-list-revert-hook #'paradox--update-mode-line 'append t)
  (tabulated-list-init-header)
  ;; We need package-menu-mode to be our parent, otherwise some
  ;; commands throw errors.  But we can't actually derive from it,
  ;; otherwise its initialization will screw up the header-format.  So
  ;; we "patch" it like this.
  (put 'paradox-menu-mode 'derived-mode-parent 'package-menu-mode)
  (run-hooks 'package-menu-mode-hook))

(defun paradox--define-sort (name &optional key)
  "Define sorting by column NAME and bind it to KEY.
Defines a function called paradox-sort-by-NAME."
  (let ((symb (intern (format "paradox-sort-by-%s" (downcase name))))
        (key (or key (substring name 0 1))))
    (eval
     `(progn
        (defun ,symb
            (invert)
          ,(format "Sort Package Menu by the %s column." name)
          (interactive "P")
          (when invert
            (setq tabulated-list-sort-key (cons ,name nil)))
          (tabulated-list--sort-by-column-name ,name))
        (define-key paradox-menu-mode-map ,(concat "S" (upcase key)) ',symb)
        (define-key paradox-menu-mode-map ,(concat "S" (downcase key)) ',symb)))))

(paradox--define-sort "Package")
(paradox--define-sort "Status")
(paradox--define-sort paradox--column-name-star "*")
(declare-function paradox-sort-by-package "paradox-menu")

(defalias 'paradox-filter-clear #'package-show-package-list
  "Clear current Package filter.
Redisplay the Packages buffer listing all packages, without
fetching the list.")

(defun paradox-filter-upgrades ()
  "Show only upgradable packages."
  (interactive)
  (if (null paradox--upgradeable-packages)
      (message "No packages have upgrades.")
    (package-show-package-list
     (mapcar #'car paradox--upgradeable-packages))
    (setq paradox--current-filter "Upgrade")
    (paradox-sort-by-package nil)))

(set-keymap-parent paradox-menu-mode-map package-menu-mode-map)
(defvar paradox--filter-map)
(define-prefix-command 'paradox--filter-map)
(define-key paradox-menu-mode-map "q" #'paradox-quit-and-close)
(define-key paradox-menu-mode-map "p" #'paradox-previous-entry)
(define-key paradox-menu-mode-map "n" #'paradox-next-entry)
(define-key paradox-menu-mode-map "k" #'paradox-previous-describe)
(define-key paradox-menu-mode-map "j" #'paradox-next-describe)
(define-key paradox-menu-mode-map "f" 'paradox--filter-map)
(define-key paradox-menu-mode-map "s" #'paradox-menu-mark-star-unstar)
(define-key paradox-menu-mode-map "h" #'paradox-menu-quick-help)
(define-key paradox-menu-mode-map "v" #'paradox-menu-visit-homepage)
(define-key paradox-menu-mode-map "l" #'paradox-menu-view-commit-list)
(define-key paradox-menu-mode-map "x" #'paradox-menu-execute)
(define-key paradox-menu-mode-map "\r" #'paradox-push-button)
(define-key paradox-menu-mode-map "F" 'package-menu-filter)
(define-key paradox--filter-map "k" #'package-menu-filter)
(define-key paradox--filter-map "f" #'package-menu-filter)
(define-key paradox--filter-map "r" #'occur)
(define-key paradox--filter-map "o" #'occur)
(define-key paradox--filter-map "u" #'paradox-filter-upgrades)
(define-key paradox--filter-map "c" #'paradox-filter-clear)


;;; Menu Mode Commands
(defun paradox-previous-entry (&optional n)
  "Move to previous entry, which might not be the previous line.
With prefix N, move to the N-th previous entry."
  (interactive "p")
  (paradox-next-entry (- n))
  (forward-line 0)
  (forward-button 1))

(defun paradox-next-entry (&optional n)
  "Move to next entry, which might not be the next line.
With prefix N, move to the N-th next entry."
  (interactive "p")
  (dotimes (_ (abs n))
    (let ((d (cl-signum n)))
      (forward-line (if (> n 0) 1 0))
      (if (eobp) (forward-line -1))
      (forward-button d))))

(defun paradox-next-describe (&optional n)
  "Move to the next package and describe it.
With prefix N, move to the N-th next package instead."
  (interactive "p")
  (paradox-next-entry n)
  (call-interactively 'package-menu-describe-package))

(defun paradox-previous-describe (&optional n)
  "Move to the previous package and describe it.
With prefix N, move to the N-th previous package instead."
  (interactive "p")
  (paradox-previous-entry n)
  (call-interactively 'package-menu-describe-package))

(defun paradox-push-button ()
  "Push button under point, or describe package."
  (interactive)
  (if (get-text-property (point) 'action)
      (call-interactively 'push-button)
    (call-interactively 'package-menu-describe-package)))

(defvar paradox--key-descriptors
  '(("next," "previous," "install," "delete," ("execute," . 1) "refresh," "help")
    ("star," "visit homepage")
    ("list commits")
    ("filter by" "+" "upgrades" "regexp" "keyword" "clear")
    ("Sort by" "+" "Package name" "Status" "*(star)")))

(defun paradox-menu-quick-help ()
  "Show short key binding help for `paradox-menu-mode'.
The full list of keys can be viewed with \\[describe-mode]."
  (interactive)
  (message (mapconcat 'paradox--prettify-key-descriptor
                      paradox--key-descriptors "\n")))

(defun paradox-quit-and-close (kill)
  "Bury this buffer and close the window.
With prefix KILL, kill the buffer instead of burying."
  (interactive "P")
  (let ((log (get-buffer-window paradox--commit-list-buffer)))
    (when (window-live-p log)
      (quit-window kill log))
    (quit-window kill)))

(defun paradox-menu-visit-homepage (pkg)
  "Visit the homepage of package named PKG.
PKG is a symbol.  Interactively it is the package under point."
  (interactive '(nil))
  (let ((url (paradox--package-homepage
              (paradox--get-or-return-package pkg))))
    (if (stringp url)
        (browse-url url)
      (message "Package %s has no homepage."
               (propertize (symbol-name pkg)
                           'face 'font-lock-keyword-face)))))

(defun paradox-menu-mark-star-unstar ()
  "Star or unstar a package and move to the next line."
  (interactive)
  (paradox--enforce-github-token
   (unless paradox--user-starred-list
     (paradox--refresh-user-starred-list))
   ;; Get package name
   (let ((pkg (paradox--get-or-return-package nil))
         will-delete repo)
     (unless pkg (error "Couldn't find package-name for this entry"))
     ;; get repo for this package
     (setq repo (cdr-safe (assoc pkg paradox--package-repo-list)))
     ;; (Un)Star repo
     (if (not repo)
         (message "This package is not a GitHub repo.")
       (setq will-delete (member repo paradox--user-starred-list))
       (paradox--star-repo repo will-delete)
       (cl-incf (cdr (assoc pkg paradox--star-count))
                (if will-delete -1 1))
       (tabulated-list-set-col paradox--column-name-star
                               (paradox--package-star-count pkg)))))
  (forward-line 1))

(defun paradox-menu-view-commit-list (pkg)
  "Visit the commit list of package named PKG.
PKG is a symbol.  Interactively it is the package under point."
  (interactive '(nil))
  (let* ((name (paradox--get-or-return-package pkg))
         (repo (cdr (assoc name paradox--package-repo-list))))
    (if repo
        (with-selected-window
            (display-buffer (get-buffer-create paradox--commit-list-buffer))
          (paradox-commit-list-mode)
          (setq paradox--package-repo repo)
          (setq paradox--package-name name)
          (setq paradox--package-version
                (paradox--get-installed-version name))
          (setq paradox--package-tag-commit-alist
                (paradox--get-tag-commit-alist repo))
          (paradox--commit-list-update-entries)
          (tabulated-list-print))
      (message "Package %s is not a GitHub repo." pkg))))


;;; Mode-line Construction
(defcustom paradox-local-variables
  '(mode-line-mule-info
    mode-line-client
    mode-line-remote mode-line-position
    column-number-mode size-indication-mode)
  "Variables which will take special values on the Packages buffer.
This is a list, where each element is either SYMBOL or (SYMBOL . VALUE).

Each SYMBOL (if it is bound) will be locally set to VALUE (or
nil) on the Packages buffer."
  :type '(repeat (choice symbol (cons symbol sexp)))
  :group 'paradox-menu
  :package-version '(paradox . "0.1"))

(defcustom paradox-display-buffer-name nil
  "If nil, *Packages* buffer name won't be displayed in the mode-line."
  :type 'boolean
  :group 'paradox-menu
  :package-version '(paradox . "0.2"))

(defun paradox--build-buffer-id (st n)
  "Return a list that propertizes ST and N for the mode-line."
  `((:propertize ,st
                 face paradox-mode-line-face)
    (:propertize ,(int-to-string n)
                 face mode-line-buffer-id)))

(defun paradox--update-mode-line ()
  "Update `mode-line-format'."
  (mapc #'paradox--set-local-value paradox-local-variables)
  (let ((total-lines (int-to-string (line-number-at-pos (point-max)))))
    (paradox--update-mode-line-front-space total-lines)
    (paradox--update-mode-line-buffer-identification total-lines))
  (set-face-foreground
   'paradox-mode-line-face
   (-when-let (fg (or (face-foreground 'mode-line-buffer-id nil t)
                      (face-foreground 'default nil t)))
     (if (> (color-distance "white" fg)
            (color-distance "black" fg))
         "black" "white"))))

(defun paradox--update-mode-line-buffer-identification (_total-lines)
  "Update `mode-line-buffer-identification'.
TOTAL-LINES is currently unused."
  (require 'spinner)
  (setq mode-line-buffer-identification
        `((paradox-display-buffer-name
           ,(propertized-buffer-identification
             (format "%%%sb" (length (buffer-name)))))
          (paradox--current-filter (:propertize ("[" paradox--current-filter "]") face paradox-mode-line-face))
          (paradox--upgradeable-packages-any?
           (:eval (paradox--build-buffer-id " Upgrade:" paradox--upgradeable-packages-number)))
          (package-menu--new-package-list
           (:eval (paradox--build-buffer-id " New:" (paradox--cas "new"))))
          ,(paradox--build-buffer-id " Installed:" (+ (paradox--cas "installed")
                                                      (paradox--cas "dependency")
                                                      (paradox--cas "unsigned")))
          (paradox--current-filter
           "" ,(paradox--build-buffer-id " Total:" (length package-archive-contents)))
          (spinner-current " Executing Transaction"))))

(defvar sml/col-number)
(defvar sml/numbers-separator)
(defvar sml/col-number-format)
(defvar sml/line-number-format)
(defvar sml/position-construct)
(declare-function sml/compile-position-construct "sml")
(defvar sml/post-id-separator)
(defun paradox--update-mode-line-front-space (total-lines)
  "Update `mode-line-front-space'.
TOTAL-LINES is the number of lines in the buffer."
  (if (memq 'sml/post-id-separator mode-line-format)
      (progn
        (add-to-list (make-local-variable 'mode-line-front-space)
                     (propertize " (" 'face 'sml/col-number))
        (setq column-number-mode line-number-mode)
        (set (make-local-variable 'sml/numbers-separator) "")
        (set (make-local-variable 'sml/col-number-format)
             (format "/%s)" total-lines))
        (set (make-local-variable 'sml/line-number-format)
             (format "%%%sl" (length total-lines)))
        (make-local-variable 'sml/position-construct)
        (sml/compile-position-construct))
    (set (make-local-variable 'mode-line-front-space)
         `(line-number-mode
           ("(" (:propertize ,(format "%%%sl" (length total-lines)) face mode-line-buffer-id) "/"
            ,total-lines ")")))
    (set (make-local-variable 'mode-line-modified) nil)))

(defun paradox--set-local-value (x)
  "Locally set value of (car X) to (cdr X)."
  (let ((sym (or (car-safe x) x)))
    (when (boundp sym)
      (set (make-local-variable sym) (cdr-safe x)))))

(defun paradox--prettify-key-descriptor (desc)
  "Prettify DESC to be displayed as a help menu."
  (if (listp desc)
      (if (listp (cdr desc))
          (mapconcat 'paradox--prettify-key-descriptor desc "   ")
        (let ((place (cdr desc))
              (out (car desc)))
          (setq out (propertize out 'face 'paradox-comment-face))
          (add-text-properties place (1+ place) '(face paradox-highlight-face) out)
          out))
    (paradox--prettify-key-descriptor (cons desc 0))))

(defun paradox--full-name-reader ()
  "Return all \"full_name\" properties in the buffer.
Much faster than `json-read'."
  (let (out)
    (while (search-forward-regexp
            "^ *\"full_name\" *: *\"\\(.*\\)\", *$" nil t)
      (push (match-string-no-properties 1) out))
    (goto-char (point-max))
    out))

(provide 'paradox-menu)
;;; paradox-menu.el ends here
