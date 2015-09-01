;;; ee-info.el --- browse Info documentation

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee, help

;; This file is [not yet] part of GNU Emacs.

;; This package is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This package is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this package; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; See the file README and documentation for more information.

;; This file contains two main parts: one for ee-info-dir and one for ee-info:
;; ee-info-dir has the unique index buffer created from dir,
;; ee-info has own buffer for index of every visited info file.

;; TODO: make ee-info-history tree

;; TODO: look in the texinfo.info for all possible node types:
;;   1. The menu entry name (optional).
;;   2. The name of the node (required).
;;   3. A description of the item (optional).
;;   The template for a menu entry looks like this:
;;      * MENU-ENTRY-NAME: NODE-NAME.   DESCRIPTION

;; TODO: Make clear why there are three types of menu links:
;; * Introduction::            Introduction and conventions used.
;; * Standards: Coding Conventions.    Coding conventions for Emacs Lisp.
;; * add-to-list:                           Setting Variables.

;; TODO: Make clear why there are four names of the same node,
;; e.g. in the next three lines from different parts of Info:
;; * Standards: Coding Conventions.    Coding conventions for Emacs Lisp.
;; Emacs Lisp Coding Conventions
;; =============================
;; there are next topis names:
;; 1. "Standards"
;; 2. "Coding Conventions"
;; 3. "Coding conventions for Emacs Lisp"
;; 4. "Emacs Lisp Coding Conventions"

;; Rough correspondence to HTML:
;; <DT><A HREF="Coding Conventions">Standards</A><DD>Coding conventions for Emacs Lisp.
;; <TITLE>Emacs Lisp Coding Conventions</TITLE>

;;; Code:

(require 'ee)

(eval-when-compile
  (require 'info))

;;; Constants

;; Name "ee-info" (the same as next variable) is better than "ee-info-dir"
(defconst ee-info-dir-mode-name "ee-info")
(defconst ee-info-mode-name "ee-info")

;;; Customizable Variables

(defgroup ee-info nil
  "Browse Info documentation."
  :prefix "ee-info-"
  :group 'ee)

(defcustom ee-info-dir-read-section-names nil
  "Non-nil means to extract section names (defined by `INFO-DIR-SECTION')
from all info files accessible from dir."
  :type 'file
  :group 'ee-info)

(defcustom ee-info-data-file-name-format "info-%s.ee"
  "Format used to create data file name to save data collected from info files.
Format may contain %s which will be replaced by info file name."
  :type 'file
  :group 'ee-info)

;;; Local Variables

(defvar ee-info-file nil
  "Current info file name.")

;;; Info dir

;;; Data Description

(defvar ee-info-dir-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/info-dir.ee")
     (data-file . "info-dir.ee")
     (collector . ee-info-dir-data-collect)
     (fields title filename nodename dir-section info-dir-section ())
     (key-fields filename))])

;;; Data Extraction

;; TODO: refresh data when DIR is updated, i.e. Info-dir-contents
;; (or it's length or checksum) is not the same as prev value
(defun ee-info-dir-data-collect (data)
  (let ((new-data
         (ee-data-convert-lists-to-vectors
          (ee-info-dir-read-directory-node
           (ee-data-field-names data)))))
    (aset new-data 0 (aref data 0))
    new-data))

(defun ee-info-dir-read-directory-node (field-names)
  "
Output: [[title filename nodename dir-section info-dir-section] ...]
"
  ;; TODO: save in file with time-stamp, and update if date of one of
  ;; dir files is newer (this functionality is in (Info-insert-dir),
  ;; so compare string returned by (Info-insert-dir)?)
  (with-temp-buffer
    (Info-insert-dir)
    (goto-char (point-min))
    (if (search-forward "\n* Menu:" nil t)
        (let (res section)
          (forward-line 1)
          (while (not (eobp))
            (beginning-of-line)
            (cond
             ;; Menu line
             ((looking-at (concat "^\\* +\\([^:\t\n]*\\):"
                                  ;; Skip non-Top menu items
                                  "[ \t\n]*([^)\t\n]+)\\."))
              (let* ((title (match-string-no-properties 1))
                     (nodename (Info-extract-menu-node-name))
                     filename)
                (string-match "\\s *\\((\\s *\\([^\t)]*\\)\\s *)\\s *\\|\\)\\(.*\\)"
                              nodename)
                (setq filename (if (= (match-beginning 1) (match-end 1))
                                   ""
                                 (substring-no-properties nodename (match-beginning 2) (match-end 2)))
                      nodename (substring-no-properties nodename (match-beginning 3) (match-end 3)))
                (let ((trim (string-match "\\s *\\'" filename)))
                  (if trim (setq filename (substring-no-properties filename 0 trim))))
                (let ((trim (string-match "\\s *\\'" nodename)))
                  (if trim (setq nodename (substring-no-properties nodename 0 trim))))
                (setq res
                      (cons
                       (mapcar
                        (lambda (field-name)
                          (cond
                           ((eq field-name 'title) title)
                           ((eq field-name 'filename) (if (equal filename "") nil filename))
                           ((eq field-name 'nodename) (if (equal nodename "") "Top" nodename))
                           ((eq field-name 'dir-section) section) ; section name from dir
                           ((eq field-name 'info-dir-section) nil) ; place for INFO-DIR-SECTION names
                           ;; TODO: extract and add the titles
                           ))
                        field-names)
                       res))))
             ;; Other non-empty strings in the dir buffer are section names
             ((looking-at "^\\([^ \t\n*][^:\n]*\\)")
              (setq section (match-string-no-properties 1))))
            (forward-line 1))
          ;; Read section names from INFO-DIR-SECTION from info files
          (if ee-info-dir-read-section-names ;;TODO: move to data-fields of view-descr
              (save-excursion
                (setq res (mapcar
                           (lambda (r)
                             (when (equal (aref r 2) "Top")
                               (Info-find-node (aref r 1) "Top")
                               (widen)
                               (goto-char (point-min))
                               (let ((sections))
                                 (while (re-search-forward "\nINFO-DIR-SECTION +\\([^\n]+\\)" nil t)
                                   (setq sections (cons (match-string-no-properties 1) sections)))
                                 (and sections (aset r 4 (nreverse sections)))))
                             r)
                           res))))
          (nreverse res)))))

;;; Actions

(defun ee-info-dir-ee-info (&optional arg)
  (interactive)
  (let ((filename (ee-field 'filename)))
    (and filename (ee-info filename))))

(defun ee-info-dir-find-node (&optional arg)
  (let* ((r (ee-view-record-get))
         (filename (ee-field 'filename))
         (nodename (ee-field 'nodename)))
    (when r
      ;; Pop to *info* to save previous node into Info-history
      (pop-to-buffer "*info*")
      (Info-find-node filename nodename))))

;;; Key Bindings

(defvar ee-info-dir-keymap nil
  "Local keymap for ee-info-dir-mode info-dir.")

;; TODO: move keybindings to defvar view/info-dir.ee?
(defun ee-info-dir-keymap-make-default ()
  "Defines default key bindings for `ee-info-dir-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "\C-o" 'ee-info-dir-find-node)
    (setq ee-info-dir-keymap map)))

(or ee-info-dir-keymap
    (ee-info-dir-keymap-make-default))

;;; Info files

;;; Data Description

(defvar ee-info-data
  '[(meta
     ;; (data-file . "info-%s.ee")
     (format-version . "0.0.1")
     (view-data-file . "view/info.ee")
     (collector . ee-info-data-collect)
     (fields nodename category menulist indexlist ())
     (key-fields nodename))])

;;; Data Extraction

(defun ee-info-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (new-data
          (ee-data-convert-lists-to-vectors
           (mapcar
            (lambda (node)
              (mapcar
               (lambda (field-name)
                 (cond
                  ((eq field-name 'nodename) (nth 0 node))
                  ((eq field-name 'category) (nth 1 node))
                  ((eq field-name 'menulist) (nth 2 node))
                  ;; ((eq field-name 'indexlist) (nth 3 node)) ; not used
                  ))
               field-names))
            (Info-build-toc ee-info-file)))))
    (aset new-data 0 (aref data 0))
    (let ((hack (aref new-data 1)))
      (aset hack 2 nil)
      (aset new-data 1 hack))
    new-data))

(or (fboundp 'Info-build-toc)
;; from GNU Emacs 21.4
(defun Info-build-toc (file)
  "Build table of contents from menus of Info FILE and its subfiles."
  (setq file (Info-find-file file))
  (with-temp-buffer
    (let ((default-directory (or (file-name-directory file)
                                 default-directory))
          (sections '(("Top" "Top")))
          nodes subfiles)
      (while (or file subfiles)
        (or file (message "Searching subfile %s..." (car subfiles)))
        (erase-buffer)
        (info-insert-file-contents (or file (car subfiles)))
        (while (and (search-forward "\n\^_\nFile:" nil 'move)
                    (search-forward "Node: " nil 'move))
          (let ((nodename (substring-no-properties (Info-following-node-name)))
                (bound (- (or (save-excursion (search-forward "\n\^_" nil t))
                              (point-max)) 2))
                (section "Top")
                menu-items)
            (when (and (not (string-match "\\<index\\>" nodename))
                       (re-search-forward "^\\* Menu:" bound t))
              (forward-line 1)
              (beginning-of-line)
              (setq bound (or (and (equal nodename "Top")
                                   (save-excursion
                                     (re-search-forward
                                      "^[ \t-]*The Detailed Node Listing" nil t)))
                              bound))
              (while (< (point) bound)
                (cond
                 ;; Menu item line
                 ((looking-at "^\\* +[^:]+:")
                  (beginning-of-line)
                  (forward-char 2)
                  (let ((menu-node-name (substring-no-properties
                                         (Info-extract-menu-node-name))))
                    (setq menu-items (cons menu-node-name menu-items))
                    (if (equal nodename "Top")
                        (setq sections
                              (cons (list menu-node-name section) sections)))))
                 ;; Other non-empty strings in the Top node are section names
                 ((and (equal nodename "Top")
                       (looking-at "^\\([^ \t\n*=.-][^:\n]*\\)"))
                  (setq section (match-string-no-properties 1))))
                (forward-line 1)
                (beginning-of-line)))
            (setq nodes (cons (list nodename
                                    (cadr (assoc nodename sections))
                                    (nreverse menu-items))
                              nodes))
            (goto-char bound)))
        (if file
            (save-excursion
              (goto-char (point-min))
              (if (search-forward "\n\^_\nIndirect:" nil t)
                  (let ((bound (save-excursion (search-forward "\n\^_" nil t))))
                    (while (re-search-forward "\\(^.*\\): [0-9]+$" bound t)
                      (setq subfiles (cons (match-string-no-properties 1)
                                           subfiles)))))
              (setq subfiles (nreverse subfiles)
                    file nil))
          (setq subfiles (cdr subfiles))))
      (message "")
      (nreverse nodes)))))

;;; Actions

(defun ee-info-find-node (&optional arg other-window)
  (interactive)
  (let ((nodename (ee-field 'nodename))
        ;; Set ee-info-file to info-file, because buffer-local
        ;; ee-info-file is not available after switching to *info*
        (info-file ee-info-file))
    ;; Mark as read and update view
    (ee-field-set 'read t)
    (ee-view-update '(read)) ;; (ee-view-record-update)
    (when other-window
      (if (one-window-p)
          ;; (split-window-vertically 11)
          (split-window-horizontally 33))
      (select-window (next-window)))
    ;;     (some-window (lambda (w)
    ;;                    (eq (buffer-name (window-buffer w)) "*info*")
    ;;                    ;(eq (window-buffer w) ee-parent-buffer)
    ;;                    ))
    (when nodename
      ;; Pop to *info* to save previous node into Info-history
      (pop-to-buffer "*info*")
      (Info-find-node info-file nodename))
      (if (eq other-window 'display)
          (select-window (next-window)))))

(defun ee-info-find-node-other-window (&optional arg)
  (interactive)
  (ee-info-find-node arg t))

(defun ee-info-find-node-other-window-display (&optional arg)
  (interactive)
  (ee-info-find-node arg 'display))

(defun ee-info-mark-bookmark ()
  (interactive)
  (if (ee-field 'bookmark)
      (ee-field-set 'bookmark nil)
    (ee-field-set 'bookmark t))
  (ee-view-update '(bookmark)) ;; (ee-view-record-update)
  )

(defun ee-info-mark-unread ()
  (interactive)
  (if (ee-field 'read)
      (ee-field-set 'read nil)
    (ee-field-set 'read t))
  (ee-view-update '(read)) ;; (ee-view-record-update)
  )

(defun ee-info-next-unread ()
  (interactive)
  (ee-view-record-next-with
   (lambda () (eq (ee-field 'read) nil)))
  (ee-info-find-node-other-window-display))

;;; Key Bindings

(defvar ee-info-keymap nil
  "Local keymap for ee-info-mode info.")

;; TODO: move keybindings to defvar view/info.ee?
(defun ee-info-keymap-make-default ()
  "Defines default key bindings for `ee-info-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "e" 'ee-info-find-node)
    (define-key map "o" 'ee-info-find-node-other-window)
    (define-key map "\C-o" 'ee-info-find-node-other-window-display)
    (define-key map "b" 'ee-info-mark-bookmark)
    ;; TODO: same keys as in Gnus
    (define-key map "\M-r" 'ee-info-mark-unread)
    (define-key map "\M-u" 'ee-info-mark-unread)
    (define-key map [tab] 'ee-info-next-unread)
    (setq ee-info-keymap map)))

(or ee-info-keymap
    (ee-info-keymap-make-default))

;;; Top-Level Functions

(defun ee-info-follow-selection ()
  (let ((node Info-current-node)
        (file Info-current-file)
        (curr-buffer (current-buffer))
        (curr-window (selected-window))
        buffer)
    (mapc (lambda (dir)
            (if (and (stringp file) (string-match (concat "^" dir) file))
                (setq file (substring-no-properties file (length dir)))))
          Info-directory-list)
    (setq buffer (format "*%s*/%s" ee-info-mode-name file))
    (cond ((get-buffer-window buffer)
           (select-window (get-buffer-window buffer))
           (let ((r (car (ee-data-records-find ee-data (cons 'nodename node)))))
             (when r
               (ee-view-record-by-key (ee-field 'nodename r))
               ;; TODO: expand hidden branch
               (ee-field-set 'read t)
               (ee-view-update '(read))))
           (select-window curr-window))
          ((get-buffer buffer)
           (set-buffer buffer)
           (let ((r (car (ee-data-records-find ee-data (cons 'nodename node)))))
             (when r
               (ee-view-record-by-key (ee-field 'nodename r))
               ;; TODO: expand hidden branch
               (ee-field-set 'read t)
               (ee-view-update '(read))))
           (set-buffer curr-buffer)))))

(defun ee-info-follow-selection-toggle ()
  (interactive)
  (if (member 'ee-info-follow-selection Info-selection-hook)
      (remove-hook 'Info-selection-hook 'ee-info-follow-selection)
    (add-hook 'Info-selection-hook 'ee-info-follow-selection)))

;; TODO: place next into e.g. (if ee-info-selection-hook-p ...)
;; or                         (if ee-info-follow-nodes ...)
(ee-info-follow-selection-toggle)

;;;###autoload
(defun ee-info (&optional file)
  "Enter ee-info, the documentation browser.
Optional argument FILE specifies the file to examine;
the default is the top-level directory of Info.

In interactive use, a prefix argument directs this command
to read a file name from the minibuffer.

The search path for Info files is in the variable `Info-directory-list'.
The top-level Info directory is made by combining all the files named `dir'
in all the directories in that path."
  (interactive (if current-prefix-arg
                   ;; TODO: make list of available info node names
                   (list (read-file-name "Info file name: " nil nil t))))
  (require 'info)
  ;; Initialize `Info-directory-list'
  (and (fboundp 'info-initialize) (info-initialize))
  (or (boundp 'Info-selection-hook)
      (defvar Info-selection-hook nil))
  (if (not (stringp file))
      (ee-view-buffer-create
       (format "*%s*/dir" ee-info-dir-mode-name)
       ee-info-dir-mode-name
       ee-info-dir-keymap
       ee-info-dir-data)
    (setq ee-info-file file)
    (ee-view-buffer-create
     (format "*%s*/%s" ee-info-mode-name file)
     ee-info-mode-name
     ee-info-keymap
     ee-info-data
     nil
     nil ;; TODO: setq ee-parent-buffer to *info*?
     nil
     (format ee-info-data-file-name-format file)
     t ;; auto-save
     )))

(provide 'ee-info)

;;; ee-info.el ends here
