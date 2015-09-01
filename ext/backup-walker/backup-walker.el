;;; backup-walker.el --- quickly traverse all backups of a file

;; this file is not part of Emacs

;; Copyright (C) 2011 Le Wang
;; Author: Le Wang
;; Maintainer: Le Wang
;; Description: quickly traverse all backups of a file

;; Created: Wed Sep  7 19:38:05 2011 (+0800)
;; Version: 0.1
;; Last-Updated: Mon Apr  1 16:59:52 2013 (+0800)
;;           By: Le Wang
;;     Update #: 135
;; URL: https://github.com/lewang/backup-walker
;; Keywords: backup
;; Compatibility: Emacs 23+



;;;{FIXME};;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                          ;;
;; 1. add find-file hoook to shorten backup buffer names with               ;;
;;    `rename-buffer'                                                       ;;
;; 2. instead of having a buffer-local state, just have a central hash      ;;
;;    keying on the unversioned backup file-name.                           ;;
;; 3. elevate minor-mode to fist class citizen that can be entered anywhere ;;
;; 4. add minor-mode to find-file hook                                      ;;
;; 5. make switch between diff and minor-mode view of backup bi-directional ;;
;; 6. don't use index, just use the suffix.  Instead update central list of ;;
;;    backups every time a new backup is opened.                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

















;;; Installation:

;;
;; add to ~/.emacs.el
;;
;;  (require 'backup-walker)
;;
;;   M-x backup-walker-start
;;
;; Of course, you should autoload, and bind the entry function to some key
;; sequence.  But the above gets you going.

;;; Commentary:

;; I never delete backups.  They are versioned in their own directory, happy
;; and safe.  My fingers skip to C-x C-s whenever I pause to think about
;; anything.  Even when I'm working with VCS, I save far more often than I
;; commit.
;;
;; This package helps me traverse those backups if I'm looking for something.
;;
;; The typical workflow is:
;;
;;   1) I'm in a buffer and realize I need to check some backups.
;;
;;        M-x backup-walker-start
;;
;;   2) I press <p> to go backwards in history until I see something
;;      interesting.  Then I press <enter> to bring it up.  OOPs this isn't
;;      it, I go back to the backup-walker window and find the right file.
;;
;;   3) I get what I need from the backup, go back to backup-walker, and press
;;      <q> and kill all open backups.
;;
;;   4) the end.
;;
;; Additionally, note that all the diff-mode facilities are available in the
;; `backup-walker' buffer.
;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Code:

(eval-when-compile
  (require 'cl))

(provide 'backup-walker)

(eval-and-compile
  (require 'diff)
  (require 'view))

(or (fboundp 'diff-no-select)
    (defun diff-no-select (old new &optional switches no-async)
      (save-window-excursion (diff old new switches no-async))
      (get-buffer-create "*Diff*")))


(easy-mmode-defmap backup-walker-ro-map
                   '(("n" . backup-walker-next)
                     ("p" . backup-walker-previous)
                     ("q" . backup-walker-quit)
                     ("b" . backup-walker-blame))
                   ""
                   :suppress t)

(easy-mmode-defmap backup-walker-mode-map
                   '(([(return)] . backup-walker-show-file-in-other-window))
                   ""
                  :inherit backup-walker-ro-map)

(defvar backup-walker-minor-mode nil "non-nil if backup walker minor mode is enabled")
(make-variable-buffer-local 'backup-walker-minor-mode)

(defsubst backup-walker-get-version (fn &optional start)
  "return version number given backup"
  (setq start (or start
                  (length (file-name-sans-versions fn))))
  (string-to-number
   (substring fn
              (string-match "[[:digit:]]+" fn start)
              (match-end 0))))

(defsubst backup-walker-get-key-help-common (index suffixes)
  (concat
   (if (eq index 0)
       ""
     (concat (propertize "<n>" 'face 'italic)
             " ~"
             (propertize (int-to-string (backup-walker-get-version (nth (1- index) suffixes)))
                         'face 'font-lock-keyword-face)
             "~ "))
   (if (nth (1+ index) suffixes)
       (concat (propertize "<p>" 'face 'italic)
               " ~"
               (propertize (int-to-string
                            (backup-walker-get-version (nth (1+ index) suffixes)))
                           'face 'font-lock-keyword-face)
               "~ ")
     "")
   (propertize "<b>" 'face 'italic)
   " blame "
   (propertize "<q>" 'face 'italic)
   " quit "))

(defsubst backup-walker-move (index-cons index suffixes new-index)
  "internal function used by backup-walker-{next,previous}"
  (cond
   ((eq major-mode 'backup-walker-mode)
    (setcdr index-cons new-index)
    (backup-walker-refresh))
   (backup-walker-minor-mode
    (let* ((prefix (cdr (assq :backup-prefix backup-walker-data-alist)))
           (new-file-name (concat prefix (nth new-index suffixes)))
           (old-file-name (concat prefix (nth index suffixes)))
           (alist (copy-alist backup-walker-data-alist))
           (saved-column (current-column))
           (saved-line (count-lines (point-min) (point)))
           (buf (find-file-noselect new-file-name)))
      (setcdr (assq :index alist) new-index)
      (set-window-buffer nil buf)
      (with-current-buffer buf
        (setq backup-walker-data-alist alist)
        (backup-walker-minor-mode 1)
        (goto-char (point-min))
        (goto-char (point-at-bol (+ saved-line
                                    (backup-walker-get-offset
                                     saved-line
                                     old-file-name
                                     new-file-name))))
        (move-to-column saved-column))))))

(define-derived-mode backup-walker-mode diff-mode "{Diff backup walker}"
  "major mode for traversing versioned backups.  Use
  `backup-walker-start' as entry point."
  (run-hooks 'view-mode-hook)         ; diff-mode sets up this hook to
                                      ; remove its read-only overrides.
  (add-to-list 'minor-mode-overriding-map-alist (cons 'buffer-read-only backup-walker-mode-map)))

(lexical-let ((overriding-element (cons 'buffer-read-only backup-walker-ro-map)))
  (defun backup-walker-minor-mode (&optional arg)
    "purposefully made non-interactive, because this mode should only be used by code"
    (setq arg (cond  ((or (null arg)
                          (eq arg 'toggle))
                      (if backup-walker-minor-mode
                          nil
                        t))
                     ((> arg 0)
                      t)
                     ((<= arg 0)
                      nil)))
    (setq backup-walker-minor-mode arg)
    (force-mode-line-update)
    (if backup-walker-minor-mode
        (let ((index (cdr (assq :index backup-walker-data-alist)))
              (suffixes (cdr (assq :backup-suffix-list backup-walker-data-alist))))
          (setq header-line-format (backup-walker-get-key-help-common index suffixes))
          (add-to-list 'minor-mode-overriding-map-alist overriding-element))
      (setq header-line-format nil)
      (setq minor-mode-overriding-map-alist
            (delq overriding-element minor-mode-overriding-map-alist)))
    backup-walker-minor-mode))

(add-minor-mode 'backup-walker-minor-mode " walker" nil nil nil)

(defvar backup-walker-data-alist nil
  "internal data")
(make-variable-buffer-local 'backup-walker-data-alist)
(put 'backup-walker-data-alist 'permanent-local t)

(defun backup-walker-get-sorted-backups (filename)
  "Return version sorted list of backups of the form:

  (prefix (list of suffixes))"
  ;; `make-backup-file-name' will get us the right directory for
  ;; ordinary or numeric backups.  It might create a directory for
  ;; backups as a side-effect, according to `backup-directory-alist'.
  (let* ((filename (file-name-sans-versions
                    (make-backup-file-name (expand-file-name filename))))
         (file (file-name-nondirectory filename))
         (dir  (file-name-directory    filename))
         (comp (file-name-all-completions file dir))
         (prefix-len (length file)))
    (cons filename (mapcar
                    (lambda (f)
                      (substring (cdr f) prefix-len))
                    (sort (mapcar (lambda (f)
                                    (cons (backup-walker-get-version f prefix-len)
                                          f))
                                  comp)
                          (lambda (f1 f2)
                            (not (< (car f1) (car f2)))))))))


(defun backup-walker-refresh ()
  (let* ((index (cdr (assq :index backup-walker-data-alist)))
         (suffixes (cdr (assq :backup-suffix-list backup-walker-data-alist)))
         (prefix (cdr (assq :backup-prefix backup-walker-data-alist)))
         (right-file (concat prefix (nth index suffixes)))
         (right-version (format "%i" (backup-walker-get-version right-file)))
         diff-buf left-file left-version)
    (if (eq index 0)
        (setq left-file (cdr (assq :original-file backup-walker-data-alist))
              left-version "orig")
      (setq left-file (concat prefix (nth (1- index) suffixes))
            left-version (format "%i" (backup-walker-get-version left-file))))
    (setq diff-buf (diff-no-select left-file right-file nil 'noasync))
    (setq buffer-read-only nil)
    (erase-buffer)
    (insert-buffer-substring diff-buf)
    (goto-char (point-min))
    (set-buffer-modified-p nil)
    (setq buffer-read-only t)
    (force-mode-line-update)
    (setq header-line-format
          (concat (format "{{ ~%s~ → ~%s~ }} "
                          (propertize left-version 'face 'font-lock-variable-name-face)
                          (propertize right-version 'face 'font-lock-variable-name-face))
                  (backup-walker-get-key-help-common index suffixes)
                  (propertize "<return>" 'face 'italic)
                  " open ~"
                  (propertize (propertize (int-to-string (backup-walker-get-version right-file))
                                          'face 'font-lock-keyword-face))
                  "~"))
    (kill-buffer diff-buf)))

;;;###autoload
(defun backup-walker-start (original-file)
  "start walking with the latest backup

with universal arg, ask for a file-name."
  (interactive (list (if (and current-prefix-arg (listp current-prefix-arg))
                         (read-file-name
                          "Original file: "
                          nil
                          buffer-file-name
                          t
                          (file-name-nondirectory buffer-file-name))
                       (or buffer-file-name
                           (error "buffer has no file name")))))
  (unless (and version-control
               (not (eq version-control 'never)))
    (error "version-control must be enabled for backup-walker to function."))
  (unless (not (backup-file-name-p original-file))
    (error "`backup-start' must be run in a non-backup buffer."))
  (unless (not (buffer-modified-p))
    (if (y-or-n-p "Save buffer (force backup) and continue?")
        (save-buffer 16)
      (error "buffer has to be unmodified to enter `backup-walker'.")))
  (let ((backups (backup-walker-get-sorted-backups original-file))
        alist
        buf)
    (if (null (cdr backups))
        (error "no backups found.")
      (push (cons :backup-prefix(car backups)) alist)
      (push (cons :backup-suffix-list (cdr backups)) alist)
      (push (cons :original-file original-file) alist)
      (push (cons :index 0) alist)
      (setq buf (get-buffer-create (format "*Walking: %s*" (buffer-name))))
      (with-current-buffer buf
        (backup-walker-mode)
        (buffer-disable-undo)
        (setq backup-walker-data-alist alist)
        (backup-walker-refresh))
      (pop-to-buffer buf))))


(defun backup-walker-next (arg)
  "move to a more recent backup
with ARG, move ARG times"
  (interactive "p")
  (cond ((< arg 0)
         (backup-walker-previous (- arg)))
        ((> arg 0)
         (let* ((index-cons (assq :index backup-walker-data-alist))
                (index (cdr index-cons))
                (suffixes (cdr (assq :backup-suffix-list backup-walker-data-alist)))
                (new-index (- index arg)))
           (if (< new-index 0)
               (signal 'args-out-of-range (list (format "not enough newer backups, max is %i" index)))
             (backup-walker-move index-cons index suffixes new-index))))))

(defun backup-walker-previous (arg)
  "move to a less recent backup
with ARG move ARG times"
  (interactive "p")
  (cond ((< arg 0)
         (backup-walker-next (- arg)))
        ((> arg 0)
         (let* ((index-cons (assq :index backup-walker-data-alist))
                (index (cdr index-cons))
                (suffixes (cdr (assq :backup-suffix-list backup-walker-data-alist)))
                (max-movement (- (1- (length suffixes)) index))
                (new-index (+ index arg)))
           (if (> arg max-movement)
               (signal 'args-out-of-range (list (format "not enough older backups, max is %i" max-movement)))
             (backup-walker-move index-cons index suffixes new-index))))))

(defun backup-walker-show-file-in-other-window ()
  "open the current backup in another window.

Only call this function interactively."
  (interactive)
  (unless (eq major-mode 'backup-walker-mode)
    (error "this is not a backup walker control buffer."))
  (let* ((index (cdr (assq :index backup-walker-data-alist)))
         (suffixes (cdr (assq :backup-suffix-list backup-walker-data-alist)))
         (prefix (cdr (assq :backup-prefix backup-walker-data-alist)))
         (file-name (concat prefix (nth index suffixes)))
         (walking-buf (current-buffer))
         (alist (copy-alist backup-walker-data-alist))
         (buf (find-file-noselect file-name)))
    (with-current-buffer buf
      (setq backup-walker-data-alist alist)
      (push (cons :walking-buf walking-buf) backup-walker-data-alist)
      (backup-walker-minor-mode 1))
    (pop-to-buffer buf)))

(defun backup-walker-blame (line)
  "find out where a certain line came into existance

show the backup *JUST BEFORE* this line was born."
  (interactive (progn
                 (unless (or (eq major-mode 'backup-walker-mode)
                             backup-walker-minor-mode)
                   (error "not in backup walker buffer"))
                 (list (read-string "line: "
                                    (when backup-walker-minor-mode
                                      (buffer-substring-no-properties (point-at-bol) (point-at-eol)))
                                    nil
                                    'backup-walker-blame))))
  (cond
   (backup-walker-minor-mode
    (let* ((my-index (cdr (assq :index backup-walker-data-alist)))
           (walking-buf (cdr (assq :walking-buf backup-walker-data-alist))))
      (with-current-buffer walking-buf
        (setcdr (assq :index backup-walker-data-alist) my-index)
        (backup-walker-refresh))
      (pop-to-buffer walking-buf)
      (backup-walker-blame line)))
   ((eq major-mode 'backup-walker-mode)
    (let* ((index-cons (assq :index backup-walker-data-alist))
           (old-index (cdr index-cons))
           (is-unified (member "-u" diff-switches))
           (search-str (format "-%s" line))
           found)
      (condition-case err
          (while (not found)
            (let ((suffixes (cdr (assq :backup-suffix-list backup-walker-data-alist)))
                  (index (cdr (assq :index backup-walker-data-alist))))
              (goto-char (point-min))
              (when (not is-unified)
                (diff-context->unified (point-min) (point-max)))
              (message "searching %s" (nth index suffixes))
              (if (search-forward search-str nil t)
                  (setq found t)
                (backup-walker-previous 1))))
        ('args-out-of-range
         (setcdr index-cons old-index)
         (backup-walker-refresh)
         (message "input was not found in backup history")))))
   (t
    (error "not sure what you want me to do."))))

(defun backup-walker-quit (arg)
  "quit backup-walker session.

Offer to kill all associated backup buffers.

with ARG, also kill the walking buffer"
  (interactive "P")
  (cond (backup-walker-minor-mode
         (pop-to-buffer (cdr (assq :walking-buf backup-walker-data-alist))))
        ((eq major-mode 'backup-walker-mode)
         (let* ((prefix (cdr (assq :backup-prefix backup-walker-data-alist)))
                (prefix-len (length prefix))
                (walking-buf (current-buffer))
                backup-bufs)
           (mapc (lambda (buf)
                   (let ((file-name (buffer-file-name buf)))
                     (when (and file-name
                                (>= (length file-name) prefix-len)
                                (string= prefix (substring file-name 0 prefix-len)))
                       (push buf backup-bufs))))
                 (buffer-list))
           (when (and (not (eq 0 (length backup-bufs)))
                      (y-or-n-p (concat (propertize (int-to-string (length backup-bufs))
                                                    'face 'highlight)
                                        " backup buffers found, kill them?")))
             (mapc (lambda (buf)
                     (kill-buffer buf))
                   backup-bufs))
           (quit-window)
           (when (and arg
                      (listp arg))
             (kill-buffer walking-buf))))
        (t
         (error "I don't know how to quit you."))))



   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;; NOTES for parsing diff outputs:                                  ;;;
   ;;;                                                                  ;;;
   ;;; diff range example:                                              ;;;
   ;;;                                                                  ;;;
   ;;;   @@ -l,r +l,r @@                                                ;;;
   ;;;                                                                  ;;;
   ;;;   ** l is line number                                            ;;;
   ;;;                                                                  ;;;
   ;;;   ** r is range                                                  ;;;
   ;;;                                                                  ;;;
   ;;;   ** When the range is 1, the range, including coma is not       ;;;
   ;;;      printed                                                     ;;;
   ;;;                                                                  ;;;
   ;;;   ** When range is 0, the line number is one less than it should ;;;
   ;;;      be.                                                         ;;;
   ;;;                                                                  ;;;
   ;;;  An alternative to doing this is to just count the `+' and `-'   ;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun backup-walker-get-offset (orig-linenum orig-file new-file)
  "ORIG-LINENUM is line position in ORIG-FILE

return an offset to adjust orig-linenum"
  (with-temp-buffer
    (call-process "diff" nil t nil "-u0" (expand-file-name orig-file) (expand-file-name new-file))
    (goto-char (point-min))
    (let (curr-line
          last-match-data)
      (loop while (re-search-forward "^@@ -\\([0-9]+\\),?\\([0-9]*\\) \\+\\([0-9]+\\),?\\([0-9]*\\) @@$"
                                     nil
                                     t)
            do (destructuring-bind (l r)
                   (backup-walker-tupple-from-hunk-header nil t)
                 (setq curr-line (+ l r))
                 (unless (> curr-line orig-linenum)
                   (setq last-match-data (match-data))))
            until (> curr-line orig-linenum))
      (if (not last-match-data)
          0
        (destructuring-bind (orig-l orig-r new-l new-r)
            (backup-walker-tupple-from-hunk-header last-match-data)
          (- (+ new-l new-r) (+ orig-l orig-r)))))))

(defun backup-walker-tupple-from-hunk-header (match-data &optional source-only)
  "LINE and SECTION are strings parsed from input

return (orig-l orig-r new-l new-r)"

  (when match-data
    (set-match-data match-data))
  (nconc
   (list
    (+ (string-to-number (match-string-no-properties 1))
       (if (equal "0" (match-string-no-properties 2))
           1
         0))
    (if (equal "" (match-string-no-properties 2))
        1
      (string-to-number (match-string-no-properties 2))))
   (when (not source-only)
     (list
      (+ (string-to-number (match-string-no-properties 3))
         (if (equal "0" (match-string-no-properties 4))
             1
           0))
      (if (equal "" (match-string-no-properties 4))
          1
        (string-to-number (match-string-no-properties 4)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; backup-walker.el ends here
