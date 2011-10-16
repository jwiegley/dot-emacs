;;; devel-notes.el --- Add annotation to sources and track them in an org file.

;; Copyright (C) 2011 Iñigo Serna, all rights reserved.

;; Author: Iñigo Serna <inigoserna at gmail dot com>
;; Created: Mon Mar 14 12:57:41 2011
;; Keywords: devel annotations TODO org
;; URL: http://www.emacswiki.org/emacs/download/devel-notes.el
;; Version: 1.0
;; Time-stamp: <2011-03-14 12:57:05 inigo>

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; NOTE
;;
;; This library is tested on Emacs 23.2.1 on Fedora 14 only.

;;; Commentary:
;;
;; Overview
;; ========
;; This library provides an easy way of adding annotations
;; to source files and track them in an org file.
;;
;;
;; INSTALLING
;; ==========
;; To install this library, save this file to a directory in your
;; `load-path' (you can view the current `load-path' using "C-h v
;; load-path RET" within Emacs), then add the following line to your
;; .emacs startup file:
;;
;;    (require 'devel-notes)
;;
;;
;; USING
;; =====
;; To add an annotation to a source file run the command
;; `develnotes-add-annotation', this will let you choose the type and comment
;; for the annotation, and it will also be saved in `develnotes-file'.
;; In case there isn't such file you will be prompted the base directory
;; where to create it.
;;
;; Note there are more `develnotes-add-TYPE' commands,
;; look at `develnotes-types-list' variable to find out existing options.
;;
;; You can create the file `develnotes-file' manually running
;; `develnotes-create-file'.
;;
;; To visit `develnotes-file' file in current window, run `develnotes-visit-file',
;; execute with a C-u to open in other window.
;;
;;
;; Customizing
;; ===========
;; You can configure some variables to customize the package behaviour.
;;
;; `develnotes-file': name of the `devel-notes' tracking file, default:
;;                    "TODO.org".
;; `develnotes-types-list': list of accepted types for entries, defaut:
;;                          ("TODO" "FIXME" "BUG" "WARNING" "NOTE" "HACK" "XXX").
;; `develnotes-timestamp-format': tTimestamp format, default "%Y/%m/%d %H:%M".
;;
;;
;; Key map Examples
;; ================
;; (global-set-key "\C-cza" 'develnotes-add-annotation)
;; (global-set-key "\C-czv" 'develnotes-visit-file)
;; (global-set-key "\C-czt" 'develnotes-add-TODO)
;; (global-set-key "\C-czf" 'develnotes-add-FIXME)
;;
;;
;; TODO and KNOWN PROBLEMS
;; =======================
;; . why tags are not aligned properly?
;; . add-entry-into-develnotes-file: timestamp as org-timestamp, as org-property?

;;; Change Log:

;;  v1.0, Mon Mar 14 12:01:11 2011
;;   - Initial public release

;;; Code:


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; package variables
(defvar develnotes-file "TODO.org"
  "Name of the `devel-notes' tracking file.")

(defvar develnotes-types-list '("TODO" "FIXME" "BUG" "WARNING" "NOTE" "HACK" "XXX")
  "List of accepted types for TODO entries.")

(defvar develnotes-timestamp-format "%Y/%m/%d %H:%M"
  "Timestamp format.")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; utils
(defun split-string-with-max (string delimiter max)
  "Split STRING by DELIMITER with a MAX maximum number of items after split."
  (let (newlist
        item
        (alist (split-string string delimiter))
        (numitems (- max 1)))
    (while (> numitems 0)
      (push (pop alist) newlist)
      (setq numitems (- numitems 1)))
    (reverse (cons (mapconcat 'identity alist delimiter) newlist))))


(defun trim-whitespace (string)
  "Trim whitespace from start and end of STRING."
  (when (string-match "^\\s *\\(.*?\\)\\s *$" string)
    (match-string-no-properties 1 string)))


;; (defun make-my-function (type)
;;   (list 'defun (intern (format "todo-insert-%s" type)) ()
;;         (list 'interactive)
;;         (list 'todo-insert-entry (format "%s" type))))
(defun make-my-function (type)
  "Generate `develnotes-add-TYPE' commands."
  `(defun ,(intern (format "develnotes-add-%s" type)) ()
     (interactive)
     (develnotes-add-entry ,(format "%s" type))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; internal functions
(defun add-entry-into-develnotes-file (notetype srcfile linenumber comment &optional timestamp)
  "Add a new `devel-notes' org-formatted entry at the end of current buffer."
  (unless (org-mode-p)
    (org-mode))
  (save-excursion
    (widen)
    (goto-char (point-max))
    (org-insert-heading)
    (insert (format "[[file:%s::%s][%s:%s]]\n  %s\n" srcfile linenumber
                    srcfile linenumber (trim-whitespace comment)))
    (org-set-tags-to notetype)
    (when timestamp
      (insert (format "  Added: %s\n" (format-time-string develnotes-timestamp-format))))))
      ;; (org-insert-time-stamp nil t t "  "))))
      ;; (org-set-property "Date and Time" (format-time-string develnotes-timestamp-format)))))


(defun develnotes-add-entry (notetype)
   "Insert a new `devel-note' entry of type NOTETYPE to current source file
and add it to `develnotes-file' file."
  ; check buffer-file-name is not nil and buffer writable
  (let ((srcfile (buffer-file-name))
        (linenumber (line-number-at-pos))
        (comment (read-from-minibuffer (format "Add %s annotation: " notetype)))
        (now (format-time-string develnotes-timestamp-format))
        (notesfile (or (develnotes-find-file) (develnotes-create-file))))
    (unless (file-writable-p srcfile)
      (error "Can't modify this file"))
    ; insert into current file
    (insert (format "%s: %s\n" notetype comment))
    (save-excursion
      (comment-region (- (point) (1+ (length (concat notetype ": " comment)))) (point)))
    ; and add it to notes file
    (let ((buffer (get-file-buffer notesfile)))
      (if buffer
          ; Todo.org already opened in a buffer
          (with-current-buffer buffer
            (add-entry-into-develnotes-file notetype srcfile linenumber comment now)
            (write-region nil nil notesfile nil t))
        ; file not opened
        (with-temp-buffer
          (add-entry-into-develnotes-file notetype srcfile linenumber comment now)
          (goto-char (point-min))
          (delete-char 1)
          (append-to-file nil nil notesfile))))))


(defun develnotes-find-file (&optional filename)
  "Search for `develnotes-file' starting at current buffer file directory
upwards and returns it or nil if not found.
Optional arg FILENAME specifies the file to use as starting point
in the search instead of current buffer file."
  (if (or filename buffer-file-name)
      (let* ((olddir nil)
             (dir (file-name-directory (or filename buffer-file-name)))
             (fullpath (concat dir develnotes-file)))
        (catch 'break
          (while (not (file-exists-p fullpath))
            (if (string= dir olddir)
                (throw 'break nil))
            (setq olddir dir
                  dir (file-name-directory (directory-file-name dir))
                  fullpath (concat dir develnotes-file)))
          fullpath))
    nil))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; public commands
(defun develnotes-create-file (&optional dir)
  "Create a new `develnotes-file' in the specified DIR and populate
with the entries found in the source files under it."
  ; ask for dir where todo.org will be created
  (interactive "DSelect directory: ")
  (unless dir
    (setq dir (read-directory-name "Select directory: " nil nil t)))
  (with-temp-buffer
    (let* ((filename (concat dir develnotes-file))
           entries
           buf
           (excluded_files (append (mapcar (lambda (x) (concat x "*")) (list develnotes-file "TAGS")) grep-find-ignored-files))
           (str_excluded_files (concat " --exclude=" (mapconcat 'identity excluded_files " --exclude=")))
           (str_excluded_dirs (concat " --exclude-dir=" (mapconcat 'identity grep-find-ignored-directories " --exclude-dir="))))
      (message "Process grep started, please wait")
      ; header
      (org-mode)
      (insert (format "%s\t-*- mode: org; -*-\n\n" filename)
              (format "#+TAGS: %s\n\n" (mapconcat 'identity develnotes-types-list " ")))
      ; for each type
      (dolist (type develnotes-types-list)
        ; get and process grep output => ((filename lineno comment) ...)
        (setq buf (shell-command-to-string (format "grep -rnw \"%s\" %s %s \"%s\""
                                                   type str_excluded_files str_excluded_dirs dir)))
        (dolist (line (split-string buf "\n"))
          (unless (string= line "")
            (push (cons type (append (split-string-with-max line ":" 3) '(t))) entries))))

      ; sort entries by (filename, lineno)
      (sort entries (lambda (l1 l2)
                      (let ((s1 (cadr l1))
                            (s2 (cadr l2)))
                        (if (string= s1 s2)
                            (string< (nth 2 l1) (nth 2 l2))
                          (string< s1 s2)))))
      ; insert formatted entry into buffer
      (dolist (entry entries)
        (apply 'add-entry-into-develnotes-file entry))
      ; write file, checking if file does exist
      (write-region nil nil filename nil nil nil t)
      filename)))


(defun develnotes-visit-file ()
  "Open `develnotes-file' in current window or in other window if C-u."
  (interactive)
  (let ((notesfile (or (develnotes-find-file) (develnotes-create-file))))
    (if notesfile
        (progn
          (if (null current-prefix-arg)
              (find-file notesfile)
            (find-file-other-window notesfile))
          ; <============================>
          (let ((re (concat "^" outline-regexp)))
            (save-excursion
              (goto-char (point-min))
              (while (re-search-forward re nil t)
                (org-set-tags nil t)
                (end-of-line 1))))
          (save-buffer)
          ; <============================>
          (message (format "%s loaded" develnotes-file)))
      (error (format "File %s not found" develnotes-file)))))


(defun develnotes-add-annotation ()
   "Ask for a new `devel-note' annotation to be inserted to current source file
and add it to `develnotes-file' file as well."
   (interactive)
   (let (fn)
     (if (symbol-function 'ido-completing-read)
         (defun fn () (ido-completing-read "Annotation type: " develnotes-types-list))
       (defun fn () (read-string "Annotation type: " "TODO")))
     (let ((notetype (fn)))
       (if (member notetype develnotes-types-list)
           (develnotes-add-entry notetype)
         (error (format "Annotation type '%s' not valid.\nChoose between %s\nor customize 'develnotes-types-list' variable."
                        notetype
                        (mapconcat 'identity develnotes-types-list ", ")))))))


; create develnotes-add-XXX commands
(dolist (type develnotes-types-list)
  (eval (make-my-function type)))


(provide 'devel-notes)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
