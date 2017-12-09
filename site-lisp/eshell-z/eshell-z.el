;;; eshell-z.el --- cd to frequent directory in eshell  -*- lexical-binding: t; -*-

;; Copyright (C) 2015, 2016, 2017  Chunyang Xu

;; Author: Chunyang Xu <mail@xuchunyang.me>
;; Package-Requires: ((cl-lib "0.5"))
;; Keywords: convenience
;; Version: 0.3.1
;; Homepage: https://github.com/xuchunyang/eshell-z

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
;;
;; `eshell-z.el' is an Emacs port of z(1) <https://github.com/rupa/z>.
;;
;; It keeps track of where you have been and how many commands you invoke there,
;; and provides a convenient way to jump to the directories you actually
;; use.
;;
;; `eshell-z.el' and z(1) can work together by sharing the same data file.
;;
;; Usage:
;;
;;  ~ $ z -h
;;  usage: z [-chlrtx] [regex1 regex2 ... regexn]
;;
;;      -c, --current        estrict matches to subdirectories of the current directory
;;      -h, --help           show a brief help message
;;      -l, --list           list only
;;      -r, --rank           match by rank only
;;      -t, --time           match by recent access only
;;      -x, --delete         remove the current directory from the datafile
;;
;;  examples:
;;
;;      z foo         cd to most frecent dir matching foo
;;      z foo bar     cd to most frecent dir matching foo, then bar
;;      z -r foo      cd to highest ranked dir matching foo
;;      z -t foo      cd to most recently accessed dir matching foo
;;      z -l foo      list all dirs matching foo (by frecency)
;;
;; Install:
;;
;; You can install this package from Melpa and Melpa-stable with package.el,
;; that is, ~M-x package-install RET eshell-z RET~. Or you can also install it
;; manually by add eshell-z.el to your `load-path', something like
;;
;;   (add-to-list 'load-path "path/to/eshell-z.el")
;;
;; Setup:
;;
;; To use this package, add following code to your init.el or .emacs
;;
;;   (add-hook 'eshell-mode-hook
;;             (defun my-eshell-mode-hook ()
;;               (require 'eshell-z)))


;;; Code:

(require 'cl-lib)
(require 'eshell)
(require 'em-dirs)
(require 'pcomplete)

(defgroup eshell-z nil
  "Eshell z customizations."
  :group 'eshell)

(defcustom eshell-z-freq-dir-hash-table-file-name
  (or (getenv "_Z_DATA")
      (expand-file-name "~/.z"))
  "If non-nil, name of the file to read/write the freq-dir-hash-table.
If it is nil, the freq-dir-hash-table will not be written to disk."
  :type 'file
  :group 'eshell-z)

(defcustom eshell-z-exclude-dirs '("/tmp/" "~/.emacs.d/elpa")
  "A list of directory trees to exclude."
  :type '(repeat (choice string))
  :group 'eshell-z)

(defcustom eshell-z-change-dir-function
  (lambda (dir)
    (eshell-kill-input)
    (goto-char (point-max))
    (insert
     (format "cd '%s'" dir))
    (eshell-send-input))
  "Function to control how the directory should be changed."
  :type 'function
  :group 'eshell-z)

(defvar eshell-z-freq-dir-hash-table nil
  "The frequent directory that Eshell was in.")

(defun eshell-z--now ()
  "Number of seconds since epoch as a string."
  (format-time-string "%s"))

(defun eshell-z--read-freq-dir-hash-table ()
  "Set `eshell-z-freq-dir-hash-table' from a history file."
  (let ((file eshell-z-freq-dir-hash-table-file-name))
    (cond
     ((or (null file)
          (equal file "")
          (file-directory-p file)
          (not (file-readable-p file)))
      nil)
     (t
      (setq eshell-z-freq-dir-hash-table
            (let ((m (make-hash-table :test 'equal)))
              (mapc (lambda (elt)
                      (let* ((entries (split-string elt "|"))
                             (key (car entries))
                             (rank (string-to-number (cadr entries)))
                             (time (car (last entries))))
                        (puthash key (cons key (list :rank rank :time time))
                                 m)))
                    (with-temp-buffer
                      (let ((jka-compr-compression-info-list nil))
                        (insert-file-contents file))
                      (split-string (buffer-string) "\n" t)))
              m))))))

;; Same as `hash-table-values' of `subr-x.el' in Emacs 24.4+
(defsubst eshell-z--hash-table-values (hash-table)
  "Return a list of values in HASH-TABLE."
  (let ((values '()))
    (maphash (lambda (_k v) (push v values)) hash-table)
    values))

(defun eshell-z--write-freq-dir-hash-table ()
  "Write `eshell-z-freq-dir-hash-table' to a history file."
  (let ((file eshell-z-freq-dir-hash-table-file-name))
    (cond
     ((or (null file)
          (equal file "")
          (null eshell-z-freq-dir-hash-table)
          (zerop (hash-table-count eshell-z-freq-dir-hash-table)))
      nil)
     ((and (file-exists-p file)
           (not (file-directory-p file))
           (not (file-writable-p file)))
      (message "Cannot write freq-dir-hash-table file %s" file))
     (t
      (with-temp-buffer
        (insert
         (mapconcat
          (lambda (val)
            (let ((dir (car val))
                  (rank (number-to-string (plist-get (cdr val) :rank)))
                  (time (plist-get (cdr val) :time)))
              (format "%s|%s|%s" dir rank time)))
          (eshell-z--hash-table-values eshell-z-freq-dir-hash-table) "\n"))
        (insert "\n")
        (let ((jka-compr-compression-info-list nil))
          (write-region (point-min) (point-max) file nil 'silent)))))))

(defun eshell-z--expand-directory-name (directory)
  "Expand and remove ending slash of DIRECTORY."
  (expand-file-name (directory-file-name directory)))

(defun eshell-z--directory-within-p (directory root)
  "Return non-nil if DIRECTORY is a sub-directory of ROOT or ROOT itself."
  (let ((root (eshell-z--expand-directory-name root))
        (directory (eshell-z--expand-directory-name directory)))
    (if (string= root directory)
        t
      (let ((len1 (length root))
            (len2 (length directory)))
        (if (< len2 len1)
            nil
          (if (and (string= root (substring directory 0 len1))
                   (= (aref directory len1) ?/))
              t
            nil))))))

(defun eshell-z--common-root (dirs)
  "Return one directory of DIRS which is the root of all the rest directories, if any."
  (let ((root (car
               (sort
                (copy-sequence dirs)
                (lambda (s1 s2) (< (length s1) (length s2)))))))
    (if (cl-every
         (lambda (elt) (eshell-z--directory-within-p elt root))
         dirs)
        root)))

(defun eshell-z--add ()
  "Add entry."
  (if eshell-z-freq-dir-hash-table-file-name
      (eshell-z--read-freq-dir-hash-table))
  (unless eshell-z-freq-dir-hash-table
    (setq eshell-z-freq-dir-hash-table (make-hash-table :test 'equal)))
  (let ((current-directory (eshell-z--expand-directory-name default-directory)))
    (unless (or
             ;; $HOME isn't worth matching
             (string= current-directory (eshell-z--expand-directory-name "~"))
             ;; don't track excluded directory trees
             (cl-some (lambda (root)
                        (and (stringp root)
                             (eshell-z--directory-within-p
                              current-directory root)))
                      eshell-z-exclude-dirs))
      (let* (
             ;; Remove end slash, z doesn't use it
             (key current-directory)
             (val (gethash key eshell-z-freq-dir-hash-table)))
        (if val
            (puthash key (cons key
                               (list :rank (1+ (plist-get (cdr val) :rank))
                                     :time (eshell-z--now)))
                     eshell-z-freq-dir-hash-table)
          (puthash key (cons key
                             (list :rank 1
                                   :time (eshell-z--now)))
                   eshell-z-freq-dir-hash-table)))))

  (if eshell-z-freq-dir-hash-table-file-name
      (eshell-z--write-freq-dir-hash-table)))

(defvar eshell-z--remove-p nil)

(defun eshell-z--remove ()
  "Remove entry."
  (if eshell-z--remove-p
      (progn
        (unless eshell-z-freq-dir-hash-table
          (setq eshell-z-freq-dir-hash-table (make-hash-table :test 'equal)))
        (remhash (eshell-z--expand-directory-name default-directory)
                 eshell-z-freq-dir-hash-table)
        (if eshell-z-freq-dir-hash-table-file-name
            (eshell-z--write-freq-dir-hash-table))
        (setq eshell-z--remove-p nil))))

;; FIXME: It's much better to provide a minor mode to handle this
(add-hook 'eshell-post-command-hook #'eshell-z--add)
(add-hook 'eshell-post-command-hook #'eshell-z--remove 'append)

(defun eshell-z--frecent (value)
  "Calculate rank of a VALUE of `eshell-z-freq-dir-hash-table'.
Base on frequency and time."
  (let* ((rank (plist-get (cdr value) :rank))
         (time (eshell-z--time value))
         (dx (- (string-to-number (eshell-z--now)) time)))
    (cond ((< dx 3600) (* rank 4))
          ((< dx 86400) (* rank 2))
          ((< dx 604800) (/ rank 2.0))
          (t (/ rank 4.0)))))

(defun eshell-z--rank (value)
  "Get rank of a VALUE of `eshell-z-freq-dir-hash-table'."
  (plist-get (cdr value) :rank))

(defun eshell-z--time (value)
  "Get time of a VALUE of `eshell-z-freq-dir-hash-table'."
  (string-to-number (plist-get (cdr value) :time)))

(defun eshell-z--float-to-string (number)
  "Format number for the list option."
  (let* ((int (truncate number))
         (result (if (= int number) int
                   number)))
    (if (integerp result)
        (format "%-10d" result)
      (format "%-10.1f" result))))

(defun eshell-z--ensure-hash-table ()
  "Ensure `eshell-z-freq-dir-hash-table' is a hash table, not nil."
  (unless eshell-z-freq-dir-hash-table
    (if eshell-z-freq-dir-hash-table-file-name
        (eshell-z--read-freq-dir-hash-table)))

  (unless eshell-z-freq-dir-hash-table
    (setq eshell-z-freq-dir-hash-table (make-hash-table :test 'equal))))

(defun eshell/z (&rest args)
  "cd to frequent directory in eshell."
  (eshell-z--ensure-hash-table)
  (eshell-eval-using-options
   "z" args
   '((?c "current" nil current
         "estrict matches to subdirectories of the current directory")
     (?h "help" nil nil "show a brief help message")
     (?l "list" nil list "list only")
     (?r "rank" nil rank-only "match by rank only")
     (?t "time" nil time-only "match by recent access only")
     (?x "delete" nil delete "remove the current directory from the datafile" )
     :usage "[-chlrtx] [regex1 regex2 ... regexn]"
     :post-usage "examples:

    z foo         cd to most frecent dir matching foo
    z foo bar     cd to most frecent dir matching foo, then bar
    z -r foo      cd to highest ranked dir matching foo
    z -t foo      cd to most recently accessed dir matching foo
    z -l foo      list all dirs matching foo (by frecency)
")
   (if delete
       (setq eshell-z--remove-p t)
     (let ((paths (sort (eshell-z--hash-table-values eshell-z-freq-dir-hash-table)
                        (if rank-only
                            (lambda (elt1 elt2)
                              (> (eshell-z--rank elt1)
                                 (eshell-z--rank elt2)))
                          (if time-only
                              (lambda (elt1 elt2)
                                (> (eshell-z--time elt1)
                                   (eshell-z--time elt2)))
                            (lambda (elt1 elt2)
                              (> (eshell-z--frecent elt1)
                                 (eshell-z--frecent elt2)))))))
           (current-directory (eshell-z--expand-directory-name
                               default-directory)))
       (if list
           (let ((matches
                  (nreverse
                   (cl-remove-if-not
                    (lambda (elt)
                      (string-match
                       (mapconcat #'identity
                                  (if current
                                      (append (list current-directory) args)
                                    args) ".*")
                       (car elt)))
                    paths))))
             (let ((common-root (eshell-z--common-root (mapcar #'car matches))))
               (when common-root
                 (eshell-print (format "%-10s %s\n" "common:" common-root))))
             ;; Display all matches
             (eshell-print
              (mapconcat
               (lambda (elt)
                 (format
                  "%s %s"
                  (eshell-z--float-to-string
                   (if rank-only (eshell-z--rank elt)
                     (if time-only (- (eshell-z--time elt)
                                      (string-to-number (eshell-z--now)))
                       (eshell-z--frecent elt))))
                  (car elt)))
               matches "\n")))
         (if (null args)
             (eshell/cd (list (completing-read "pattern " paths nil t)))
           (let ((path (car args)))
             (if (numberp path)
                 (setq path (number-to-string path)))
             ;; if we hit enter on a completion just go there
             (if (file-accessible-directory-p path)
                 (eshell/cd (list path))
               (let* ((matches
                       (cl-remove-if-not
                        (lambda (elt)
                          (string-match
                           (mapconcat #'identity
                                      (if current
                                          (append (list current-directory) args)
                                        args) ".*")
                           (car elt)))
                        paths))
                      (newdir (or (eshell-z--common-root (mapcar #'car matches))
                                  (caar matches))))
                 (if (and newdir (file-accessible-directory-p newdir))
                     (eshell/cd (list newdir))))))))))
   nil))

(defun pcomplete/z ()
  "Completion for the `z' command."
  (while t
    (if (pcomplete-match "^-" 0)
        (cond
         ;; Long options
         ((pcomplete-match "^--" 0)
          (pcomplete-here* '("--current" "--help" "--list" "--rank" "--time" "--delete")))
         ;; Short options
         (t (pcomplete-opt "chlrtx")))
      (pcomplete-here* (eshell-z--hash-table-values
                        eshell-z-freq-dir-hash-table)))))

(defvar ivy-sort-functions-alist)

;;;###autoload
(defun eshell-z (dir)
  "Switch to eshell and change directory to DIR."
  (interactive
   (list (let ((paths
                (sort (progn
                        (eshell-z--ensure-hash-table)
                        (eshell-z--hash-table-values eshell-z-freq-dir-hash-table))
                      (lambda (elt1 elt2)
                        (> (eshell-z--frecent elt1)
                           (eshell-z--frecent elt2)))))
               (ivy-sort-functions-alist nil))
           (completing-read "pattern " paths nil t))))
  (let ((eshell-buffer (if (eq major-mode 'eshell-mode)
                           (buffer-name)
                         "*eshell*")))
    (if (get-buffer eshell-buffer)
        (switch-to-buffer eshell-buffer)
      (call-interactively 'eshell))
    (unless (get-buffer-process (current-buffer))
      (funcall eshell-z-change-dir-function dir))))

(provide 'eshell-z)
;;; eshell-z.el ends here
