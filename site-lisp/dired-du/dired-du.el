;;; dired-du.el --- Dired with recursive directory sizes -*- lexical-binding: t -*-
;;
;; Filename: dired-du.el
;; Description: Dired with recursive directory sizes
;; Author: Tino Calancha <tino.calancha@gmail.com>
;; Maintainer: Tino Calancha <tino.calancha@gmail.com>
;; Copyright (C) 2016-2017, Tino Calancha, all rights reserved.
;; Created: Wed Mar 23 22:54:00 2016
;; Version: 0.4
;; Package-Requires: ((emacs "24.4") (cl-lib "0.5"))
;; Last-Updated: Sat May 27 18:25:35 JST 2017
;;           By: calancha
;;     Update #: 337
;; Compatibility: GNU Emacs: 24.4
;; Keywords: files, unix, convenience
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Commentary:
;;
;; -- Display the recursive size of directories in Dired --
;;
;; This file defines a minor mode `dired-du-mode' to show
;; the recursive size of directories in Dired buffers.
;; If `du' program is available, then the directory sizes are
;; obtained with it.  Otherwise, the directory sizes are obtained
;; with Lisp.  The former is faster and provide a more precise value.
;; For directories where the user doesn't have read permission,
;; the recursive size is not obtained.
;; Once this mode is enabled, every new Dired buffer displays
;; recursive dir sizes.
;;
;; To enable the mode at start up:
;;
;; 1) Store the file in a directory within `load-path'.
;; 2) Add the following into .emacs file:
;;
;;    (add-hook 'dired-mode-hook #'dired-du-mode)
;;
;; Note that obtaining the recursive size of all the directories
;; in a Dired buffer might be very slow: it may significantly delay
;; the time to display a new Dired buffer.
;; Instead of enabling `dired-du-mode' by default in all Dired buffers
;; you might prefer to use this mode just as an interfaz to
;; the `du' program: you can enable it in the current Dired buffer,
;; and disable it once you have finished checking the used space.
;;
;; -- Number of marked files and their size --
;;
;; In addition, this library adds a command, `dired-du-count-sizes',
;; to count the number of marked files and how much space
;; they use; the command accepts a particular character mark
;; i.e., '*' or all kind of marks i.e, any character other than ?\s.
;;
;; Bugs
;; ====
;; Sometimes the progress reporter shows funny things,
;; for instance, percents > 100.
;;
;;  Internal variables defined here:
;;
;;   `dired-du--user-warned', `dired-du-dir-info',
;;   `dired-du-filesp-subdir-header', `dired-du-find-dired-buffer',
;;   `dired-du-local-subdir-header', `dired-du-mode',
;;   `dired-du-remote-subdir-header'.
;;
;;  Coustom variables defined here:
;;
;;   `dired-du-bind-count-sizes', `dired-du-bind-human-toggle',
;;   `dired-du-bind-mode', `dired-du-on-find-dired-ok',
;;   `dired-du-size-format', `dired-du-update-headers',
;;   `dired-du-used-space-program'.
;;
;;  Macros defined here:
;;
;;   `dired-du-map-over-marks', `dired-du-with-saved-marks'.
;;
;;  Commands defined here:
;;
;;   `dired-du--toggle-human-readable', `dired-du-count-sizes',
;;   `dired-du-drop-all-subdirs', `dired-du-insert-marked-dirs',
;;   `dired-du-on-find-dired-ok-toggle', `dired-du-recompute-dir-size',
;;   `dired-du-update-dir-info'.
;;
;;  Non-interactive functions defined here:
;;
;;   `dired-du--cache-dir-info', `dired-du--change-human-sizes',
;;   `dired-du--count-sizes-1', `dired-du--count-sizes-2',
;;   `dired-du--create-or-check-dir-info', `dired-du--delete-entry',
;;   `dired-du--drop-unexistent-files', `dired-du--file-in-dir-info-p',
;;   `dired-du--find-dired-around', `dired-du--fullname-to-glob-pos',
;;   `dired-du--get-all-files-type',
;;   `dired-du--get-max-gid-and-size-lengths-for-subdir',
;;   `dired-du--get-num-extra-blanks', `dired-du--get-position',
;;   `dired-du--get-position-1', `dired-du--get-value',
;;   `dired-du--global-update-dir-info', `dired-du--initialize',
;;   `dired-du--insert-subdir', `dired-du--local-update-dir-info',
;;   `dired-du--number-as-string-p', `dired-du--read-size-from-buffer',
;;   `dired-du--replace', `dired-du--replace-1',
;;   `dired-du--reset', `dired-du--revert',
;;   `dired-du--subdir-position', `dired-du--update-subdir-header',
;;   `dired-du--update-subdir-header-1', `dired-du-alist-get',
;;   `dired-du-directory-at-current-line-p',
;;   `dired-du-distinguish-one-marked',
;;   `dired-du-filename-relative-to-default-dir',
;;   `dired-du-get-all-directories', `dired-du-get-all-files',
;;   `dired-du-get-all-marks', `dired-du-get-all-non-directories',
;;   `dired-du-get-all-subdir-directories',
;;   `dired-du-get-all-subdir-non-directories', `dired-du-get-file-info',
;;   `dired-du-get-file-size-local', `dired-du-get-file-size-remote',
;;   `dired-du-get-marked-files', `dired-du-get-recursive-dir-size',
;;   `dired-du-get-recursive-dir-size-in-parallel', `dired-du-mark-buffer',
;;   `dired-du-mark-subdir-files', `dired-du-marker-regexp',
;;   `dired-du-run-in-parallel', `dired-du-string-to-number',
;;   `dired-du-unmark-buffer', `dired-du-use-comma-separator'.
;;
;;  Inline functions defined here:
;;
;;   `dired-du-assert-dired-mode', `dired-du-link-number',
;;   `dired-du-modification-time', `dired-du-size'.
;;
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This file is NOT part of GNU Emacs.
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Code:


(require 'cl-lib)
(require 'dired)
(require 'find-dired)
(autoload 'dired-subdir-min "dired-aux")

(defgroup dired-du nil
  "Dired with recursive size dir."
  :prefix "dired-du-"
  :group 'dired-du)

(defvar dired-du-dir-info nil
  "Alist of cached (DIRNAME . DIR-INFO) in Dired buffer.
DIRNAME is a subdirectory in the DIRED buffer.

DIR-INFO is one alist with information about each directory
in DIRNAME obtained with `dired-du-get-file-info'.  Each
element is an alist:
\(NAME ((nlink . NLINK) (size . SIZE) (time . TIME))).

The size of the directories is the recursive size obtained with
`dired-du-used-space-program'.  The size of the entries
'.' and '..' is not changed.")
(make-variable-buffer-local 'dired-du-dir-info)

(defvar dired-du-mode nil
  "Variable with the status of the mode.
If this variable evaluates non-nil, then show recursive size
for directories in the Dired buffer.  This variable is also used
as default value for INCLUDE-DIRS in `dired-du-count-sizes'.")
(make-variable-buffer-local 'dired-du-mode)

(put 'dired-du-mode 'permanent-local t)

(defcustom dired-du-used-space-program
  (purecopy (let ((opts (if (string-prefix-p "gnu" (symbol-name system-type))
                            "-sb"
                          "-sk"))) ; -k overestimate used space\
                                   ; for files w/ size < 1024.
              (cond ((executable-find "du") (list "du" opts))
                    ((file-executable-p "/usr/sbin/du")
                     (list "/usr/sbin/du" opts))
                    ((file-executable-p "/etc/du") (list "/etc/du" opts)))))
  "Program and its options to get recursively the total size of a directory.
We assume the output has the format of `du'.
A value of nil disables this feature."
  :type '(choice (const :tag "Unset" nil)
                 (list (string :tag "Program")
                       (repeat :tag "Options"
                               :inline t
                               (string :format "%v"))))
  :group 'dired-du)

(defvar dired-du--user-warned (and dired-du-used-space-program t)
  "Nil if the user must be warned about \
`dired-du-used-space-program' being nil.")

(defcustom dired-du-size-format nil
  "Set the format for file sizes.
If equals t, then `dired-du-count-sizes' displays file
sizes using `file-size-human-readable'.

If equals 'comma, then `dired-du-count-sizes' displays
file sizes using thousands comma separator.

Otherwise display file sizes in default numeric format."
  :type '(choice
          (const :tag "Use default numeric format" nil)
          (const :tag "Use human readable string" t)
          (const :tag "Use thousands comma separator" 'comma))
  :group 'dired-du)

(defcustom dired-du-on-find-dired-ok nil
  "If Non-nil show recursive dir sizes in `find-dired'.
The format to display the file sizes is control by
`dired-du-size-format'."
  :type 'boolean :group 'dired-du)

(defvar dired-du-find-dired-buffer nil
  "Non-nil if current buffer is a `find-dired' buffer.
When `dired-du-on-find-dired-ok' evaluates non-nil, then this
buffer show recursive dir sizes with format according with
`dired-du-size-format' if the mode is enabled.")
(make-variable-buffer-local 'dired-du-find-dired-buffer)

(defcustom dired-du-update-headers nil
  "If Non-nil, update the subdir headers.
The total used space shown contains the recursive size of the directories."
  :type 'boolean :group 'dired-du)

(defvar dired-du-local-subdir-header
  "^  total used in directory \\([,.0-9]+[BkKMGTPEZY]?\\) \
available \\([,.0-9]+[BkKMGTPEZY]?\\)"
  "Regexp matching a subdir header in a Dired buffer in the local host.")

(defvar dired-du-remote-subdir-header
  "^  total \\([,.0-9]+[BkKMGTPEZY]?\\)"
  "Regexp matching a subdir header in a Dired buffer visiting a remote host.")

(defvar dired-du-filesp-subdir-header
  "^ *files \\([,0-9]+\\)/\\([,0-9]+\\) space used \
\\([,.0-9]+[BkKMGTPEZY]?\\) available \\([,.0-9]+[BkKMGTPEZY]?\\)"
  "Regexp matching a subdir header in a Dired buffer using lib `files+'.")



(defcustom dired-du-bind-mode t
  "Non-nil means bind `dired-du-mode' to C-x M-r in `dired-mode-map', otherwise do not."
  :type 'boolean
  :set (lambda (sym val)
         (let ((map dired-mode-map))
           (when (set sym val)
             (define-key map (kbd "C-x M-r") 'dired-du-mode))))
  :group 'dired-keys)

(defcustom dired-du-bind-human-toggle t
  "Non-nil means bind `dired-du--toggle-human-readable' to C-x C-h in `dired-mode-map', otherwise do not."
  :type 'boolean
  :set (lambda (sym val)
         (let ((map dired-mode-map))
           (when (set sym val)
             (define-key map (kbd "C-x C-h") 'dired-du--toggle-human-readable))))
  :group 'dired-keys)

(defcustom dired-du-bind-count-sizes t
  "Non-nil means bind `dired-du-count-sizes' to *N in `dired-mode-map', otherwise do not."
  :type 'boolean
  :set (lambda (sym val)
         (let ((map dired-mode-map))
           (when (set sym val)
             (define-key map "*N" 'dired-du-count-sizes))))
  :group 'dired-keys)

;;; Macros.

(defmacro dired-du-with-saved-marks (&rest body)
  "Save alist of files and their marks; execute BODY; restore the marks.
The value returned is the value of the last form in BODY."
  (declare (indent 0) (debug t))
  (let ((saved-marks (make-symbol "saved-marks"))
        (new-marks   (make-symbol "new-marks")))
    `(let ((,saved-marks (dired-remember-marks (point-min) (point-max))))
       (unwind-protect
           (progn ,@body)
         (let ((,new-marks (dired-remember-marks (point-min) (point-max))))
           (unless (equal ,saved-marks ,new-marks)
             (dired-du-unmark-buffer)
             (let ((inhibit-read-only t))
               (dired-mark-remembered ,saved-marks))))))))

;; As `dired-map-over-marks' but with additional arg ALL-MARKS.
(defmacro dired-du-map-over-marks (body arg &optional show-progress
                                        distinguish-one-marked
                                        marker-char all-marks)
  "Eval BODY with point on each marked line.  Return a list of BODY's results.
If no marked file could be found, execute BODY on the current
line.  ARG, if non-nil, specifies the files to use instead of the
marked files.

If ARG is an integer, use the next ARG (or previous -ARG, if
ARG<0) files.  In that case, point is dragged along.  This is so
that commands on the next ARG (instead of the marked) files can
be chained easily.
For any other non-nil value of ARG, use the current file.

If optional third arg SHOW-PROGRESS evaluates to non-nil,
redisplay the dired buffer after each file is processed.

No guarantee is made about the position on the marked line.
BODY must ensure this itself if it depends on this.

Search starts at the beginning of the buffer, thus the car of the
list corresponds to the line nearest to the buffer's bottom.
This is also true for (positive and negative) integer values of
ARG.

BODY should not be too long as it is expanded four times.

If DISTINGUISH-ONE-MARKED is non-nil, then if we find just one
marked file, return (t FILENAME) instead of (FILENAME).

If MARKER-CHAR is non-nil, then it is the mark
character to search.  Otherwise use `dired-marker-char'.

If ALL-MARKS is non-nil, accept all mark characters.  Otherwise use
just MARKER-CHAR."
  ;;
  ;;Warning: BODY must not add new lines before point - this may cause an
  ;;endless loop.
  ;;This warning should not apply any longer, sk  2-Sep-1991 14:10.
  `(prog1
       (let ((inhibit-read-only t) case-fold-search found results)
         (if ,arg
             (if (integerp ,arg)
                 (progn ;; no save-excursion, want to move point.
                   (dired-repeat-over-lines
                    ,arg
                    (function (lambda ()
                                (if ,show-progress (sit-for 0))
                                (setq results (cons ,body results)))))
                   (if (< ,arg 0)
                       (nreverse results)
                     results))
               ;; non-nil, non-integer ARG means use current file:
               (list ,body))
           (let ((regexp (dired-du-marker-regexp ,marker-char ,all-marks))
                 next-position)
             (save-excursion
               (goto-char (point-min))
               ;; remember position of next marked file before BODY
               ;; can insert lines before the just found file,
               ;; confusing us by finding the same marked file again
               ;; and again and...
               (setq next-position (and (re-search-forward regexp nil t)
                                        (point-marker))
                     found (not (null next-position)))
               (while next-position
                 (goto-char next-position)
                 (if ,show-progress (sit-for 0))
                 (setq results (cons ,body results))
                 ;; move after last match
                 (goto-char next-position)
                 (forward-line 1)
                 (set-marker next-position nil)
                 (setq next-position (and (re-search-forward regexp nil t)
                                          (point-marker)))))
             (if (and ,distinguish-one-marked (= (length results) 1))
                 (setq results (cons t results)))
             (if found
                 results
               (list ,body)))))
     ;; save-excursion loses, again
     (dired-move-to-filename)))


;;; Advice `find-dired'.
;;  Set buffer local variable `dired-du-find-dired-buffer' non-nil
;;  on the output buffer of `find-dired' commands.
;;  Substitute recursive dir sizes in those buffers only if
;;  `dired-du-on-find-dired-ok' non-nil.

(defun dired-du--find-dired-around (orig-fun &rest args)
  "Advice function for `find-dired-sentinel'.
Set `dired-du-find-dired-buffer' non-nil in current buffer
and run `dired-after-readin-hook'.
ORIG-FUN is the original `find-dired-sentinel'.
ARGS are the arguments for `find-dired-sentinel'."
  (setq dired-du-find-dired-buffer t)
  (let ((res (apply orig-fun args)))
    (unless (featurep 'find-dired+)
      (run-hooks 'dired-after-readin-hook))
    res))


;; As `dired-du-get-marked-files' but with additional arg ALL-MARKS.
(defun dired-du-get-marked-files (&optional localp arg filter
                                            distinguish-one-marked
                                            marker-char all-marks)
  "Return the marked files names as a list of strings.
The list is in the same order as the buffer, that is, the car is the
  first marked file.
Values returned are normally absolute file names.
Optional arg LOCALP as in `dired-get-filename'.
Optional second argument ARG, if non-nil, specifies files near
 point instead of marked files.  It usually comes from the prefix
 argument.
  If ARG is an integer, use the next ARG files.
  If ARG is any other non-nil value, return the current file name.
  If no files are marked, and ARG is nil, also return the current file name.
Optional third argument FILTER, if non-nil, is a function to select
  some of the files--those for which (funcall FILTER FILENAME) is non-nil.

If DISTINGUISH-ONE-MARKED is non-nil, then if we find just one marked file,
return (t FILENAME) instead of (FILENAME).
Don't use that together with FILTER.

Optional arg MARKER-CHAR, if non-nil, then it is the mark
character to search.  Otherwise use `dired-marker-char'.

Optional arg ALL-MARKS, if non-nil, then accept all mark characters.
Otherwise use just MARKER-CHAR."
  (let ((all-of-them
         (save-excursion
           (delq nil (dired-du-map-over-marks
                      (dired-get-filename localp 'no-error-if-not-filep)
                      arg nil distinguish-one-marked marker-char all-marks))))
        result)
    (when (equal all-of-them '(t))
      (setq all-of-them nil))
    (if (not filter)
        (if (and distinguish-one-marked (eq (car all-of-them) t))
            all-of-them
          (nreverse all-of-them))
      (dolist (file all-of-them)
        (if (funcall filter file)
            (push file result)))
      result)))

;; As `dired-marker-regexp' but with optional args. MARKER-CHAR and ALL-MARKS.
(defun dired-du-marker-regexp (&optional marker-char all-marks)
  "Return a regexp matching `dired-marker-char' at the beginning of line.
If MARKER-CHAR evaluates non-nil, then the regexp matches MARKER-CHAR
instead of `dired-marker-char'.
If optional argument ALL-MARKS evaluates to non-nil, then the regexp
matches any mark character."
  (if all-marks
      dired-re-mark
    (concat "^"
            (regexp-quote
             (char-to-string (or marker-char dired-marker-char))))))

(defsubst dired-du-link-number (attributes)
  "Return the number of links in ATTRIBUTES returned by `file-attributes'."
  (nth 1 attributes))

(defsubst dired-du-modification-time (attributes)
  "The modification time in ATTRIBUTES returned by `file-attributes'.
This is the time of the last change to the file's contents, and
is a list of integers (HIGH LOW USEC PSEC) in the same style
as (current-time)."
  (nth 5 attributes))

(defsubst dired-du-size (attributes)
  "The size (in bytes) in ATTRIBUTES returned by `file-attributes'.
This is a floating point number if the size is too large for an integer."
  (nth 7 attributes))


;;; Toggle on `dired-du-on-find-dired-ok'.

(defun dired-du-on-find-dired-ok-toggle ()
  "Toggle on `dired-du-on-find-dired-ok'."
  (interactive)
  (setq dired-du-on-find-dired-ok
        (not dired-du-on-find-dired-ok))
  (if dired-du-on-find-dired-ok
      (message "Enabled `dired-du-on-find-dired-ok'")
    (message "Disabled `dired-du-on-find-dired-ok'"))
  (when dired-du-find-dired-buffer
    (cond ((and dired-du-on-find-dired-ok
                dired-du-mode)
           (dired-du--replace))
          ((not dired-du-on-find-dired-ok)
           (revert-buffer)))))


;;; Handle sizes with thousands comma separator.
(defun dired-du-string-to-number (str)
  "Like `string-to-number' but recognize a trailing unit prefix.
For example, 2K is expanded to 2048.0.  The caller should make
sure that a trailing letter in STR is one of BKkMGTPEZY.
It handles thousands comma separator."
  (let* ((str-new (replace-regexp-in-string "," "" str))
         (val (string-to-number str-new))
         (u (unless (zerop val)
              (aref str-new (1- (length str-new))))))
    (when (and u (> u ?9))
      (when (= u ?k)
        (setq u ?K))
      (let ((units '(?B ?K ?M ?G ?T ?P ?E ?Z ?Y)))
        (while (and units (/= (pop units) u))
          (setq val (* 1024.0 val)))))
    val))

(defun dired-du-use-comma-separator (num)
  "Return number NUM as an string using comma separator."
  (replace-regexp-in-string
   "^," ""
   (apply #'string
          (reverse
           (string-to-list
            (replace-regexp-in-string
             ",\\." "."
             (replace-regexp-in-string
              "\\([0-9]\\{3\\}\\)" "\\1,"
              (apply #'string
                     (reverse
                      (string-to-list
                       (replace-regexp-in-string
                        "\\.0$" ""
                        (number-to-string
                         num))))))))))))


;;; Functions to obtain recursive dir size.
(defsubst dired-du-assert-dired-mode ()
  "Ensure current buffer is in `dired-mode'."
  (cl-assert (derived-mode-p 'dired-mode)))

(defun dired-du-directory-at-current-line-p ()
  "Return non-nil if there is a directory at current line in the Dired buffer."
  (dired-du-assert-dired-mode)
  (save-excursion
    (goto-char (line-beginning-position)) (looking-at-p dired-re-dir)))

(defun dired-du-filename-relative-to-default-dir (&optional file)
  "Return the filename relative to default directory of a file.
Optional arg FILE, if non-nil, then is the file relative or fullname.
Otherwise use the file at the current line in the Dired buffer."
  (if (not file)
      (dired-get-filename t t)
    (let ((basename (file-name-nondirectory file))
          (relname  (file-relative-name file)))
      (cond ((member basename '("." ".."))
             (let ((dir (file-name-directory file)))
               (cond (dir
                      (concat
                       (file-name-as-directory
                        (file-name-nondirectory
                         (directory-file-name
                          dir))) basename))
                     (t
                      file))))
            (t
             relname)))))

(defun dired-du--read-size-from-buffer ()
  "Return displayed size for file at current line as a decimal number."
  (save-excursion
    (when (dired-move-to-filename)
      (re-search-backward
       directory-listing-before-filename-regexp)
      (let ((pos (progn (skip-chars-forward "^ \t") (point))))
        (skip-chars-backward "^ \t")
        (dired-du-string-to-number
         (buffer-substring-no-properties (point) pos))))))

(defun dired-du-get-recursive-dir-size ()
  "Return recursive directory size for dir at current line.
If there is not a directory in the current line return nil."
  (dired-du-assert-dired-mode)
  (when (dired-du-directory-at-current-line-p)
    ;; remote files need relative name.
    (let ((dir-rel (dired-get-filename t 'noerror))
          (size 0)
          (dired-buffer (current-buffer)))
      (with-temp-buffer
        (if dired-du-used-space-program
            (process-file (car dired-du-used-space-program)
                          nil t nil
                          (cadr dired-du-used-space-program)
                          dir-rel)
          ;; `du' not available: estimate the size with Lisp as
          ;; the size of all the regular files under this dir.  This is
          ;; an underestimation, but it's OK for most of the cases.
          (require 'find-lisp)
          (with-no-warnings
            (let* ((files (ignore-errors ; Ignore permission denied errors.
                            (find-lisp-find-files dir-rel "")))
                   (tmp (if (null files)
                            (with-current-buffer dired-buffer
                              (dired-du--read-size-from-buffer))
                          (apply #'+ (mapcar
                                      (lambda (f)
                                        (dired-du-size
                                         (file-attributes f)))
                                      files)))))
              (insert (format "%d" tmp)))))
        (goto-char 1)
        (while (re-search-forward "^[0-9]+" nil t)
          (setq size (+ size (string-to-number (match-string 0)))))) size)))

(defun dired-du-run-in-parallel (command out-buf)
  "Run COMMAND for several files in parallel.
Like `dired-run-shell-command' but adding optional arg OUT-BUF and not
displaying the buffer associated to the shell process."
  ;; prevent showing temp buffer.
  (let ((display-buffer-alist (cons '(" \\*temp\\*"
                                      (display-buffer-no-window)
                                      (allow-no-window . t))
                                    display-buffer-alist))
        (handler
         (find-file-name-handler (directory-file-name default-directory)
                                 'shell-command)))
    (if handler (apply handler 'shell-command (list command out-buf))
      (shell-command command out-buf))
    ;; change process sentinel to avoid showing a large command in the echo area.
    (let ((sentinel (lambda (process signal)
                      (when (memq (process-status process) '(exit signal))
                        (message "collection of recursive dir size: %s."
                                 (substring signal 0 -1))
                        (message nil)))))
      (set-process-sentinel (get-buffer-process out-buf) sentinel)))
  ;; return nil for sake of nconc in dired-bunch-files.
  nil)

(defun dired-du-get-recursive-dir-size-in-parallel (dirs)
  "Get recursive directory size for DIRS.
DIRS is a list of directories.
The return value is an alist (DIRNAME . SIZE)."
  (dired-du-assert-dired-mode)
  (save-excursion
    (let ((dirs-rel (mapcar 'file-relative-name dirs))
          (command  (format "%s %s&" (car dired-du-used-space-program)
                            (cadr dired-du-used-space-program)))
          (prep (make-progress-reporter
                 "Dired-Du collecting recursive dir sizes, please wait ..."
                 0 (length dirs)))
          result)
      (dired-bunch-files
       (- 10000 (length command))
       (function (lambda (&rest files)
                   (with-temp-buffer
                     (let ((buff (current-buffer)))
                       (dired-du-run-in-parallel
                        (dired-shell-stuff-it
                         command files 'on-each) buff)
                       (let ((proc (get-buffer-process buff)))
                         ;; wait until all files processed.
                         (while (eq (process-status proc) 'run)
                           (let ((completed (count-lines (point-min)
                                                         (point-max)))
                                 (old 0))
                             (unless (= completed old)
                               (progress-reporter-force-update
                                prep
                                completed
                                (format
                                 "Dired-Du collecting dir sizes ...(%d/%d) "
                                 completed
                                 (length dirs)))
                               (setq old completed))
                             (setq completed (count-lines (point-min)
                                                          (point-max)))
                             (sleep-for 1))))
                       ;; collect dir sizes.
                       (goto-char 1)
                       (while (re-search-forward "^[0-9]+" nil t)
                         (let ((size      (string-to-number (match-string 0)))
                               (dir-name  (progn
                                            (skip-chars-forward " \t")
                                            (buffer-substring-no-properties
                                             (point)
                                             (line-end-position)))))
                           (push (cons dir-name size) result)))))))
       nil
       dirs-rel) result)))


;;; Query functions for `dired-du-dir-info'.

(defun dired-du--get-position-1 (name &optional dir-info)
  "Return position of NAME in DIR-INFO."
  ;; (unless dir-info (setq dir-info (cdar dired-du-dir-info)))
  (let ((elt (cond ((hash-table-p dir-info)
                    (gethash name dir-info))
                   (t (assoc name dir-info)))))
    (when elt
      (cl-position elt dir-info :test #'equal))))

(defun dired-du--get-position (name &optional dir-info glob-pos)
  "Return position of NAME in DIR-INFO.
Optional arg DIR-INFO, if non-nil,  is an alist with same structure as
`dired-du-dir-info'.  Otherwise defaults to `dired-du-dir-info'.

Optional arg GLOB-POS, if non-nil, is the global position
in DIR-INFO of the alist containing (KEY . VALUE).  Otherwise, it
is obtained inside this function.

Return value is a cons (GLOB-POS . REL-POS);  REL-POS is the
position of NAME in the alist.

If NAME is not found in DIR-INFO return nil."
  (unless dir-info
    (setq dir-info (dired-du--create-or-check-dir-info)))
  (let ((info (cl-remove-if-not (lambda (x) (cdr-safe x)) dir-info))
        res)
    (when info
      (cl-labels ((fn (v alist gpos)
                      (let ((rpos (dired-du--get-position-1 v (cdr alist))))
                        (when rpos
                          (setq res
                                (cons
                                 (or gpos
                                     (dired-du--subdir-position (car alist)))
                                 rpos))))))
                 (if glob-pos
                     (let ((local-info (nth glob-pos dir-info)))
                       (if (not (consp local-info))
                           (setq res nil)
                         (fn name local-info glob-pos)))
                   (catch 'found ; Loop on info.
                     (dolist (local-info info)
                       (when (fn name local-info nil)
                         (throw 'found nil))))))) res))

(defun dired-du-alist-get (key alist &optional default)
  "Return the value associated with KEY in ALIST, using `assq'.
If KEY is not found in ALIST, return DEFAULT."
  (let ((x (assq key alist)))
    (if x (cdr x) default)))

(defun dired-du--get-value (name key &optional dir-info glob-pos)
  "Return for file NAME its VALUE in (KEY . VALUE).
KEY is a symbol.
Optional arg DIR-INFO, if non-nil,  is an alist with same structure as
`dired-du-dir-info'.  Otherwise defaults to
`dired-du-dir-info'.

Optional arg GLOB-POS, if non-nil, is the global position
in DIR-INFO of the alist containing (KEY . VALUE).  Otherwise, it
is obtained inside this function.

If name is not found in DIR-INFO return nil."
  (unless dir-info
    (setq dir-info dired-du-dir-info))
  (let ((pos (dired-du--get-position name dir-info glob-pos))
        info value)
    (when pos
      (let ((global-pos (car pos))
            (rel-pos    (cdr pos)))
        (setq info  (cdr (nth global-pos dir-info))
              value (dired-du-alist-get key (nth rel-pos info)))))
    value))

(defun dired-du--subdir-position (subdir)
  "Return the position of SUBDIR in `dired-du-dir-info'.
SUBDIR should be a fullname.
If SUBDIR is not found return nil."
  (dired-du--create-or-check-dir-info)
  (cl-position-if (lambda (x)
                    (let ((dir (car-safe x)))
                      (and (stringp dir)
                           (string= dir subdir))))
                  dired-du-dir-info))

(defun dired-du--fullname-to-glob-pos (dir)
  "Return the global index of DIR in `dired-du-dir-info'."
  (let ((rel-name (file-relative-name dir)))
    (car (dired-du--get-position rel-name))))

(defun dired-du--file-in-dir-info-p (file &optional dir-info)
  "Return non-nil if FILE is included in DIR-INFO."
  (let ((relname  (dired-du-filename-relative-to-default-dir file))
        (glob-pos (dired-du--fullname-to-glob-pos file)))
    (dired-du--get-position relname dir-info glob-pos)))

(defun dired-du--create-or-check-dir-info (&optional keep-drop-dirs)
  "Initialize `dired-du-dir-info' and return it.
Intial value is just a list with the subdir names included in the
Dired buffer.  If there are subdirs not included in `dired-du-dir-info'
then they are added.

Optional arg KEEP-DROP-DIRS, when evaluates non-nil, keep the information of
subdirectories shown before.  Otherwise that information is discarded for
performance reasons."
  (let* ((subdir-alist  dired-subdir-alist)
         (num-subdirs  (length subdir-alist)))
    (cond ((not dired-du-dir-info)
           (setq dired-du-dir-info
                 (mapcar (lambda (x) (cons (car x) nil)) subdir-alist)))
          ((> num-subdirs ; add missing subdirs.
              (length dired-du-dir-info))
           (let ((subdirs (mapcar 'car subdir-alist)))
             (dolist (dir subdirs)
               (unless (assoc-string dir dired-du-dir-info)
                 (push (list dir) dired-du-dir-info)))))
          ((and (< num-subdirs ; drop subdirs not shown anymore.
                   (length dired-du-dir-info))
                (not keep-drop-dirs))
           (setq dired-du-dir-info
                 (cl-delete-if
                  (lambda (x)
                    (let ((old (car-safe x)))
                      (and (stringp old)
                           (not (assoc-string old subdir-alist)))))
                  dired-du-dir-info))))
    dired-du-dir-info))


;;; Get info for file at current line.

(defun dired-du-get-file-info (&optional glob-pos dir-dots dir-size)
  "Get file info for file at current line in dired buffer.
Optional arg GLOB-POS, when non-nil, is the position in
`dired-du-dir-info' to look up.  Otherwise, look in all positions.

Optional arg DIR-DOTS, if non-nil, then obtain the recursive dir size
for '.' and '..' as well.  Otherwise obtain their size from the buffer.

Optional arg DIR-SIZE, if non-nil, is the recursive dir size for the
the file in the current dired line."
  ;; code for this function is borrowed from dired-x.el::dired-mark-sexp
  (let ((remote-dir (file-remote-p default-directory))
        nlink gid size time time-mod
        name time-cache size-cache nlink-cache change isdir)
    (save-excursion
      (dired-du--create-or-check-dir-info)
      (if (dired-move-to-filename)
          (let ((mode-len 10)
                (filename  (and (null remote-dir)
                                (dired-get-filename 'local 'noerror)))
                ;; When the buffer is remote, all information but the recursize
                ;; dir size, is collected from the buffer for performance
                ;; reasons; this may cause a lost in the precision
                ;; if a file has time-cache equals to its modification time.
                ;; For instance, if the file has a cached time "mar 19 12:46",
                ;; and it changes its size before "mar 19 12:47", then neither
                ;; the time-cache nor the size-cache are updated.
                ;; For local files the file information is collected with
                ;; `file-attributes',so in the previous example file would
                ;; update its size on the buffer.
                (attributes (and (null remote-dir)
                                 (file-attributes
                                  (dired-get-filename nil 'noerror) 'string)))
                (dired-re-inode-size "\\=\\s *\\([0-9]+\\s +\\)?\
\\(?:\\([0-9]+\\(?:\\.[0-9]*\\)?[BkKMGTPEZY]?\\)? ?\\)"))
            (beginning-of-line)
            (forward-char 2)
            (re-search-forward dired-re-inode-size nil t)
            (setq isdir (dired-du-directory-at-current-line-p))
            (cond (remote-dir ; collect info from buffer
                   ;; xxx might be a size not followed by a unit prefix.
                   ;; we could set s to inode if it were otherwise nil,
                   ;; with a similar reasoning as below for setting gid to uid,
                   ;; but it would be even more whimsical.
                   ;; (setq inode (when (match-string 1)
                   ;;               (string-to-number (match-string 1)))
                   (setq nlink
                         (progn
                           (forward-char mode-len)
                           ;; skip any extended attributes marker ("." or "+").
                           (or (looking-at-p " ")
                               (forward-char 1))
                           (read (current-buffer)))
                         name
                         (progn
                           (dired-move-to-filename)
                           (buffer-substring-no-properties
                            (point)
                            (or
                             (dired-move-to-end-of-filename t)
                             (point)))))
                   ;; the name stored is the relative name to default-directory.
                                        ; In non-remote case, its returned by
                   (let* ((basename (file-name-nondirectory name))
                          (fullname
                           (if (member basename '("." ".."))
                               (concat
                                (file-name-as-directory
                                 (dired-current-directory))
                                basename)
                             (expand-file-name name default-directory))))
                     (setq name
                           (dired-du-filename-relative-to-default-dir
                            fullname))))
                  (t
                   ;; collect info from file system
                   ;; gid read from buffer: user may disable gid display;
                   ;; we need the the string in the left of the size,
                   ;; whatever it is (uid/gid).
                   (setq nlink      (dired-du-link-number attributes)
                         time-mod   (dired-du-modification-time attributes)
                         name       filename)))
            (setq time-cache  (dired-du--get-value name 'time nil glob-pos)
                  size-cache  (dired-du--get-value name 'size nil glob-pos)
                  nlink-cache (dired-du--get-value name 'nlink nil glob-pos))
            (dired-move-to-filename)
            (save-excursion
              (setq time
                    (cond (remote-dir
                           ;; the regexp below tries to match from the last
                           ;; digit of the size field through a space after
                           ;; the date.  Also, dates may have different
                           ;; formats depending on file age, so the date
                           ;; column need not be aligned to the right.
                           (buffer-substring-no-properties
                            (save-excursion
                              (skip-chars-backward " \t")
                              (point))
                            (progn
                              (re-search-backward
                               directory-listing-before-filename-regexp)
                              (skip-chars-forward "^ \t")
                              (1+ (point)))))
                          (t ; local file
                           (progn
                             (re-search-backward
                              directory-listing-before-filename-regexp)
                             (skip-chars-forward "^ \t")
                             (format "%s" time-mod))))
                    size (let ((size-on-buffer
                                (dired-du-string-to-number
                                 (buffer-substring-no-properties
                                  (point)
                                  (progn
                                    (skip-chars-backward "^ \t")
                                    (point))))))
                           (cond ((member
                                   (file-name-nondirectory name) '("." ".."))
                                  (let* ((size-file     size-on-buffer)
                                         (size-human
                                          (file-size-human-readable size-file))
                                         (size-no-human
                                          (format "%d" size-file))
                                         (size-comma
                                          (dired-du-use-comma-separator
                                           size-file))
                                         (fn (lambda (human default size-comma)
                                               (cond ((eq t dired-du-size-format)
                                                      human)
                                                     ((null dired-du-size-format)
                                                      default)
                                                     (t
                                                      size-comma)))))
                                    (cond ((null dir-dots)
                                           (funcall fn size-human size-no-human
                                                    size-comma))
                                          (t ; obtain recursive size also\
					                         ; for '.' and '..'.
                                           (let* ((size-dir
                                                   (or dir-size
                                                       (dired-du-get-recursive-dir-size)))
                                                  (size-human
                                                   (file-size-human-readable
                                                    size-dir))
                                                  (size-no-human
                                                   (format "%d" size-dir))
                                                  (size-comma
                                                   (dired-du-use-comma-separator
                                                    size-dir)))
                                             (funcall fn size-human
                                                      size-no-human
                                                      size-comma))))))
                                 ((and dired-du-mode
                                       (dired-du-directory-at-current-line-p))
                                  (let* ((size-recur
                                          (or (and (string= time time-cache)
                                                   (= nlink nlink-cache)
                                                   (dired-du-string-to-number
                                                    size-cache))
                                              (or
                                               dir-size
                                               (dired-du-get-recursive-dir-size))))
                                         (recursive-size
                                          (cond ((eq t dired-du-size-format)
                                                 (file-size-human-readable
                                                  size-recur))
                                                ((null dired-du-size-format)
                                                 (format "%d" size-recur))
                                                (t
                                                 (dired-du-use-comma-separator
                                                  size-recur)))))
                                    recursive-size))
                                 (t
                                  (let* ((size-file
                                          (progn
                                            (dired-du-string-to-number
                                             (format "%d" size-on-buffer))))
                                         (size-human
                                          (file-size-human-readable size-file))
                                         (size-no-human
                                          (format "%d" size-file))
                                         (size-comma
                                          (dired-du-use-comma-separator
                                           size-file)))
                                    (cond ((eq t dired-du-size-format)
                                           size-human)
                                          ((null dired-du-size-format)
                                           size-no-human)
                                          (t
                                           size-comma))))))
                    gid (buffer-substring-no-properties
                         (progn
                           (skip-chars-backward " \t")
                           (point))
                         (progn
                           (skip-chars-backward "^ \t")
                           (point)))
                    ;; set update change flag.
                    change (cond ((and (dired-du-directory-at-current-line-p)
                                       (not (string= size size-cache)))
                                  'change-size)
                                 (t
                                  (or
                                   (not (string= size size-cache))
                                   (not (= nlink nlink-cache))
                                   (not (string= time time-cache)))))))
            (cons name
                  (list
                   (cons 'nlink nlink)
                   (cons 'gid gid)
                   (cons 'size size)
                   (cons 'time time)
                   (cons 'isdir isdir)
                   (cons 'change change))))
        nil))))

(defun dired-du-get-file-size-local ()
  "Return size for non-directory at current line."
  (dired-du-assert-dired-mode)
  (unless (dired-du-directory-at-current-line-p)
    (dired-du-size (file-attributes (dired-get-filename)))))

(defun dired-du-get-file-size-remote ()
  "Return size for file at current line.
The return value is the size shown in the Dired buffer.
To return the recursive size of directories use
`dired-du-get-recursive-dir-size'."
  (dired-du-assert-dired-mode)
  ;; (unless (dired-du-directory-at-current-line-p)
  (save-excursion
    (dired-move-to-filename)
    (re-search-backward directory-listing-before-filename-regexp)
    (skip-chars-forward "^ \t")
    (backward-char 1)
    (dired-du-string-to-number
     (buffer-substring-no-properties
      (1+ (point))
      (save-excursion
        (skip-chars-backward "^ \t")
        (point))))));)


;;; Mark/Unmark subdirs or whole buffer (including "." and "..").

(defun dired-du-mark-subdir-files (&optional mark must-exist)
  "Mark all files in current subdirectory.
Optional arg MARK, if non-nil, then is the character mark used.
Otherwise use `dired-marker-char'.
Optional arg MUST-EXIST, if non-nil, hide non-existant files.

Directories '.' and '..' are also marked."
  (save-restriction
    (narrow-to-region (dired-subdir-min)
                      (dired-subdir-max))
    (dired-du-mark-buffer mark must-exist)))

(defun dired-du-mark-buffer (&optional mark must-exist)
  "Mark all files in the Dired buffer.
Optional arg MARK, if non-nil, then is the character mark used.
Otherwise use `dired-marker-char'.
Optional arg MUST-EXIST, if non-nil, hide non-existant files.

Directories '.' and '..' are also marked."
  (let ((dired-marker-char (or mark dired-marker-char)))
    (save-excursion
      (dired-mark-files-in-region (point-min) (point-max))
      ;; Handle '.' and '..'
      (let ((inhibit-read-only t))
        (goto-char (point-min))
        (while (re-search-forward dired-re-dot (point-max) t)
          (goto-char (line-beginning-position))
          (delete-char 1)
          (insert dired-marker-char))))
    (when (and must-exist (not (eq dired-marker-char ?\s)))
      (dired-du-map-over-marks
       (let ((file (dired-get-filename t t))
             (inhibit-read-only t))
         (when (and file (not (file-exists-p file)))
           (delete-region (line-beginning-position)
                          (progn (forward-line 1) (point)))))
       nil) nil)))

(defun dired-du-unmark-buffer (&optional mark)
  "Remove MARK from all files in the Dired buffer.
If MARK evaluates nil, remove any mark.

Like `dired-du-unmark-buffer' but don't print
any message in the echo area."
  (cond ((null mark)
         (dired-du-mark-buffer ?\s))
        (t
         (let ((start  (point-min))
               (end    (point-max))
               (regexp (dired-du-marker-regexp mark))
               (inhibit-read-only t))
           (save-excursion
             (goto-char start)
             (while (re-search-forward regexp end t)
               (goto-char (line-beginning-position))
               (delete-char 1)
               (insert-char ?\s)))))))


;;; Update subdir headers.

(defun dired-du--update-subdir-header-1 (size-data)
  "Helper function for `dired-du--update-subdir-header'.
SIZE-DATA are the numbers in the subdir header line."
  (let ((inhibit-read-only t))
    (dotimes (i (length size-data))
      (let* ((j (1+ i))
             (fn (lambda ()
                   (cond ((eq t dired-du-size-format)
                          (let ((fn2 (if (or (> j 2)
                                             (< (length size-data) 4))
                                         (function file-size-human-readable)
                                       (lambda (x) (format "%d" x)))))
                            (replace-match (funcall fn2
                                                    (dired-du-string-to-number
                                                     (nth i size-data)))
                                           nil nil nil j)))
                         ((null dired-du-size-format)
                          (replace-match (format "%d"
                                                 (dired-du-string-to-number
                                                  (nth i size-data)))
                                         nil nil nil j))
                         (t
                          (replace-match (dired-du-use-comma-separator
                                          (dired-du-string-to-number
                                           (nth i size-data)))
                                         nil nil nil j))))))
        (funcall fn)))))

(defun dired-du--update-subdir-header (subdir &optional file-info)
  "Show numbers in SUBDIR header according with `dired-du-size-format'.
Optional arg FILE-INFO, if non-nil, is the file info for SUBDIR files."
  (when dired-du-update-headers
    (let ((fn (lambda () (let (new-info)
                           (save-excursion
                             (when (dired-move-to-filename)
                               (setq new-info (dired-du-get-file-info))
                               new-info)))))
          (local   dired-du-local-subdir-header)
          (remote  dired-du-remote-subdir-header)
          (filesp  dired-du-filesp-subdir-header)
          limit used-space available-space num-files
          num-tot-files size-data num-matches)
      (save-excursion
        (dired-goto-subdir subdir)
        (save-excursion (forward-line 2) (setq limit (point)))
        (when (save-excursion
                (or (re-search-forward local limit t)
                    (re-search-forward remote limit t)
                    (re-search-forward filesp limit t)))
          (setq num-matches (/ (- (length (match-data)) 2) 2)
                used-space
                (save-match-data
                  (cond ((null dired-du-mode)
                         (match-string (1- num-matches)))
                        (t
                         (unless file-info
                           (setq file-info
                                 (delq nil
                                       (dired-du-with-saved-marks
                                        (save-excursion
                                          (dired-du-mark-subdir-files
                                           nil 'must-exist)
                                          (dired-du-map-over-marks
                                           (funcall fn) nil nil nil))))))
                         (let ((size
                                (apply #'+
                                       (mapcar
                                        (lambda (x)
                                          (dired-du-string-to-number
                                           (dired-du-alist-get 'size x)))
                                        file-info))))
                           (format "%d" size)))))
                num-files (match-string 1) ; equals used-space for local
                num-tot-files (match-string 2) ; equals available-space for local
                ;; The available-space is shown in kb when
                ;; `directory-free-space-args' is set to its default value (-Pk);
                ;; it may be shown in other units if the user has changed
                ;; `directory-free-space-args'.
                ;; To convert available-space to bytes, its better call
                ;; `directory-free-space-program' again with
                ;; `directory-free-space-args' bind to "-Pk".
                available-space
                (and (not (file-remote-p default-directory))
                     (let ((directory-free-space-args "-Pk"))
                       (format "%d"
                               (* 1024
                                  (dired-du-string-to-number
                                   (get-free-disk-space
                                    (dired-current-directory)))))))
                size-data       (list num-files
                                      num-tot-files
                                      used-space
                                      available-space))
          (cond ((re-search-forward local limit t)
                 (dired-du--update-subdir-header-1 (nthcdr 2 size-data)))
                ((re-search-forward remote limit t)
                 (dired-du--update-subdir-header-1 (list (nth 2 size-data))))
                ((re-search-forward filesp limit t)
                 (dired-du--update-subdir-header-1 size-data))))))))


;;; Obtain required width for the column showing file sizes.

(defun dired-du--get-num-extra-blanks (dir-info)
  "Return the minimum width of size column to fit the largest dir size.
DIR-INFO is the alist with file info as in `dired-du-get-file-info'.

Return value is a list
\(NUM-BLANKS NUM-BLANKS-HUMAN NUM-BLANKS-COMMA MAX-GID-LEN).

NUM-BLANKS is the minimum width of the size column to show the largest
directory size.

NUM-BLANKS-HUMAN is the minimum width of the size column to show the largest
directory size using human readable units.

NUM-BLANKS-COMMA is the minimum width of the size column to show the largest
directory size using thousands comma separator.

MAX-GID-LEN is the largest element of the column just left side of
the size column; usually the gid, but the code is agnostic about the
meaning of such column."
  (let* ((fn (lambda (x)
               (length
                (format "%d"
                        (dired-du-string-to-number
                         (dired-du-alist-get 'size x))))))
         (fn2 (lambda (x)
                (length (file-size-human-readable
                         (dired-du-string-to-number
                          (dired-du-alist-get 'size x))))))
         (fn3 (lambda (x)
                (length (dired-du-use-comma-separator
                         (dired-du-string-to-number
                          (dired-du-alist-get 'size x))))))
         (fn4 (lambda (x) (length (dired-du-alist-get 'gid x))))
         (max-size-len
          (or (and dir-info (apply #'max (mapcar fn dir-info))) 0))
         (max-size-human-len
          (or (and dir-info (apply #'max (mapcar fn2 dir-info))) 0))
         (max-size-comma-len
          (or (and dir-info (apply #'max (mapcar fn3 dir-info))) 0))
         (max-gid-len
          (or (and dir-info (apply #'max (mapcar fn4 dir-info))) 0))
         result num-blanks num-blanks-human num-blanks-comma)
    (setq num-blanks       (1+ max-size-len) ; 1 space far from gid
          num-blanks-human (1+ max-size-human-len)
          num-blanks-comma (1+ max-size-comma-len)
          result           (list num-blanks
                                 num-blanks-human
                                 num-blanks-comma
                                 max-gid-len))
    result))

(defun dired-du--get-max-gid-and-size-lengths-for-subdir
    (subdir max-lens &optional non-dirs)
  "Get max length of gids and sizes for SUBDIR in several formats.
MAX-LENS is a list
\(MAX-SIZE-LEN MAX-SIZE-HUMAN-LEN MAX-SIZE-COMMA-LEN MAX-GID-LEN).

Supported size formats are: default (1024), human (1k),
and comma separator \(1,024).

Optional arg NON-DIRS, when non-nil, then restrict to
non-directories.

Return nil."
  (let* ((max-size-len 0)
         (max-size-human-len 0)
         (max-size-comma-len 0)
         (max-gid-len 0)
         (fn (lambda ()
               (when (and (dired-move-to-filename)
                          (re-search-backward
                           directory-listing-before-filename-regexp)
                          (or (not non-dirs)
                              (not (dired-du-directory-at-current-line-p))))
                 (let (size gid)
                   ;; Handle human readable case: if size is\
                   ;; not shown in human readable.
                   ;; just comeback to the same position.
                   (skip-chars-forward "^ \t")
                   (backward-char 1)
                   (setq size (buffer-substring-no-properties
                               (1+ (point))
                               (prog1
                                   (save-excursion
                                     (skip-chars-backward "^ \t")
                                     (point))
                                 (skip-chars-backward "^ \t")
                                 (skip-chars-backward " \t")))
                         gid  (buffer-substring-no-properties
                               (point)
                               (save-excursion
                                 (skip-chars-backward "^ \t")
                                 (point))))
                   ;; If the file is a dir and `dired-du-mode'\
                   ;; is enabled, then use stored size.
                   (when (and (dired-du-directory-at-current-line-p)
                              dired-du-mode)
                     (let ((name (dired-get-filename t t)))
                       (setq size
                             (or (dired-du--get-value name 'size)
                                 (format "%d"
                                         (dired-du-get-recursive-dir-size))))))
                   (let* ((size-num       (dired-du-string-to-number size))
                          (size-no-human  (format "%d" size-num))
                          (size-comma
                           (dired-du-use-comma-separator size-num))
                          (size-len       (length size-no-human))
                          (size-human-len
                           (length (file-size-human-readable size-num)))
                          (size-comma-len (length size-comma))
                          (gid-len        (length gid)))
                     (setq max-size-len
                           (max max-size-len size-len)
                           max-size-human-len
                           (max max-size-human-len size-human-len)
                           max-size-comma-len
                           (max max-size-comma-len size-comma-len)
                           max-gid-len
                           (max max-gid-len gid-len))) nil)))))
    (save-excursion
      (dired-goto-subdir subdir)
      (dired-du-with-saved-marks
       (save-excursion
         (dired-du-unmark-buffer)
         (dired-du-mark-subdir-files nil 'must-exist)
         (dired-du-map-over-marks (funcall fn) nil nil nil))))
    (setcar max-lens max-size-len)
    (setcdr max-lens (list max-size-human-len
                           max-size-comma-len
                           max-gid-len)) nil))


;;; Change format of file sizes.

(defun dired-du--revert (&optional ignore-auto noconfirm preserve-modes)
  "Revert current dired buffer.
Arguments IGNORE-AUTO, NOCONFIRM and PRESERVE-MODES are ignored."
  (let ((switches dired-actual-switches)
        proc)
    (ignore ignore-auto noconfirm preserve-modes)
    (when (string-match "--human-readable" switches)
      (setq switches (replace-match "" t t switches)))
    (setq switches (apply #'string (delete ?h (string-to-list switches)))
          switches (if (string-match "[ \t\n\r]+\\'" switches)
                       (replace-match "" t t switches)
                     switches))
    (let ((dired-actual-switches switches)
          (prep (make-progress-reporter "Wait until find process finish")))
      (dired-revert)
      (setq proc (get-buffer-process (current-buffer)))
      (while (and proc (memq 'run (process-status proc)))
        (progress-reporter-update prep)
        (sleep-for 1))))
  (dired-du--replace))

(defun dired-du--change-human-sizes (&optional human-readable)
  "Change the format to show the file sizes in the Dired buffer.
Optional arg, HUMAN-READABLE has the same mean as
`dired-du-size-format'."
  ;; To translate human readable format into default numeric format,
  ;; revert the buffer:  for `find-dired' buffers ask
  ;; confirmation before revert.
  (let (revert-find res)
    (unless human-readable
      (let ((switches dired-actual-switches))
        (when (string-match "--human-readable" switches)
          (setq switches (replace-match "" t t switches)))
        (setq switches (apply #'string (delete ?h (string-to-list switches)))
              switches (if (string-match "[ \t\n\r]+\\'" switches)
                           (replace-match "" t t switches)
                         switches))
        (let ((dired-actual-switches switches))
          ;; (prep (make-progress-reporter "Wait until find process finish")))
          ;; Just prompt in the case of `find-dired' buffers.
          (setq revert-find
                (or (not dired-du-find-dired-buffer)
                    (y-or-n-p "Change to numeric size format \
requires revert buffer.  Revert? ")))
          (when revert-find
            (revert-buffer)
            (setq res  t)))))
    (unless revert-find
      (message nil))
    (when human-readable
      (setq res t)
      (save-excursion
        (let* ((max-lens     (make-list 4 0))
               (subdirs      (mapcar 'car dired-subdir-alist))
               (num-subdirs  (length subdirs))
               (counter      0)
               (done         nil)
               (prep (make-progress-reporter
                      (cond ((eq human-readable t)
                             "Changing to human readable sizes...")
                            ((null human-readable)
                             (setq done t)
                             "Changing to default numeric sizes...")
                            (t
                             "Changing to size with thousands \
comma separator..."))
                      0 num-subdirs)))
          (unless done
            (dolist (subdir subdirs)
              (progress-reporter-update prep counter)
              (setq counter (1+ counter))
              (save-excursion
                (dired-goto-subdir subdir)
                (dired-du--update-subdir-header subdir)
                (dired-du--get-max-gid-and-size-lengths-for-subdir
                 subdir max-lens)
                (let* ((max-size-len       (nth 0 max-lens))
                       (max-size-human-len (nth 1 max-lens))
                       (max-size-comma-len (nth 2 max-lens))
                       (max-gid-len        (nth 3 max-lens))
                       (fn (lambda ()
                             (when
                                 (and (dired-move-to-filename)
                                      (re-search-backward
                                       directory-listing-before-filename-regexp))
                               (let (size end-size)
                                 ;; Handle human readable case: if size \
                                 ;; is not shown in human readable
                                 ;; just comeback to the same position.
                                 (skip-chars-forward "^ \t")
                                 (backward-char 1)
                                 (setq end-size (1+ (point))
                                       size     (buffer-substring-no-properties
                                                 end-size
                                                 (progn
                                                   (skip-chars-backward "^ \t")
                                                   (point))))
                                 ;; If the file is a dir and `dired-du-mode'\
                                 ;; is enabled, then use stored size.
                                 (when (and
                                        (dired-du-directory-at-current-line-p)
                                        dired-du-mode)
                                   (let ((name (dired-get-filename t t)))
                                     (setq size (dired-du--get-value name 'size))
                                     (cl-assert (not (null size)))))
                                 (let* ((size-num     (dired-du-string-to-number
                                                       size))
                                        (size-human    (file-size-human-readable
                                                        size-num))
                                        (size-no-human (format "%d" size-num))
                                        (size-comma
                                         (dired-du-use-comma-separator
                                          size-num))
                                        (num-blanks
                                         (cond ((eq t human-readable)
                                                (1+ max-size-human-len))
                                               ((null human-readable)
                                                (1+ max-size-len))
                                               (t
                                                (1+ max-size-comma-len))))
                                        (fmt (format "%%%ds" num-blanks)))

                                   (skip-chars-backward " \t") ; gid end
                                   (skip-chars-backward "^ \t") ; gid start
                                   (forward-char max-gid-len)
                                   (delete-region (point) end-size)
                                   (insert
                                    (format
                                     fmt
                                     (cond ((eq t human-readable) size-human)
                                           ((null human-readable) size-no-human)
                                           (t size-comma))))) nil)))))
                  (dired-du-with-saved-marks
                   (save-excursion
                     (dired-du-unmark-buffer)
                     (dired-du-mark-subdir-files nil 'must-exist)
                     (dired-du-map-over-marks (funcall fn) nil nil nil))))))
            (progress-reporter-done prep))))) res))

(defun dired-du--toggle-human-readable (&optional no-message)
  "Toggle to show file sizes with human readable string in Dired buffers.
Optional arg, NO-MESSAGE, if non-nil don't show message in the echo area."
  (interactive)
  (when (and (derived-mode-p 'dired-mode)
             dired-du-find-dired-buffer
             (not dired-du-on-find-dired-ok))
    (error "Toogle format size in `find-dired' buffers \
is disabled; enable with %s"
           (substitute-command-keys "\\[dired-du-on-find-dired-ok-toggle\]")))

  (when (and (derived-mode-p 'dired-mode)
             (or (not dired-du-find-dired-buffer)
                 dired-du-on-find-dired-ok))
    (let* ((options '(t nil comma))
           (pos     (cl-position dired-du-size-format options))
           (idx     (% (1+ pos) (length options)))
           (human   (nth idx options)))
      (setq dired-du-size-format human)
      ;; If `dired-du--change-human-sizes' return nil, then means the user
      ;; has canceled the change: set `dired-du-size-format' to original
      ;; value.
      (if (not (dired-du--change-human-sizes human))
          (setq dired-du-size-format (nth pos options))
        (let ((string (cond ((eq human t)
                             "Enabled human-readable units in Dired buffer")
                            ((null human)
                             "Enabled default numeric size \
format in Dired buffer")
                            (t
                             "Enabled size with thousands comma \
separator in Dired buffer"))))
          (let ((inhibit-read-only t))
                (dired-insert-set-properties (point-min) (point-max)))
          (unless no-message
            (message string)))))))


;;; Functions to update `dired-du-dir-info'.

(defun dired-du--delete-entry (name)
  "Delete from `dired-du-dir-info' entry for file NAME."
  (let ((glob-rel-pos (dired-du--get-position name)))
    (if (not glob-rel-pos)
        (error "Trying to delete unexistant entry for file '%s'" name)
      (let* ((glob-pos (car glob-rel-pos))
             (info (cdr (nth glob-pos dired-du-dir-info))))
        (setq info (delete (assoc name info) info))
        (setf (cdr (nth glob-pos dired-du-dir-info))
              info)
        nil))))

(defun dired-du--local-update-dir-info (new-entry glob-pos)
  "Update with NEW-ENTRY position GLOB-POS of `dired-du-dir-info'.
NEW-ENTRY is the file information for just one file.

If there is an entry for the same file, it is replaced with NEW-ENTRY.
Otherwise, NEW-ENTRY is added in front to
\(cdr (nth GLOB-POS `dired-du-dir-info')).

Return `dired-du-dir-info'."
  (let ((isdir        (dired-du-alist-get 'isdir new-entry))
        (has-changed  (dired-du-alist-get 'change new-entry)))
    (unless glob-pos
      (progn
        (message "called dired-du--local-update-dir-info with null glob-pos")
        (sit-for 2)
        (ding)
        (setq glob-pos (dired-du--subdir-position
                        (dired-current-directory)))))
    (when (and has-changed isdir)  ; Only update if has change
                                   ; flag non-nil and it is a directory.
      ;; Drop unnecessary info.
      (setq new-entry
            (cl-delete-if
             (lambda (x) (or
                          (eq 'change (car-safe x))
                          (eq 'gid (car-safe x))
                          (eq 'isdir (car-safe x))))

             new-entry))
      (let* ((name         (car new-entry))
             (glob-rel-pos (dired-du--get-position name))
             (info         dired-du-dir-info)
             (replace      (and glob-rel-pos (equal glob-pos
                                                    (car glob-rel-pos)))))
        (cond (replace ; update file.
               (dired-du--delete-entry name)
               (let ((glob-pos (car glob-rel-pos)))
                 (setf (cdr (nth glob-pos dired-du-dir-info))
                       (push new-entry
                             (cdr (nth glob-pos dired-du-dir-info))))))
              (t ; new file.
               (let ((alist (nth glob-pos info)))
                 (if (not (cdr alist)) ; No records.
                     (setq alist (cons (car alist) (list new-entry)))
                   (let ((cdr-new  (cdr alist))) ; Add new info
                     (setcdr alist (push new-entry cdr-new))))
                 (setf (nth glob-pos dired-du-dir-info)
                       alist)))))) dired-du-dir-info))

(defun dired-du--global-update-dir-info (new-info glob-pos)
  "Update with NEW-INFO position GLOB-POS of `dired-du-dir-info'.
NEW-INFO may be the file info for one file or several.

If NEW-INFO contains information for one file already in
`dired-du-dir-info', then the new infomation replace
the old one.  Otherwise, the new information is added in front to
\(cdr (nth GLOB-POS `dired-du-dir-info')).

Return `dired-du-dir-info'."
  (dolist (new-entry new-info)
    (dired-du--local-update-dir-info new-entry glob-pos)))

(defun dired-du-update-dir-info ()
  "Update recursive size for the marked files.
This updates both, `dired-du-dir-info' and the Dired buffer.
If no marked files, update the file at point."
  (interactive)
  (save-excursion
    (dired-du-map-over-marks
     (let ((pos (dired-du--subdir-position (dired-current-directory)))
           (info (list (dired-du-get-file-info))))
       (dired-du--global-update-dir-info info pos))
     nil))
  (dired-du--revert))

(defun dired-du--drop-unexistent-files ()
  "Remove from `dired-du-dir-info' records of unexistent files."
  (when (or (not dired-du-find-dired-buffer)
            (and dired-du-find-dired-buffer
                 dired-du-on-find-dired-ok))
    (let ((subdirs (mapcar 'car dired-subdir-alist)))
      (save-excursion
        (dolist (dir subdirs)
          (let* ((glob-pos  (dired-du--subdir-position dir))
                 (info      (nth glob-pos dired-du-dir-info)))
            (when (cdr info) ; Contains records.
              (let ((entries (cdr info)))
                (dolist (entry entries)
                  (let* ((name     (car entry))
                         (basename (file-name-nondirectory name))
                         ;; (fullname (expand-file-name name default-directory)))
                         (fullname
                          (if (member basename '("." ".."))
                              (concat
                               (file-name-as-directory
                                (dired-current-directory))
                               basename)
                            (expand-file-name name default-directory))))
                    (or (dired-goto-file fullname)
                        (dired-du--delete-entry name))))))))))))

(defun dired-du--reset ()
  "Reset `dired-du-dir-info' to the initial value."
  (setq dired-du-dir-info nil)
  (dired-du--create-or-check-dir-info) nil)

(defun dired-du-recompute-dir-size ()
  "Revert Dired buffer and recompute dir sizes."
  (interactive)
  (dired-du-assert-dired-mode)
  (dired-du--reset)
  (revert-buffer))

(defun dired-du--insert-subdir (dir)
  "Insert subdirectory DIR in `dired-du-dir-info'."
  (let ((subdir (file-name-as-directory dir)))
    (cl-pushnew subdir dired-du-dir-info :test #'equal)))


;;; Get marks, files and directories.

(defun dired-du-get-all-marks ()
  "Return list of marks in the Dired buffer."
  (let (marks)
    (save-excursion
      (dired-du-map-over-marks
       (let* ((pos (save-excursion
                     (goto-char (line-beginning-position))
                     (point)))
              (char (string-to-char
                     (buffer-substring-no-properties pos (1+ pos)))))
         (cl-pushnew char marks)) nil nil nil nil 'all-marks)
      (delete ?\s marks))))

(defun dired-du-get-all-files (&optional local)
  "Return list of files in the Dired buffer.
Optional arg LOCAL, if non-nil, then return file name
relative to `default-directory'.  Otherwise, return fullnames.

If '.' and '..' are present in the buffer, then include them as well."
  (let ((marked
         (delq nil
               (dired-du-get-marked-files
                local nil nil nil nil 'all-marks)))
        (unmarked
         (delq nil
               (dired-du-get-marked-files local nil nil nil ?\s))))
    (delete-dups
     (nconc marked unmarked))))

(defun dired-du--get-all-files-type (type &optional local)
  "Return list of files of type TYPE in the Dired buffer.
TYPE can be 'dirs, for directories, or 'non-dirs, for non directories.

Optional arg LOCAL, if non-nil, then return file name relative
to `default-directory'.

If '.' and '..' are present in the buffer, then include them as well."
  (let* ((fn (lambda ()
               (cond ((eq type 'dirs)
                      (when (dired-du-directory-at-current-line-p)
                        (dired-get-filename local 'noerror)))
                     (t
                      (unless (dired-du-directory-at-current-line-p)
                        (dired-get-filename local 'noerror))))))
         (files (delq nil
                      (dired-du-map-over-marks
                       (funcall fn) nil nil nil ?\s)))
         (files
          (nconc
           files
           (delq nil
                 (dired-du-map-over-marks
                  (funcall fn) nil nil nil nil 'all-marks))))
         (files (delete-dups files)))
    files))

(defun dired-du-get-all-directories (&optional local)
  "Return list of directories in the Dired buffer.
Optional arg LOCAL, if non-nil, then return file name relative
to `default-directory'.

If '.' and '..' are present in the buffer, then include them as well."
  (dired-du--get-all-files-type 'dirs local))

(defun dired-du-get-all-non-directories (&optional local)
  "Return list of non directories in the Dired buffer.
Optional arg LOCAL, if non-nil, then return file name
relative to `default-directory'."
  (dired-du--get-all-files-type 'non-dirs local))

(defun dired-du-get-all-subdir-directories (&optional local)
  "Return all directories in a subdir.
Optional arg LOCAL, if non-nil, return file names relative to
`default-directory'.  Otherwise use the fullname.

If '.' and '..' are present in the buffer, then include them as well."
  (save-restriction
    (narrow-to-region (dired-subdir-min)
                      (dired-subdir-max))
    (dired-du-get-all-directories local)))

(defun dired-du-get-all-subdir-non-directories (&optional local)
  "Return all non-directories in a subdir.
Optional arg LOCAL, if non-nil, return file names relative to
`default-directory'.  Otherwise use the fullname.

If '.' and '..' are present in the buffer, then include them as well."
  (save-restriction
    (narrow-to-region (dired-subdir-min)
                      (dired-subdir-max))
    (dired-du-get-all-non-directories local)))


;;; Insert recursive dir size on Dired buffer.

(defun dired-du--number-as-string-p (str)
  "Return non-nil if STR represents a decimal number."
  (or (string= str "0")
      (and (not (string= str "0"))
           (/= 0 (string-to-number str)))))

(defun dired-du--replace-1 (&optional glob-pos)
  "Replace recursive directory size on Dired buffer.
Optional arg GLOB-POS, if non-nil, is the entry in
`dired-du-dir-info' to replace.  Otherwise, default to 0.

Return file info for current subdir."
  (unless glob-pos (setq glob-pos 0))
  (unless (cdr dired-subdir-alist) (setq glob-pos 0))
  (unless dired-du-mode
    (error "Recursive dir sizes is disabled: Use `dired-du-mode' to enable it"))
  (when (or (not dired-du-find-dired-buffer)
            (and dired-du-find-dired-buffer
                 dired-du-on-find-dired-ok))
    (let* ((inhibit-read-only t)
           (init-pos (point))
           (cur-subdir       (let ((info (nth glob-pos dired-du-dir-info)))
                               (cond ((listp info) (car info))
                                     (t info))))
           ;; All files/dirs must exist, otherwise will fail in '/proc'.
           (all-dirs          (cl-delete-if-not
                               #'file-exists-p
                               (dired-du-get-all-directories)))
           (all-files         (cl-delete-if-not #'file-exists-p
                                                (dired-du-get-all-files)))
           (num-tot-files     (length all-files))
           (num-tot-dirs      (length all-dirs))
           (all-subdir-dirs   (cl-delete-if-not
                               #'file-exists-p
                               (dired-du-get-all-subdir-directories 'local)))
           ;; Collect all directories not in `dired-du-dir-info'
           ;; and process them in parallel.
           (subdir-dirname-size
            (and dired-du-mode
                 (let ((missing-dirs
                        (cl-delete-if
                         (lambda (x)
                            (and (dired-du--file-in-dir-info-p
                                  x
                                  dired-du-dir-info)
                                (not (member x '("." "..")))))
                         all-subdir-dirs)))
                   (when missing-dirs
                     (if dired-du-used-space-program
                         (dired-du-get-recursive-dir-size-in-parallel
                          missing-dirs)
                       (let (res)
                         (save-excursion
                           (dolist (d missing-dirs)
                             (dired-goto-file
                              (expand-file-name d default-directory))
                             (push (list d (dired-du-get-recursive-dir-size))
                                   res)))))))))
           (dir-counter 0)
           (collect-str "Dired-Du collecting file info ...")
           (rep-coll
            (make-progress-reporter
             collect-str 0 num-tot-dirs nil nil 1)) ; Just dirs.
           (replace-str "Dired-Du replacing file info ...")
           (rep-rep
            (make-progress-reporter replace-str 0 num-tot-files)) ; All files.
           file-info name fullname size nblanks-gidlen
           num-blanks num-blanks-human
           num-blanks-comma max-gid-len)
      (save-excursion
        (dired-goto-subdir cur-subdir)
        (let ((fn (lambda ()
                    (let (cdir isdirp new-info)
                      (save-excursion
                        (when (dired-move-to-filename)
                          (setq cdir   (dired-get-filename t t)
                                isdirp (dired-du-directory-at-current-line-p))
                          (when isdirp
                            (save-excursion
                              (goto-char init-pos)
                              (progress-reporter-force-update rep-coll
                                                              dir-counter
                                                              collect-str)))
                          ;; Use the recursive dir size if we already got it.
                          (let ((dirname-size
                                 (cdr (assoc-string cdir subdir-dirname-size))))
                            (setq new-info
                                  (dired-du-get-file-info glob-pos
                                                          nil dirname-size)
                                  dir-counter
                                  (or (and isdirp (1+ dir-counter))
                                      dir-counter)))))
                      new-info))))
          (setq file-info
                (delq nil
                      (when cur-subdir
                        (dired-du-with-saved-marks
                         (save-excursion
                           (dired-du-mark-subdir-files ; Al files.
                            nil
                            'must-exist)
                           (dired-du-map-over-marks (funcall fn) nil nil nil)))))
                nblanks-gidlen    (dired-du--get-num-extra-blanks file-info)
                num-blanks        (nth 0 nblanks-gidlen)
                num-blanks-human  (nth 1 nblanks-gidlen)
                num-blanks-comma  (nth 2 nblanks-gidlen)
                max-gid-len       (nth 3 nblanks-gidlen)))
        (or (= dir-counter num-tot-dirs)
            (progress-reporter-done rep-coll))
        (let* ((replace-str (aref (cdr rep-rep) 3))
               (replace-done (concat replace-str "Done"))
               basename)
          (save-excursion
            (dired-du--update-subdir-header cur-subdir file-info)
            (dolist (finfo file-info)
              (setq name     (car finfo) ;(dired-du-alist-get 'name finfo)
                    size     (dired-du-alist-get 'size finfo)
                    basename (file-name-nondirectory name)
                    fullname (if (member basename '("." ".."))
                                 (concat (file-name-as-directory cur-subdir)
                                         basename)
                               (expand-file-name name default-directory)))
              (when (and (dired-goto-file fullname)
                         (re-search-backward
                          directory-listing-before-filename-regexp
                          (line-beginning-position) t))
                ;; Handle human readable case: in other case just
                ;; comeback to the same position.
                (skip-chars-forward "^ \t")
                (backward-char 1)
                (unless num-blanks (error "The num-blanks null"))
                (unless num-blanks-human (error "The num-blanks-human null"))
                (unless max-gid-len (error "The max-gid-len null"))
                (let ((pos (1+ (point)))
                      (fmt (format "%%%ds" (cond ((eq t dired-du-size-format)
                                                  num-blanks-human)
                                                 ((null dired-du-size-format)
                                                  num-blanks)
                                                 (t num-blanks-comma))))
                      gid-start gid-end)
                  (skip-chars-forward "^ \t")
                  (skip-chars-backward "^ \t")
                  (skip-chars-backward " \t")
                  (setq gid-end (point))
                  (skip-chars-backward "^ \t")
                  (setq gid-start (point))
                  ;; With numeric GID, the column is right indented; otherwise,
                  ;; the column is left indented.
                  (if (not (dired-du--number-as-string-p
                            (buffer-substring-no-properties gid-start gid-end)))
                      (forward-char max-gid-len)
                    (goto-char gid-end))
                  (delete-region (point) pos)
                  (insert
                   (format fmt
                           (cond ((eq t dired-du-size-format)
                                  (file-size-human-readable
                                   (dired-du-string-to-number size)))
                                 ((null dired-du-size-format)
                                  (format "%d" (dired-du-string-to-number size)))
                                 (t
                                  (dired-du-use-comma-separator
                                   (dired-du-string-to-number size))))))))
              (forward-line 1)))
          (message replace-done)
          (message nil)
          (nreverse file-info))))))

(defun dired-du--replace ()
  "Replace recursive directory size on Dired buffer."
  (dired-du-assert-dired-mode)
  (when (or (not dired-du-find-dired-buffer)
            (and dired-du-find-dired-buffer
                 dired-du-on-find-dired-ok))
    (unless dired-du-mode
      (error "Recursive dir sizes is disabled: \
Use `dired-du-mode' to enable it"))
    (let ((subdirs (mapcar 'car dired-subdir-alist))
          empty-info result)
      (dired-du-with-saved-marks
       (save-excursion
         (dired-du-unmark-buffer)
         (dolist (dir subdirs)
           (let ((glob-pos  (dired-du--subdir-position dir)))
             (unless glob-pos ; Inserting a new subdir.
               (dired-du--insert-subdir dir)
               (unless (equal 0 (dired-du--subdir-position dir))
                 (error "The glob-pos for dir %s not 0 (%S) %S"
                        dir
                        (dired-du--subdir-position dir)
                        dired-du-dir-info))
               (setq glob-pos 0))
             (let ((dir-info (dired-du--replace-1 glob-pos)))
               (when dired-du-mode
                 (if empty-info
                     (push dir-info result)
                   (dired-du--global-update-dir-info dir-info glob-pos))))))))
      ;; When empty-dir we are setting first time this directory.
      (when (and empty-info dired-du-mode)
        (setcdr dired-du-dir-info result))
      (let ((inhibit-read-only t))
        (dired-insert-set-properties (point-min) (point-max))))))


;;; Define minor mode.

;;;###autoload
(define-minor-mode dired-du-mode
  "Toggle dired-du mode.
Interactively with no argument, this command toggles the mode.
A positive prefix argument enables the mode, any other prefix
argument disables it.  From Lisp, argument omitted or nil enables
the mode, `toggle' toggles the state.

Show the recursive size of directories in Dired buffers.
Once this mode is enabled, every new Dired buffer displays
recursive dir sizes.
The directory size is obtained with `dired-du-used-space-program'.

Note that obtaining the recursive size of all the directories
in a Dired buffer might be slow; thus, it may significantly delay
the time to display a new Dired buffer.

Instead of enabling `dired-du-mode' by default in all Dired buffers
you might prefer to use this mode as a convenient interfaz to
the `du' program: just enable it in the current Dired buffer,
and disable it once you have finished checking the used space."
  :init-value nil
  :lighter (:eval (if dired-du-mode
                      " Dired-du"
                    ""))
  :keymap nil
  :variable dired-du-mode
  ;; Propagate the state to all Dired buffers.
  ;; Only the current buffer is reverted.
  :after-hook (let ((state dired-du-mode))
                (dolist (buff dired-buffers)
                  (with-current-buffer (cdr buff)
                    (force-mode-line-update)
                    (setq dired-du-mode state)
                    (setq revert-buffer-function
                          (or (and state #'dired-du--revert)
                              #'dired-revert)))))

  ;; If `major-mode' not dired mode, set `dired-du-mode' nil and exit.
  (unless (derived-mode-p 'dired-mode)
    (error "Dired-Du: Buffer not a Dired buffer"))
  (cond (dired-du-mode
         (advice-add 'find-dired-sentinel :around #'dired-du--find-dired-around)

         (add-hook 'dired-before-readin-hook #'dired-du--drop-unexistent-files)
         (add-hook 'dired-after-readin-hook #'dired-du--replace 'append)
         (add-hook 'dired-du-mode-hook #'dired-du--initialize)
         (add-hook 'dired-mode-hook #'dired-du-mode))
        (t
         (advice-remove 'find-dired-sentinel #'dired-du--find-dired-around)
         (remove-hook 'dired-before-readin-hook
                      #'dired-du--drop-unexistent-files)
         (remove-hook 'dired-after-readin-hook #'dired-du--replace)
         (remove-hook 'dired-mode-hook #'dired-du-mode))))

(defun dired-du--initialize ()
  "Called by function `dired-du-mode' to initialize the mode."
  (let ((enable-str  "Dired-Du mode enabled")
        (disable-str "Dired-Du mode disabled")
        (mode-on     dired-du-mode))
    (cond ((not (derived-mode-p 'dired-mode))
           (error "Major mode not dired-mode"))
          (t
           (cond (mode-on
                  (when (and (null dired-du-used-space-program)
                             (null dired-du--user-warned))
                    (setq dired-du--user-warned t)
                    (beep)
                    (message "Program `dired-du-used-space-program' not found.
Fallback to calculate recursive dir size in Lisp.
Please, consider install a 'du' executable suitable to your platform.")
                    (sit-for 1)
                    (message nil))
                  (message "Initializing Dired-Du mode ...")
                  (dired-du--replace)
                  (message "%s in Dired buffers" enable-str))
                 (t
                  (dired-revert)
                  (message "%s in Dired buffers" disable-str)))))))


;;; Count marked files and their sizes.

(defun dired-du-distinguish-one-marked (info)
  "Return INFO without 1 marked flag.
INFO is the output of `dired-du-get-marked-files' or
`dired-du-map-over-marks'."
  (let ((res (cond ((not (cdr info)) nil)
                   ((and (not (cddr info)) (eq (car info) t))
                    (cdr info))
                   (t info)))) res))

(defun dired-du--cache-dir-info (&optional dir-info
                                           target-files
                                           include-dirs
                                           mark all-marks)
  "Update `dired-du-dir-info' and return it.
Optional arg DIR-INFO, if non-nil, is the new value.  Otherwise, it is
obtained within this function.

Optional arg TARGET-FILES, if non-nil, then is a list of the
full name of the files to update.  Otherwise use all marked files.

Optional arg INCLUDE-DIRS, if non-nil, then include the size
of the marked directories.

Optional arg MARK, if non-nil, is the mark character to search.
Otherwise use `dired-marker-char'.

Optional arg ALL-MARKS, if non-nil, acept all mark characters."
  (cond (dir-info
         (setq dired-du-dir-info dir-info))
        (t
         (save-excursion
           (dired-du--create-or-check-dir-info)
           (let* ((init-pos (point))
                  (files
                   (cond (target-files)
                         (t
                          (let ((marked
                                 (dired-du-get-marked-files
                                  nil nil nil t mark 'all-marks)))
                            (dired-du-distinguish-one-marked marked)))))
                  (info dired-du-dir-info)
                  ;; Only files which are not already in info except '.' and '..'
                  (files
                   (cl-delete-if
                    (lambda (x)
                      (let ((basename (file-name-nondirectory x)))
                        (and (dired-du--file-in-dir-info-p x info)
                             (not (member basename '("." "..")))))) files))
                  (num-files   (length files))
                  (collect-str "Dired-Du catching file info ...")
                  (progress-reporter-collect
                   (make-progress-reporter collect-str 0 num-files nil nil 1))
                  (counter 0)
                  (fn (lambda ()
                        (let ((file (dired-get-filename nil 'noerror))
                              dir isdirp glob-pos new-info)
                          (save-excursion
                            ;; Only those in files.
                            (when (and (member file files)
                                       (dired-move-to-filename))
                              (setq dir    (file-name-directory file)
                                    isdirp (dired-du-directory-at-current-line-p)
                                    glob-pos (dired-du--subdir-position dir)
                                    counter  (1+ counter))
                              ;; Include dirs means get recursive size for dirs.
                              (let ((dired-du-mode include-dirs))
                                (setq new-info
                                      (list (dired-du-get-file-info
                                             nil 'dir-dots))))
                              ;; For dirs only cache recursive size.
                              ;; for non-dirs always cache.
                              (when (and glob-pos new-info isdirp include-dirs)
                                (dired-du--global-update-dir-info
                                 new-info glob-pos))))
                          (when isdirp
                            (save-excursion
                              (goto-char init-pos)
                              (progress-reporter-force-update
                               progress-reporter-collect
                               counter
                               collect-str)))
                          nil))))
             (let ((marked-files
                    (dired-du-get-marked-files nil nil nil t mark all-marks)))
               (when (cdr marked-files)
                 (dired-du-map-over-marks
                  (funcall fn) nil nil nil mark all-marks)
                 (progress-reporter-done progress-reporter-collect)))))))
  dired-du-dir-info)

(defun dired-du--count-sizes-2 (mark all-marks include-dirs)
  "Helper function for `dired-du-count-sizes'.
Return list (MARK NUM_NON_DIRS NUM_DIRS TOTAL_SIZE).

If arg ALL-MARKS, non-nil, then use all character marks in the buffer.

If arg INCLUDE-DIRS, if non-nil, then include the directory sizes."
  (when (and include-dirs
             (not (equal 0 (condition-case nil
                               (process-file (car dired-du-used-space-program)
                                             nil nil nil null-device)
                             (error nil))))
             (null dired-du--user-warned))
    (setq dired-du--user-warned t)
    (beep)
    (message "Program `dired-du-used-space-program' not found.
Fallback to calculate recursive dir size in Lisp.
Please, consider install a 'du' executable suitable to your platform.")
    (sit-for 1)
    (message nil))
  (if (eq mark ?\r)
      (progn
        (message "Mark cannot be \\r")
        (sit-for 1)
        (ding))
    (save-excursion
      (let* ((files        (dired-du-get-marked-files nil nil nil t mark))
             (files        (dired-du-distinguish-one-marked files))
             (num-files    (length files))
             (dirs         (delq nil
                                 (dired-du-map-over-marks
                                  (when (dired-du-directory-at-current-line-p)
                                    (dired-get-filename nil 'noerror))
                                  nil nil t mark all-marks)))
             (dirs         (dired-du-distinguish-one-marked dirs))
             (num-dirs     (length dirs))
             (num-non-dirs (- num-files num-dirs))
             (dir-info     (dired-du--cache-dir-info nil
                                                     dirs
                                                     include-dirs
                                                     mark all-marks))
             ;; size for all non-directories
             (non-dirs-size
              (apply
               #'+
               (mapcar
                (lambda (x)
                  (dired-du-string-to-number
                   (dired-du-alist-get 'size x)))
                (let* ((info
                        (delq nil
                              (dired-du-map-over-marks
                               (unless (dired-du-directory-at-current-line-p)
                                 (dired-du-get-file-info))
                               nil nil 'distinguish-one-marked mark all-marks)))
                       (info (dired-du-distinguish-one-marked info))) info))))
             ;; (info (delq nil (dired-du-map-over-marks
             ;;                  (if (and (dired-du-directory-at-current-line-p)
             ;;                           include-dirs)
             ;;                      (dired-du-get-recursive-dir-size)
             ;;                    (dired-du-get-file-size-remote))
             ;;                  nil nil 'distinguish-one mark all-marks)))
             ;; (info (dired-du-distinguish-one-marked info))
             ;; (total-size (apply #'+ info))
             (total-size    non-dirs-size)
             total-size-str)
        ;; Add recursive size of directories
        (when (and include-dirs
                   (not (= num-dirs 0)))
          (let ((scale-factor
                 (if (and dired-du-used-space-program
                          (string= (cadr dired-du-used-space-program) "-sk"))
                     1024.0
                   1.0)))
            (cond (dir-info ; Cache size dir
                   (let ((dirs-size
                          (apply
                           #'+
                           (mapcar
                            (lambda (name)
                              (let* ((relname
                                      (dired-du-filename-relative-to-default-dir
                                       name))
                                     (glob-pos
                                      (dired-du--fullname-to-glob-pos name))
                                     (size     (dired-du--get-value
                                                relname
                                                'size
                                                dir-info
                                                glob-pos)))
                                (or (and size
                                         (dired-du-string-to-number size))
                                    0))) dirs))))
                     (setq total-size
                           (+ total-size (* scale-factor dirs-size)))))
                  (t ; Get size dir with `dired-du-dir-info'.
                     ; Needed if dir size not cached.
                   (let* ((sizes
                           (mapcar
                            (lambda (fullname)
                              (save-excursion
                                (or (and (dired-goto-file fullname)
                                         (dired-du-get-recursive-dir-size))
                                    0))) dirs))
                          (dirs-size (apply #'+ sizes)))
                     (setq total-size
                           (+ total-size (* scale-factor dirs-size))))))))

        (setq total-size-str
              (cond ((eq t dired-du-size-format)
                     (file-size-human-readable total-size))
                    ((null dired-du-size-format)
                     (format "%d" total-size))
                    (t
                     (let ((total
                            (string-to-number
                             (format "%.0f" total-size))))
                       (dired-du-use-comma-separator total)))))
        (list mark num-non-dirs num-dirs total-size-str)))))

(defun dired-du--count-sizes-1 (mark all-marks include-dirs)
  "Helper function for `dired-du-count-sizes'.
Return alist (MARK . TOTAL_SIZE).

If arg ALL-MARKS, non-nil, then use all character marks in the buffer.

If arg INCLUDE-DIRS, non-nil, then include the directory sizes."
  (unless mark (setq mark dired-marker-char))
  (let ((marks (dired-du-get-all-marks))
        mark-size-alist)
    (cond ((not all-marks)
           (setq mark-size-alist
                 (list (dired-du--count-sizes-2
                        mark
                        nil
                        include-dirs))))
          (t
           (unless marks
             (error "No marked files"))
           (dolist (cur-mark marks)
             (push (dired-du--count-sizes-2
                    cur-mark
                    nil
                    include-dirs) mark-size-alist))))
    mark-size-alist))

;;;###autoload
(defun dired-du-count-sizes (mark &optional all-marks include-dirs)
  "Count sizes of files marked with MARK.
If MARK evaluates nil, then use `dired-marker-char'.

Optional arg ALL-MARKS, if non-nil, then accept all mark characters.

Optional arg INCLUDE-DIRS, if non-nil, include the recursive size of the
marked directories.
If called interactively with a prefix, then prompt for previous
args.  Otherwise, all optional arguments but INCLUDE-DIRS are nil, and
INCLUDE-DIRS is set to variable `dired-du-mode'.

Directories '.' '..' are not special: if they are marked, then return
their recursive size."
  (interactive
   (let* ((cursor-in-echo-area t)
          (askme current-prefix-arg)
          (all-marks (and askme (y-or-n-p "All marks? ")))
          (mark (or (and askme
                         (not all-marks)
                         (progn
                           (message "Count files marked with mark: ")
                           (read-char)))
                    dired-marker-char))
          ;; If `dired-du-mode' is enabled include dirs; otherwise prompt user.
          (dirs (or dired-du-mode
                    (and askme
                         ;; (car dired-du-used-space-program)
                         (y-or-n-p "Include directories? ")))))
     (list mark all-marks dirs)))
  (dired-du-assert-dired-mode)
  (save-excursion
    (let ((mark-size-alist (dired-du--count-sizes-1 mark all-marks include-dirs))
          (out-buf         (get-buffer-create "*dired-du-count-sizes*"))
          text)
      (with-current-buffer out-buf
        (erase-buffer)
        (dolist (mark-info mark-size-alist)
          (let* ((cur-mark     (nth 0 mark-info))
                 (num-non-dirs (nth 1 mark-info))
                 (num-dirs     (nth 2 mark-info))
                 (size-str     (nth 3 mark-info))
                 (num-files    (+ num-non-dirs num-dirs)))
            (setq text
                  (if (= num-files 0)
                      (format "No marked files with mark '%s'\n"
                              (char-to-string cur-mark))
                    (format "Marked with '%s' %d file%s (%d/%d dirs/files) \
with total size %s%s%s\n"
                            (char-to-string cur-mark)
                            num-files
                            (dired-plural-s num-files)
                            num-dirs
                            num-non-dirs
                            size-str
                            (or (and (eq t dired-du-size-format) "") " bytes")
                            (or (and (not include-dirs)
                                     " (dirs size excluded)") ""))))
            (insert text))))
      (if (cdr mark-size-alist)
          (display-buffer out-buf)
        (message (substring text 0 -1))))))



;;; Miscellaneous functions.

;;;###autoload
(defun dired-du-insert-marked-dirs ()
  "Insert all marked subdirectories."
  (interactive)
  (let ((dired-du dired-du-mode))
    (unwind-protect
        (save-excursion
          (when dired-du (dired-du-mode -1))
          (mapc 'dired-maybe-insert-subdir (dired-du-get-marked-files)))
      (when dired-du (dired-du-mode)))))

(defun dired-du-drop-all-subdirs ()
  "Drop all subdirs in the current Dired buffer."
  (interactive)
  (while (cdr dired-subdir-alist)
    (dired-unsubdir (caar dired-subdir-alist)))
  (goto-char (point-min))
  (dired-revert))


(provide 'dired-du)

;;; dired-du.el ends here
