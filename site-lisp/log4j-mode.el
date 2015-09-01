;;; log4j-mode.el --- major mode for viewing log files

;; Copyright (C) 2006-2008 Johan Dykstrom

;; Author: Johan Dykstrom <jody4711-sourceforge@yahoo.se>
;; Created: Jan 2006
;; Version: 1.3
;; Keywords: log, log4j, java

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be
;; useful, but WITHOUT ANY WARRANTY; without even the implied
;; warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
;; PURPOSE.  See the GNU General Public License for more details.

;; You should have received a copy of the GNU General Public
;; License along with this program; if not, write to the Free
;; Software Foundation, Inc., 59 Temple Place, Suite 330, Boston,
;; MA 02111-1307 USA

;;; Commentary:

;; This package provides a major mode for viewing log files, including syntax
;; highlighting, filtering, and source code browsing.
;;
;; Log records are syntax highlighted using keywords such as INFO and ERROR.
;; Customizable regular expressions are used to find the beginning and end of
;; multi-line log records.
;;
;; To filter a log file buffer, type `C-c C-s', and enter the desired filter
;; criteria - any number of keywords separated by spaces. Log records that
;; contain any of the words in the include list, and none of the words in the
;; exclude list, will be copied to the filter buffer. All other log records
;; will be discarded. If the include list is blank, all log records will be
;; included. If the exclude list is blank, no records will be excluded. If the
;; log file buffer is auto reverted, the filter buffer will be updated too. To
;; stop filtering the log file buffer, just type `C-c C-s' again.
;;
;; To show the source code for a Java identifier found in the log file, place
;; the point in the identifier, and type `C-c C-b'. Log4j mode will parse the
;; expression around point, and look up the Java identifier found using jtags
;; - an Emacs package for editing and browsing Java source code.
;;
;; This command is only enabled if package jtags is loaded. Note that this
;; version of Log4j mode requires jtags version 0.95 or later. For more
;; information about jtags, see http://jtags.sourceforge.net.
;;
;; Finally, the commands `M-}' and `M-{' are redefined to move to the end
;; and beginning of the current log record.
;;
;; The latest version of Log4j mode can always be found at
;; http://log4j-mode.sourceforge.net.

;; Installation:

;; Place "log4j-mode.el" in your `load-path' and place the following lines
;; of code in your init file:
;;
;; (autoload 'log4j-mode "log4j-mode" "Major mode for viewing log files." t)
;; (add-to-list 'auto-mode-alist '("\\.log\\'" . log4j-mode))
;;
;; To enable source code browsing, place "jtags.el" in your `load-path' too.

;; Configuration:

;; You can customize the faces that are used for syntax highlighting.
;; Type `M-x customize-group' and enter group name "log4j-mode".
;;
;; Log file buffers are auto reverted by default. If you don't like that,
;; set `log4j-auto-revert-flag' to nil.
;;
;; You can also customize the regular expressions that are used to find the
;; beginning and end of multi-line log records. However, in many cases this
;; will not be necessary. Log4j mode can automatically detect single-line and
;; multi-line log records created by Log4j and JDK's built-in logging package.
;;
;; If you use the arrow keys to move around in the text, you can define `C-up'
;; and `C-down' to move to the end and beginning of the current log record.
;; Put the following lines of code in your init file:
;;
;; (add-hook
;;  'log4j-mode-hook
;;  (lambda ()
;;    (define-key log4j-mode-local-map [(control down)] 'log4j-forward-record)
;;    (define-key log4j-mode-local-map [(control up)] 'log4j-backward-record)))

;; XEmacs:

;; XEmacs tends to move the point to `point-min' when auto reverting a buffer.
;; Setting the customizable variable `log4j-restore-point-flag' to 't leaves
;; the point at its original position.
;;
;; To tell XEmacs which tags table files to use for log files, modify variable
;; `tag-table-alist' to include log files. Using the example in file "jtags.el"
;; you could put the following lines of code in your init file:
;;
;; (setq tag-table-alist '(("\\.\\(java\\|log\\)$" . "c:/java/j2sdk1.4.2/src")
;;                         ("\\.\\(java\\|log\\)$" . "c:/projects/tetris/src")))

;;; Change Log:

;;  1.3    2008-02-28  Changed load method to autoload. Fixed several XEmacs
;;                     bugs. Added customization of Auto Revert mode.
;;  1.2.1  2008-02-01  Updated to work with jtags version 0.95.
;;  1.2    2006-11-30  Log4j mode is a full major mode, not a Generic mode.
;;                     Rewrote syntax highlighting and filtering to support
;;                     multi-line log records. Improved filtering performance.
;;                     Added source code browsing and commands for moving
;;                     across log records. Added hook variables.
;;  1.1    2006-10-04  Ported to XEmacs. Changed key bindings. Highlights
;;                     complete line.
;;  1.0    2006-01-03  Initial version.

;;; Code:

;; ----------------------------------------------------------------------------
;; Other packages:
;; ----------------------------------------------------------------------------

(eval-when-compile (require 'cl))

;; Use package jtags if available
(condition-case nil
    (require 'jtags)
  (error nil))

;; ----------------------------------------------------------------------------
;; Faces and customization:
;; ----------------------------------------------------------------------------

(defgroup log4j-mode nil
  "Major mode for viewing log files."
  :link '(emacs-library-link :tag "Source File" "log4j-mode.el")
  :group 'faces
  :group 'files)

(defface log4j-font-lock-debug-face '((t (:foreground "Gray45")))
  "*Font Lock face used to highlight DEBUG log records."
  :group 'font-lock-highlighting-faces
  :group 'log4j-mode)
(defvar log4j-font-lock-debug-face
  (make-face 'log4j-font-lock-debug-face))

(defface log4j-font-lock-info-face '((t (:foreground "ForestGreen")))
  "*Font Lock face used to highlight INFO log records."
  :group 'font-lock-highlighting-faces
  :group 'log4j-mode)
(defvar log4j-font-lock-info-face
  (make-face 'log4j-font-lock-info-face))

(defface log4j-font-lock-warn-face '((t (:foreground "DodgerBlue")))
  "*Font Lock face used to highlight WARN log records."
  :group 'font-lock-highlighting-faces
  :group 'log4j-mode)
(defvar log4j-font-lock-warn-face
  (make-face 'log4j-font-lock-warn-face))

(defface log4j-font-lock-error-face '((t (:foreground "Red")))
  "*Font Lock face used to highlight ERROR log records."
  :group 'font-lock-highlighting-faces
  :group 'log4j-mode)
(defvar log4j-font-lock-error-face
  (make-face 'log4j-font-lock-error-face))

(defface log4j-font-lock-fatal-face '((t (:foreground "Red" :bold t)))
  "*Font Lock face used to highlight FATAL log records."
  :group 'font-lock-highlighting-faces
  :group 'log4j-mode)
(defvar log4j-font-lock-fatal-face
  (make-face 'log4j-font-lock-fatal-face))

(defcustom log4j-record-begin-regexp "^"
  "*Regexp that matches the beginning of a multi-line log record.

Log4j mode can automatically detect single-line and multi-line log records
created by Log4j and JDK's built-in logging package. If you use another logging
package, set this variable to a regexp that matches the beginning of a log
record, e.g. \"<log_record>\".

See also function `log4j-guess-file-format'."
  :type 'regexp
  :group 'log4j-mode)

(defcustom log4j-record-end-regexp "$"
  "*Regexp that matches the end of a multi-line log record.

Log4j mode can automatically detect single-line and multi-line log records
created by Log4j and JDK's built-in logging package. If you use another logging
package, set this variable to a regexp that matches the end of a log record,
e.g. \"</log_record>\".

See also function `log4j-guess-file-format'."
  :type 'regexp
  :group 'log4j-mode)

(defcustom log4j-auto-revert-flag 't
  "*Non-nil means that log file buffers have Auto Revert mode on by default.
When the file on disk changes, the log file buffer will be auto reverted.
If the log file buffer is filtered, the filter buffer will be updated too."
  :type 'boolean
  :group 'log4j-mode)

(defcustom log4j-restore-point-flag 't
  "*Non-nil means restore position of point after auto reverting buffer.
When auto reverting a buffer, XEmacs sometimes moves the point to
`point-min'. Setting this variable to 't makes `auto-revert-buffers'
restore the position of the point after auto reverting the buffer."
  :type 'boolean
  :group 'log4j-mode)

;; ----------------------------------------------------------------------------
;; Variables:
;; ----------------------------------------------------------------------------

(defconst log4j-mode-version "1.3"
  "The current version of Log4j mode.")

(defvar log4j-mode-hook nil
  "*Hook run when entering Log4j mode.")

(defvar log4j-after-filter-hook nil
  "*Hook run after updating the filter buffer.
This hook is run as the very last thing after updating the filter buffer.
The point is in the filter buffer when the hook is run.")

(defvar log4j-include-regexp nil
  "A regexp that matches all include filter keywords.
Only log records that match this regexp are copied to the filter buffer.
This variable is set by function `log4j-start-filter'.")

(defvar log4j-exclude-regexp nil
  "A regexp that matches all exclude filter keywords.
Log records that match this regexp are _not_ copied to the filter buffer.
This variable is set by function `log4j-start-filter'.")

(defvar log4j-filter-active-flag nil
  "Non-nil means that log file filtering is active in this buffer.
This variable is set by the functions `log4j-start-filter' and
`log4j-stop-filter'.")

(defvar log4j-last-filter-pos 1
  "The source buffer position where filtering stopped last time.")

(defvar log4j-last-highlight-pos 1
  "The buffer position where syntax highlighting stopped last time.")

(defvar log4j-local-record-begin-regexp nil
  "A regexp that matches the beginning of a log record in this buffer.
This variable is set by function `log4j-guess-file-format'.")

(defvar log4j-local-record-end-regexp nil
  "A regexp that matches the end of a log record in this buffer.
This variable is set by function `log4j-guess-file-format'.")

;; Make some variables buffer local to enable filtering of multiple log files
(make-variable-buffer-local 'log4j-include-regexp)
(make-variable-buffer-local 'log4j-exclude-regexp)
(make-variable-buffer-local 'log4j-filter-active-flag)
(make-variable-buffer-local 'log4j-last-filter-pos)
(make-variable-buffer-local 'log4j-last-highlight-pos)
(make-variable-buffer-local 'log4j-local-record-begin-regexp)
(make-variable-buffer-local 'log4j-local-record-end-regexp)

;; ----------------------------------------------------------------------------
;; Generic functions:
;; ----------------------------------------------------------------------------

(defun log4j-get-point-in-buffer (buffer)
  "Return value of point in buffer BUFFER.
BUFFER may be a buffer or the name of an existing buffer."
  (save-excursion
    (set-buffer buffer)
    (point)))

(defun log4j-filter-list (predicate list)
  "Return a list containing all items satisfying PREDICATE in LIST.
The original LIST is not modified. PREDICATE should be a function of one
argument that returns non-nil if the argument should be part of the result
list. Example:

\(log4j-filter-list \(lambda \(x\) \(> x 3\)\) '\(1 2 3 4 5\)\) -> \(4 5\)"
  (let (result)
    (while list
      (if (funcall predicate (car list))
          (setq result (cons (car list) result)))
      (setq list (cdr list)))
    (reverse result)))

;; ----------------------------------------------------------------------------
;; Moving around:
;; ----------------------------------------------------------------------------

(defun log4j-backward-record ()
  "Move backward to start of log record."
  (interactive)
  (let ((org-pos (point)))
    (if (re-search-backward log4j-local-record-begin-regexp nil t)
        (if (eq org-pos (point))
            (forward-line -1))
      (goto-char (point-min)))))

(defun log4j-forward-record ()
  "Move forward to end of log record."
  (interactive)
  (if (re-search-forward log4j-local-record-end-regexp nil t)
      (if (not (eobp))
          (forward-char))
    (goto-char (point-max))))

(defsubst log4j-record-search-forward (&optional regexp bound)
  "Search forward from point for log record matching REGEXP.
Set point to the end of the occurrence found, and return point.

An optional second argument BOUND bounds the search; it is a buffer position.
The match found must not extend after that position.
This function also sets `match-data' to the entire match.

This is a key function in the package. Both syntax highlighting and
filtering depend on this function being efficient and correct."
  (let ((org-pos (point)))
    (block while-loop

      ;; While there are more matches for REGEXP
      (while (re-search-forward regexp bound t)
        (if (re-search-backward log4j-local-record-begin-regexp org-pos t)
            (let ((begin-pos (point)))

              ;; If we found a matching log record, set match data and return
              (if (re-search-forward log4j-local-record-end-regexp bound t)
                  (progn
                    ;; (message "Regexp `%s' matched at [%d, %d]" regexp begin-pos (point))
                    (set-match-data (list begin-pos (point)))
                    (return-from while-loop (point)))
                (return-from while-loop))))))))

(defsubst log4j-next-record (&optional regexp)
  "Search forward from point for next complete log record.
If REGEXP is specified, search for a log record that contains REGEXP.
Set point to the end of the occurrence found, and return point.
This function also sets `match-data' to the entire match."
  (if regexp
      (log4j-record-search-forward regexp)
    (if (re-search-forward log4j-local-record-begin-regexp nil t)
        (let ((begin-pos (match-beginning 0)))
          (if (re-search-forward log4j-local-record-end-regexp nil t)
              (when (/= begin-pos (point))
                ;; (message "Next record at [%d, %d]" begin-pos (point))
                (set-match-data (list begin-pos (point)))
                (point)))))))

;; ----------------------------------------------------------------------------
;; Filtering and reverting:
;; ----------------------------------------------------------------------------

(defun log4j-setup-buffers ()
  "Setup source buffer and filter buffer for filtering a new log file.
Reset stored buffer position in source buffer. Create or empty filter buffer.
Set Log4j mode."
  (save-excursion
    (setq log4j-last-filter-pos (point-min))
    (let ((record-begin-regexp log4j-local-record-begin-regexp)
          (record-end-regexp log4j-local-record-end-regexp))

      ;; Setup filter buffer
      (set-buffer (get-buffer-create (log4j-filter-buffer-name (buffer-name))))
      (erase-buffer)
      (log4j-mode)

      ;; Copy record begin and end regexps from source buffer
      (setq log4j-local-record-begin-regexp record-begin-regexp)
      (setq log4j-local-record-end-regexp record-end-regexp))))

(defun log4j-filter-buffer-name (source-buffer-name)
  "Return a filter buffer name matching SOURCE-BUFFER-NAME."
  (concat "*" source-buffer-name "*"))

;; ----------------------------------------------------------------------------

(defun log4j-filter-buffer (include-regexp exclude-regexp)
  "Filter the current log file buffer using the supplied filter regexps.

Copy log records that match INCLUDE-REGEXP to the filter buffer, but only if
they do not match EXCLUDE-REGEXP. If INCLUDE-REGEXP is nil, all records are
included. If EXCLUDE-REGEXP is nil, no records are excluded.

When the entire source buffer has been processed, the current buffer position
is stored. The next time the source buffer is updated, filtering starts from
this position."
  (save-excursion
    (save-window-excursion
      (let ((source-buffer-name (buffer-name))
            (filter-buffer-name (log4j-filter-buffer-name (buffer-name)))
            (filter-buffer-pos nil))

        ;; If the filter buffer does not exist, create it
        (unless (bufferp (get-buffer filter-buffer-name))
          (log4j-setup-buffers))

        ;; If the stored buffer position is greater than point-max, the old log
        ;; file has been overwritten with a new, shorter log file
        (if (> log4j-last-filter-pos (point-max))
            (log4j-setup-buffers))
        (setq filter-buffer-pos (save-excursion
                                  (set-buffer filter-buffer-name)
                                  (point)))

        (if auto-revert-verbose
            (message "Filtering buffer `%s'." source-buffer-name))
        ;; (message "log4j-filter-buffer: Starting at %d" log4j-last-filter-pos)
        (goto-char log4j-last-filter-pos)

        ;; While there are records matching the include regexp
        (save-match-data
          (while (and (not (eobp))
                      (log4j-next-record include-regexp))
            (let ((begin-pos (match-beginning 0))
                  (end-pos (match-end 0)))
              (goto-char begin-pos)

              ;; If the record does not match the exclude regexp, copy it
              (unless (and exclude-regexp
                           (re-search-forward exclude-regexp end-pos t))
                ;; (message "log4j-filter-buffer: Found record at [%d, %d]" begin-pos end-pos)
                (set-buffer filter-buffer-name)
                (goto-char (point-max))
                (insert-buffer-substring source-buffer-name begin-pos end-pos)
                (insert "\n")
                (set-buffer source-buffer-name))
              (goto-char end-pos))))

        ;; Store buffer position for next time
        (setq log4j-last-filter-pos (point-max))

        ;; Syntax highlight filter buffer, and run hooks
        (set-buffer filter-buffer-name)
        (log4j-highlight-buffer)
        (goto-char filter-buffer-pos)
        (run-hooks 'log4j-after-filter-hook)))))

;; ----------------------------------------------------------------------------
;; Starting and stopping:
;; ----------------------------------------------------------------------------

(defun log4j-make-regexp (string)
  "Return a regexp to match a substring in STRING.
STRING is a space separated list of keywords.
If STRING is all white space, return nil."
  (let ((strings (log4j-filter-list (lambda (x) (> (length x) 0))
                                    (split-string string))))
    (if strings
        (regexp-opt strings t))))

(defun log4j-start-filter (include-string exclude-string)
  "Turn filtering on in the current log file buffer.
When used interactively, the user enters INCLUDE-STRING and EXCLUDE-STRING,
which should be strings of filter keywords, separated by spaces."
  (interactive "sInclude keywords: \nsExclude keywords: ")
  (message "Filtering is ON in buffer `%s'." (buffer-name))

  (setq log4j-include-regexp (log4j-make-regexp include-string))
  (setq log4j-exclude-regexp (log4j-make-regexp exclude-string))

  (setq log4j-filter-active-flag 't)
  (define-key log4j-mode-local-map [(control c) (control s)] 'log4j-stop-filter)

  (log4j-setup-buffers)
  (display-buffer (log4j-filter-buffer-name (buffer-name)))
  (log4j-filter-buffer log4j-include-regexp log4j-exclude-regexp))

(defun log4j-stop-filter ()
  "Turn filtering off in the current log file buffer."
  (interactive)
  (message "Filtering is OFF in buffer `%s'." (buffer-name))
  (setq log4j-filter-active-flag nil)
  (define-key log4j-mode-local-map [(control c) (control s)] 'log4j-start-filter))

;; ----------------------------------------------------------------------------
;; Browsing source code:
;; ----------------------------------------------------------------------------

(defun log4j-browse-source ()
  "Look up the identifier around or before point, and show its declaration.

This function uses package `jtags' to find and display the declaration of a
Java identifier found in the log file.

Parse the expression around or before point. Split the expression into package,
class and member. Call function `jtags-lookup-identifier' to find out where the
identifier is declared. Load the Java source file and move the point to the
first line of the declaration."
  (interactive)
  (save-excursion
    (if (or (not (boundp 'jtags-version)) (string< jtags-version "0.95"))
        (error "This function requires jtags version 0.95 or later")

      ;; Find beginning of identifier
      (skip-chars-backward "A-Za-z0-9_<>.")
      (when (looking-at "<[A-Za-z0-9_]+>")
        (skip-chars-forward  "<A-Za-z0-9_")
        (forward-char))

      ;; Find end of identifier
      (let ((end-pos (save-excursion (skip-chars-forward  "<A-Za-z0-9_>.") (point)))
            package
            class
            member)

        ;; Try to match "package.class.member", where package is optional
        (if (re-search-forward "\\([A-Za-z0-9_.]+\\\.\\)*\\([A-Za-z0-9_]+\\)\\\.\\([A-Za-z0-9_]+\\|<init>\\)" end-pos t)
            (progn
              (setq package (match-string 1))
              (if package
                  (setq package (substring package 0 (- (length package) 1))))
              (setq class (match-string 2))
              (setq member (match-string 3))

              ;; If constructor
              (if (string-equal member "<init>")
                  (setq member class)))

          ;; Otherwise, try to match a class name
          (if (re-search-forward "\\([A-Za-z0-9_]+\\)" nil t)
              (setq class (match-string 1))))

        ;; Look up identifier using jtags
        (let* ((package-list (if package (list (concat package ".*"))))
               (definition (jtags-lookup-identifier class member package-list)))

          ;; If tag not found, try without member
          (when (null definition)
            (if package
                (setq package (concat package "." class))
              (setq package class))
            (setq package-list (list (concat package ".*")))
            (setq class member)
            (setq member nil)

            (setq definition (jtags-lookup-identifier class member package-list)))
          ;; (message "log4j-browse-source: Definition=%S" definition)

          ;; If tag not found - print message
          (if (null definition)
              (message "Tag not found!")

            ;; Tag found - display declaration in other window
            (let ((file (jtags-definition-file definition))
                  (line (jtags-definition-line definition)))
              (pop-to-buffer (find-file-noselect file t))
              (goto-line line)
              (message "Found tag in %s" file))))))))

;; ----------------------------------------------------------------------------
;; Syntax highlighting:
;; ----------------------------------------------------------------------------

(defun log4j-highlight-buffer ()
  "Syntax highlight buffer incrementally, when buffer has been updated."
  (save-excursion
    ;; If the stored buffer position is greater than point-max, the old log
    ;; file has been overwritten with a new, shorter log file
    (if (> log4j-last-highlight-pos (point-max))
        (setq log4j-last-highlight-pos (point-min)))

    ;; If the stored buffer position is equal to point-min, fontify the whole
    ;; buffer
    (if (equal log4j-last-highlight-pos (point-min))
        (font-lock-fontify-buffer)

      ;; Otherwise, fontify only the new text
      (font-lock-fontify-region log4j-last-highlight-pos (point-max)))
    (setq log4j-last-highlight-pos (point-max))))

(defun log4j-match-record-fatal (bound)
  "Search forward from point to BOUND for FATAL log record."
  (log4j-record-search-forward "\\<\\(FATAL\\)\\>" bound))

(defun log4j-match-record-error (bound)
  "Search forward from point to BOUND for ERROR log record."
  (log4j-record-search-forward "\\<\\(ERROR\\|SEVERE\\)\\>" bound))

(defun log4j-match-record-warn (bound)
  "Search forward from point to BOUND for WARN log record."
  (log4j-record-search-forward "\\<\\(WARN\\(?:ING\\)?\\)\\>" bound))

(defun log4j-match-record-info (bound)
  "Search forward from point to BOUND for INFO log record."
  (log4j-record-search-forward "\\<\\(CONFIG\\|INFO\\)\\>" bound))

(defun log4j-match-record-debug (bound)
  "Search forward from point to BOUND for DEBUG level log record."
  (log4j-record-search-forward "\\<\\(DEBUG\\|FINE\\(?:R\\|ST\\)?\\|STATUS\\)\\>" bound))

(defvar log4j-font-lock-keywords
  (list '(log4j-match-record-fatal 0 'log4j-font-lock-fatal-face)
        '(log4j-match-record-error 0 'log4j-font-lock-error-face)
        '(log4j-match-record-warn  0 'log4j-font-lock-warn-face)
        '(log4j-match-record-info  0 'log4j-font-lock-info-face)
        '(log4j-match-record-debug 0 'log4j-font-lock-debug-face))
  "Describes how to syntax highlight keywords in Log4j mode buffers.")

;; ----------------------------------------------------------------------------
;; Initialization:
;; ----------------------------------------------------------------------------

(defvar log4j-mode-map nil
  "Global keymap used while in Log4j mode.
This keymap is copied to `log4j-mode-local-map' when a new log file buffer is
created.")

(unless log4j-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(control c) (control b)] 'log4j-browse-source)
    (define-key map [(control c) (control s)] 'log4j-start-filter)
    (define-key map [(meta })] 'log4j-forward-record)
    (define-key map [(meta {)] 'log4j-backward-record)
    (setq log4j-mode-map map)))

(defvar log4j-mode-local-map nil
  "Local keymap used while in Log4j mode.
This is a buffer local variable, so any changes to the keymap become buffer
local.")

(defun log4j-after-revert-function ()
  "Update source and filter buffers after auto reverting the source buffer.
This hook function is added to `after-revert-hook' and runs every time the
source buffer has been auto reverted. New log records in the source buffer are
syntax highlighted and filtered."
  (log4j-highlight-buffer)
  (if log4j-filter-active-flag
      (log4j-filter-buffer log4j-include-regexp log4j-exclude-regexp)))

(when (featurep 'xemacs)
  (defadvice auto-revert-buffers (around log4j-restore-point activate)
    "Save point and window start; execute function; restore those things.
 The values of point and window start are restored after auto reverting
 buffers.

 Setting `log4j-restore-point-flag' to nil turns this feature off."
    (if (not log4j-restore-point-flag)
        ad-do-it
      (let ((obuffer (current-buffer))
            (owindow (selected-window))
            (opoints (make-hash-table)))

        (dolist (buffer auto-revert-buffer-list)
          (when (buffer-live-p buffer)
            (set-buffer buffer)
            (when (eq major-mode 'log4j-mode)

              ;; If buffer is visible in any window, select that window,
              ;; and save start point and point
              (when (get-buffer-window buffer)
                (select-window (get-buffer-window buffer))
                (puthash buffer (cons (window-start) (point)) opoints)))))

        ;; Make sure we are not in a visible buffer
        (set-buffer (other-buffer))

        ;; Call advised function
        ad-do-it

        (dolist (buffer auto-revert-buffer-list)
          (when (buffer-live-p buffer)
            (set-buffer buffer)
            (when (eq major-mode 'log4j-mode)

              ;; If buffer is visible in any window, select that window,
              ;; and restore start point and point
              (when (get-buffer-window buffer)
                (select-window (get-buffer-window buffer))

                ;; If point has been moved during auto revert
                (let ((odata (gethash buffer opoints)))
                  (when (not (equal odata (cons (window-start) (point))))
                    (if auto-revert-verbose
                        (message "Restoring point in buffer `%s'." (buffer-name)))
                    (set-window-start (get-buffer-window buffer) (car odata))
                    (goto-char (cdr odata))))))))
        (set-buffer obuffer)
        (select-window owindow)))))

(defun log4j-guess-file-format ()
  "Guess log file format, and set record begin and end regexps accordingly.

This function guesses the log file format by looking for patterns that are
usually present in certain types of log files. The following formats are
recognized (in this order):

format             begin                         end
------             -----                         ---

Log4j              \"<log4j:event\"                \"</log4j:event>\"
JDK                \"<record>\"                    \"</record>\"
Customized Value   `log4j-record-begin-regexp'   `log4j-record-end-regexp'
Single-line        \"^\"                           \"$\"

The single-line log record format will always match.

See variables `log4j-record-begin-regexp' and `log4j-record-end-regexp' for
information on how to customize log record regexps."
  (save-excursion
    (let ((found nil))

      ;; Log4j records (org.apache.log4j.xml.XMLLayout)
      (unless found
        (goto-char (point-min))
        (setq log4j-local-record-begin-regexp "<log4j:event")
        (setq log4j-local-record-end-regexp "</log4j:event>")
        (setq found (log4j-next-record)))

      ;; JDK records (java.util.logging.XMLFormatter)
      (unless found
        (goto-char (point-min))
        (setq log4j-local-record-begin-regexp "<record>")
        (setq log4j-local-record-end-regexp "</record>")
        (setq found (log4j-next-record)))

      ;; Customized values
      (unless found
        (goto-char (point-min))
        (setq log4j-local-record-begin-regexp log4j-record-begin-regexp)
        (setq log4j-local-record-end-regexp log4j-record-end-regexp)
        (setq found (log4j-next-record)))

      ;; Single-line log records
      (unless found
        (goto-char (point-min))
        (setq log4j-local-record-begin-regexp "^")
        (setq log4j-local-record-end-regexp "$")
        (setq found (log4j-next-record)))
      )))

;;;###autoload (add-to-list 'auto-mode-alist '("\\.log\\'" . log4j-mode))

;;;###autoload
(defun log4j-mode ()
  "Major mode for viewing log files.
Log4j mode provides syntax highlighting and filtering of log files.
It also provides functionality to find and display the declaration
of a Java identifier found in the log file.

You can customize the faces that are used for syntax highlighting.
Type `M-x customize-group' and enter group name \"log4j-mode\".
You can also customize the regular expressions that are used to find
the beginning and end of multi-line log records. However, in many
cases this will not be necessary.

Commands:
Use `\\<log4j-mode-map>\\[log4j-start-filter]' to start/stop log file filtering in the current buffer.
Enter any number of include and exclude keywords that will be used to
filter the log records. Keywords are separated by spaces.

Use `\\<log4j-mode-map>\\[log4j-browse-source]' to show the declaration of the Java identifier around or
before point. This command is only enabled if package `jtags' is loaded.
For more information about jtags, see http://jtags.sourceforge.net.

Finally, the commands `\\<log4j-mode-map>\\[log4j-forward-record]' and `\\<log4j-mode-map>\\[log4j-backward-record]' move point forward and backward
across log records.

\\{log4j-mode-local-map}"
  (interactive)
  (kill-all-local-variables)

  ;; Set major mode variables
  (setq major-mode 'log4j-mode)
  (setq mode-name "Log4j")

  ;; Make search case sensitive
  (setq case-fold-search nil)

  ;; Guess log file format based on patterns found in file
  (log4j-guess-file-format)

  ;; Use a buffer local copy of global Log4j keymap
  (set (make-local-variable 'log4j-mode-local-map) (copy-keymap log4j-mode-map))
  (use-local-map log4j-mode-local-map)

  ;; Disable font-lock-support-mode - the Font Lock support modes do not work
  ;; well with multi-line log records
  (set (make-local-variable 'font-lock-support-mode) nil)
  (set (make-local-variable 'font-lock-defaults) '(log4j-font-lock-keywords t t))

  ;; Turn on font-lock-mode
  (if (not font-lock-mode)
      (font-lock-mode 1))

  ;; The buffer is completely fontified from the beginning, so "after revert
  ;; fontification" should start at point-max
  (setq log4j-last-highlight-pos (point-max))

  ;; Turn on Auto Revert mode if buffer is visiting a file
  (when (buffer-file-name)
    (if log4j-auto-revert-flag
        (auto-revert-mode 1))
    (add-hook 'after-revert-hook 'log4j-after-revert-function nil t))

  ;; Run any Log4j mode start-up hooks
  (run-hooks 'log4j-mode-hook))

(provide 'log4j-mode)

;; ----------------------------------------------------------------------------

;;; log4j-mode.el ends here
