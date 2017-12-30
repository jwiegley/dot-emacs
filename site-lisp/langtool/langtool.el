;;; langtool.el --- Grammar check utility using LanguageTool

;; Author: Masahiro Hayashi <mhayashi1120@gmail.com>
;; Keywords: docs
;; URL: https://github.com/mhayashi1120/Emacs-langtool
;; Emacs: GNU Emacs 24 or later
;; Version: 1.7.0
;; Package-Requires: ((cl-lib "0.3"))

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; ## Install:

;; Install LanguageTool (and java)
;; http://www.languagetool.org/

;; Put this file into load-path'ed directory, and byte compile it if
;; desired. And put the following expression into your ~/.emacs.
;;
;;     (require 'langtool)
;;     (setq langtool-language-tool-jar "/path/to/languagetool-commandline.jar")
;;
;; If you use old version of LanguageTool, may be:
;;
;;     (setq langtool-language-tool-jar "/path/to/LanguageTool.jar")
;;
;; Alternatively, you can set the classpath where LanguageTool's jars reside:
;;
;;     (require 'langtool)
;;     (setq langtool-java-classpath
;;           "/usr/share/languagetool:/usr/share/java/languagetool/*")

;; These settings are optional:

;; * Key binding if you desired.
;;
;;     (global-set-key "\C-x4w" 'langtool-check)
;;     (global-set-key "\C-x4W" 'langtool-check-done)
;;     (global-set-key "\C-x4l" 'langtool-switch-default-language)
;;     (global-set-key "\C-x44" 'langtool-show-message-at-point)
;;     (global-set-key "\C-x4c" 'langtool-correct-buffer)

;; * Default language is detected by LANG/LC_ALL environment variable.
;;   Please set `langtool-default-language` if you need to change default value.
;;
;;     (setq langtool-default-language "en-US")
;;
;;   Otherwise, invoke `M-x langtool-check` with `C-u` (universal-argument)

;; * Currently GNU java version is not working.
;;   Please change the variable to your favorite java executable.
;;
;;     (setq langtool-java-bin "/path/to/java")

;; * Maybe your LanguageTool have launcher. (e.g. Gentoo)
;;   You need to set `langtool-bin'.
;;   See https://github.com/mhayashi1120/Emacs-langtool/issues/24
;;
;;     (setq langtool-bin "/usr/bin/languagetool")

;; * Maybe you want to specify your mother tongue.
;;
;;     (setq langtool-mother-tongue "en")

;; * To customize LanguageTool commandline arguments.
;;
;;     (setq langtool-java-user-arguments '("-Dfile.encoding=UTF-8"))
;;
;;   You can also make the variable to buffer local like following:
;;
;;     (add-hook '**SOME**-mode-hook
;;               (lambda () (set (make-local-variable 'langtool-java-user-arguments)
;;                              '("-Dfile.encoding=UTF-8"))))
;;
;;   NOTE: Although there is no good example, `langtool-user-arguments' is
;;   a similar custom variable.

;; ## Usage:

;; * To check current buffer and show warnings.
;;
;;     M-x langtool-check
;;
;;   Check with different language. You can complete supported language
;;   with C-i/TAB
;;
;;     C-u M-x langtool-check

;; * To correct marker follow LanguageTool suggestions.
;;
;;     M-x langtool-correct-buffer

;; * Go to warning point you can see a report from LanguageTool.
;;   Otherwise:
;;
;;     M-x langtool-show-message-at-point

;; * Show LanguageTool report automatically by `popup'
;;   This idea come from:
;;   http://d.hatena.ne.jp/LaclefYoshi/20150912/langtool_popup
;;
;;     (defun langtool-autoshow-detail-popup (overlays)
;;       (when (require 'popup nil t)
;;         ;; Do not interrupt current popup
;;         (unless (or popup-instances
;;                     ;; suppress popup after type `C-g' .
;;                     (memq last-command '(keyboard-quit)))
;;           (let ((msg (langtool-details-error-message overlays)))
;;             (popup-tip msg)))))
;;
;;     (setq langtool-autoshow-message-function
;;           'langtool-autoshow-detail-popup)

;; * To finish checking. All langtool marker is removed.
;;
;;     M-x langtool-check-done

;;; TODO:

;; * process coding system (test on Windows)
;; * check only docstring (emacs-lisp-mode)
;;    or using (derived-mode-p 'prog-mode) and only string and comment
;; * java encoding <-> elisp encoding (No enough information..)
;; * change to --json argument to parse. Do not forget to parse partial json
;;  in a process filter. Parsing whole json slow down Emacs

;;; Code:

(require 'cl-lib)
(require 'compile)

(defgroup langtool nil
  "Customize langtool"
  :prefix "langtool-"
  :group 'applications)

;;;
;;; Variables / Faces
;;;

;;
;; constants
;;

(defconst langtool-output-regexp
  (eval-when-compile
    (concat
     "^[0-9]+\\.) Line \\([0-9]+\\), column \\([0-9]+\\), Rule ID: \\(.*\\)\n"
     "Message: \\(.*\\)\n"
     "\\(?:Suggestion: \\(.*\\)\n\\)?"
     ;; As long as i can read
     ;; src/dev/de/danielnaber/languagetool/dev/wikipedia/OutputDumpHandler.java
     "\\(\\(?:.*\\)\n\\(?:[ ^]+\\)\\)\n"
     "\n?"                              ; last result have no new-line
     )))

;;
;; externals
;;

(defvar current-prefix-arg)
(defvar unread-command-events)
(defvar locale-language-names)

;;
;; faces
;;

(defface langtool-errline
  '((((class color) (background dark)) (:background "Firebrick4"))
    (((class color) (background light)) (:background "LightPink"))
    (t (:bold t)))
  "Face used for marking error lines."
  :group 'langtool)

(defface langtool-correction-face
  '((((class mono)) (:inverse-video t :bold t :underline t))
    (t (:background "red1" :foreground "yellow" :bold t)))
  "Face used to visualize correction."
  :group 'langtool)

;;
;; customize variables
;;

(defcustom langtool-java-bin "java"
  "Executing java command."
  :group 'langtool
  :type 'file)

(defcustom langtool-bin nil
  "Executing LanguageTool command."
  :group 'langtool
  :type 'file)

(defcustom langtool-java-user-arguments nil
  "List of string which is passed to java command as arguments.
This java command holds LanguageTool process.
Otherwise, function which return above value.

e.g. ( Described at http://wiki.languagetool.org/command-line-options )
\(setq langtool-java-user-arguments '(\"-Dfile.encoding=UTF-8\"))

"
  :group 'langtool
  :type '(choice
          (repeat string)
          function))

(defcustom langtool-language-tool-jar nil
  "LanguageTool jar file.

No need to set this variable when `langtool-java-classpath' is set."
  :group 'langtool
  :type 'file)

(defcustom langtool-java-classpath nil
  "Custom classpath to use on special environment. (e.g. Arch Linux)
Do not set both of this variable and `langtool-language-tool-jar'.

https://github.com/mhayashi1120/Emacs-langtool/pull/12
https://github.com/mhayashi1120/Emacs-langtool/issues/8"
  :group 'langtool
  :type 'string)

(defcustom langtool-default-language nil
  "Language name pass to LanguageTool."
  :group 'langtool
  :type 'string)

(defcustom langtool-mother-tongue nil
  "Your mothertongue Language name pass to LanguageTool."
  :group 'langtool
  :type 'string)

(defcustom langtool-disabled-rules nil
  "Disabled rules pass to LanguageTool.
String that separated by comma or list of string.
"
  :group 'langtool
  :type '(choice
          (list string)
          string))

(defcustom langtool-user-arguments nil
  "Similar to `langtool-java-user-arguments' except this list is appended
 after `-jar' argument.

Valid values are described below:
http://wiki.languagetool.org/command-line-options

Do not change this variable if you don't understand what you are doing.
"
  :group 'langtool
  :type '(choice
          (repeat string)
          function))

(defcustom langtool-error-exists-hook
  '(langtool-autoshow-ensure-timer)
  "Hook run after LanguageTool process found any error(s)."
  :group 'langtool
  :type 'hook)

(defcustom langtool-noerror-hook nil
  "Hook run after LanguageTool report no error."
  :group 'langtool
  :type 'hook)

(defcustom langtool-finish-hook
  '(langtool-autoshow-cleanup-timer-maybe)
  "Hook run after cleanup buffer."
  :group 'langtool
  :type 'hook)

;;
;; local variables
;;

(defvar langtool-local-disabled-rules nil)
(make-variable-buffer-local 'langtool-local-disabled-rules)

(defvar langtool-temp-file nil)
(make-variable-buffer-local 'langtool-temp-file)

(defvar langtool-buffer-process nil)
(make-variable-buffer-local 'langtool-buffer-process)

(defvar langtool-mode-line-message nil)
(make-variable-buffer-local 'langtool-mode-line-message)
(put 'langtool-mode-line-message 'risky-local-variable t)

(defvar langtool-error-buffer-name " *LanguageTool Errors* ")

(defvar langtool--debug nil)

(defvar langtool--correction-keys
  ;; (q)uit, (c)lear, (e)dit, (i)gnore
  [?0 ?1 ?2 ?3 ?4 ?5 ?6 ?7 ?8 ?9
      ;; suggestions may over 10.
      ;; define rest of alphabet just in case.
      ?a ?b ?d ?f ?g ?h ?j ?k ?l ?m ?n
      ?o ?p ?r ?s ?t ?u ?v ?w ?x ?y ?z])

;;;
;;; Internal functions
;;;

;;
;; basic functions
;;

(defmacro langtool--with-java-environ (&rest form)
  `(let ((coding-system-for-read langtool-process-coding-system))
     (progn ,@form)))

(defun langtool-region-active-p ()
  (cond
   ((fboundp 'region-active-p)
    (funcall 'region-active-p))
   (t
    (and transient-mark-mode mark-active))))

(defun langtool--debug (key fmt &rest args)
  (when langtool--debug
    (let ((buf (get-buffer-create "*LanguageTool Debug*")))
      (with-current-buffer buf
        (goto-char (point-max))
        (insert "---------- [" key "] ----------\n")
        (insert (apply 'format fmt args) "\n")))))

(defun langtool--chomp (s)
  (if (string-match "\\(?:\\(\r\n\\)+\\|\\(\n\\)+\\)\\'" s)
      (substring s 0 (match-beginning 0))
    s))

;;
;; handle error overlay
;;

;;FIXME
;;http://sourceforge.net/tracker/?func=detail&aid=3054895&group_id=110216&atid=655717
(defun langtool--fuzzy-search (context-regexp length)
  (let* ((regexp (concat ".*?" context-regexp))
         (default (cons (point) (+ (point) length))))
    (or (and (null regexp)
             (cons (point) (+ (point) length)))
        (and (looking-at regexp)
             (cons (match-beginning 1) (match-end 1)))
        (let ((beg (min (point-at-bol) (- (point) 20))))
          (cl-loop while (and (not (bobp))
                              (<= beg (point)))
                   ;; backward just sentence length to search sentence after point
                   do (condition-case nil
                          (backward-char length)
                        (beginning-of-buffer nil))
                   if (looking-at regexp)
                   return (cons (match-beginning 1) (match-end 1))))
        default)))

(defun langtool--create-overlay (tuple)
  (let ((line (nth 0 tuple))
        (col (nth 1 tuple))
        (len (nth 2 tuple))
        (sugs (nth 3 tuple))
        (msg (nth 4 tuple))
        (message (nth 5 tuple))
        (rule-id (nth 6 tuple))
        (context (nth 7 tuple)))
    (goto-char (point-min))
    (forward-line (1- line))
    ;;  1. sketchy move to column that is indicated by LanguageTool.
    ;;  2. fuzzy match to reported sentence which indicated by ^^^ like string.
    (forward-char (1- col))
    (cl-destructuring-bind (start . end)
        (langtool--fuzzy-search context len)
      (let ((ov (make-overlay start end)))
        (overlay-put ov 'langtool-simple-message msg)
        (overlay-put ov 'langtool-message message)
        (overlay-put ov 'langtool-suggestions sugs)
        (overlay-put ov 'langtool-rule-id rule-id)
        (overlay-put ov 'priority 1)
        (overlay-put ov 'face 'langtool-errline)))))

(defun langtool--clear-buffer-overlays ()
  (mapc
   (lambda (ov)
     (delete-overlay ov))
   (langtool--overlays-region (point-min) (point-max))))

(defun langtool--overlays-region (start end)
  (sort
   (remove
    nil
    (mapcar
     (lambda (ov)
       (when (overlay-get ov 'langtool-message)
         ov))
     (overlays-in start end)))
   (lambda (ov1 ov2)
     (< (overlay-start ov1) (overlay-start ov2)))))

(defun langtool--current-error-overlays ()
  (remove nil
          (mapcar
           (lambda (ov)
             (and (overlay-get ov 'langtool-message)
                  ov))
           (overlays-at (point)))))

(defun langtool--expire-buffer-overlays ()
  (mapc
   (lambda (o)
     (unless (overlay-get o 'face)
       (delete-overlay o)))
   (langtool--overlays-region (point-min) (point-max))))

(defun langtool--erase-overlay (ov)
  (overlay-put ov 'face nil))

(defun langtool--next-overlay (current overlays)
  (cl-loop for o in (cdr (memq current overlays))
           if (overlay-get o 'face)
           return o))

(defun langtool--prev-overlay (current overlays)
  (cl-loop for o in (cdr (memq current (reverse overlays)))
           if (overlay-get o 'face)
           return o))

(defun langtool--goto-error (overlays predicate)
  (catch 'done
    (mapc
     (lambda (ov)
       (when (funcall predicate ov)
         (goto-char (overlay-start ov))
         (throw 'done t)))
     overlays)
    nil))

(defun langtool-working-p ()
  (cl-loop with current = (current-buffer)
           for buf in (buffer-list)
           when (and (not (eq buf current))
                     (with-current-buffer buf
                       (langtool--overlays-region
                        (point-min) (point-max))))
           return buf
           finally return nil))

;;
;; utility
;;

(defun langtool-simple-error-message (overlays)
  "Textify error messages as long as simple."
  (mapconcat
   (lambda (ov)
     (format
      "[%s] %s%s"
      (overlay-get ov 'langtool-rule-id)
      (overlay-get ov 'langtool-simple-message)
      (if (overlay-get ov 'langtool-suggestions)
          (concat
           " -> ("
           (mapconcat 'identity (overlay-get ov 'langtool-suggestions) ", ")
           ")")
        "")))
   overlays "\n"))

(defun langtool-details-error-message (overlays)
  "Textify error messages."
  (mapconcat
   (lambda (ov)
     (concat
      (format "Rule ID: %s\n"
              (overlay-get ov 'langtool-rule-id))
      (format "Message: %s\n"
              (overlay-get ov 'langtool-simple-message))
      (if (overlay-get ov 'langtool-suggestions)
          (concat
           "Suggestions: "
           (mapconcat
            'identity
            (overlay-get ov 'langtool-suggestions)
            "; "))
        "")))
   overlays
   "\n\n"))

(defun langtool--current-error-messages ()
  (mapcar
   (lambda (ov)
     (overlay-get ov 'langtool-message))
   (langtool--current-error-overlays)))

;;
;; LanguageTool Process
;;

(defun langtool--disabled-rules ()
  (let ((custom langtool-disabled-rules)
        (locals langtool-local-disabled-rules))
    (cond
     ((stringp custom)
      (mapconcat 'identity
                 (cons custom locals)
                 ","))
     (t
      (mapconcat 'identity
                 (append custom locals)
                 ",")))))

(defun langtool--check-command ()
  (cond
   (langtool-bin
    (unless (executable-find langtool-bin)
      (error "LanguageTool command not executable")))
   ((or (null langtool-java-bin)
        (not (executable-find langtool-java-bin)))
    (error "java command is not found")))
  (cond
   (langtool-java-classpath)
   (langtool-language-tool-jar
    (unless (file-readable-p langtool-language-tool-jar)
      (error "langtool jar file is not readable"))))
  (when langtool-buffer-process
    (error "Another process is running")))

(defun langtool--basic-command&args ()
  (let (command args)
    (cond
     (langtool-bin
      (setq command langtool-bin))
     (t
      (setq command langtool-java-bin)
      ;; Construct arguments pass to java command
      (setq args (langtool--custom-arguments 'langtool-java-user-arguments))
      (cond
       (langtool-java-classpath
        (setq args (append
                    args
                    (list "-cp" langtool-java-classpath
                          "org.languagetool.commandline.Main"))))
       (langtool-language-tool-jar
        (setq args (append
                    args
                    (list "-jar" (langtool--process-file-name langtool-language-tool-jar))))))))
    (list command args)))

(defun langtool--process-create-buffer ()
  (generate-new-buffer " *LanguageTool* "))

(defun langtool--sentence-to-fuzzy (sentence)
  (mapconcat 'regexp-quote
             ;; this sentence is reported by LanguageTool
             (split-string sentence " +")
             ;; LanguageTool interpreted newline as space.
             "[[:space:]\n]+?"))

(defun langtool--pointed-length (message)
  (or
   (and (string-match "\n\\( *\\)\\(\\^+\\)" message)
        (length (match-string 2 message)))
   ;; never through here, but if return nil from this function make stop everything.
   1))

(defun langtool--process-filter (proc event)
  (langtool--debug "Filter" "%s" event)
  (with-current-buffer (process-buffer proc)
    (goto-char (point-max))
    (insert event)
    (let ((min (or (process-get proc 'langtool-process-done)
                   (point-min)))
          (buffer (process-get proc 'langtool-source-buffer))
          (begin (process-get proc 'langtool-region-begin))
          (finish (process-get proc 'langtool-region-finish))
          n-tuple)
      (goto-char min)
      (while (re-search-forward langtool-output-regexp nil t)
        (let* ((line (string-to-number (match-string 1)))
               (column (1- (string-to-number (match-string 2))))
               (rule-id (match-string 3))
               (suggest (match-string 5))
               (msg1 (match-string 4))
               ;; rest of line. Point the raw message.
               (msg2 (match-string 6))
               (message
                (concat "Rule ID: " rule-id "\n"
                        msg1 "\n\n"
                        msg2))
               (suggestions (and suggest (split-string suggest "; ")))
               (context (langtool--pointed-context-regexp msg2))
               (len (langtool--pointed-length msg2)))
          (setq n-tuple (cons
                         (list line column len suggestions
                               msg1 message rule-id context)
                         n-tuple))))
      (process-put proc 'langtool-process-done (point))
      (when (buffer-live-p buffer)
        (with-current-buffer buffer
          (save-excursion
            (save-restriction
              (when (and begin finish)
                (narrow-to-region begin finish))
              (mapc
               (lambda (tuple)
                 (langtool--create-overlay tuple))
               (nreverse n-tuple)))))))))

;;FIXME sometimes LanguageTool reports wrong column.
(defun langtool--pointed-context-regexp (message)
  (when (string-match "\\(.*\\)\n\\( *\\)\\(\\^+\\)" message)
    (let* ((msg1 (match-string 1 message))
           ;; calculate marker "^" start at column
           (pre (length (match-string 2 message)))
           ;; "^" marker length
           (len (length (match-string 3 message)))
           (end (+ pre len))
           (sentence (substring msg1 pre end))
           (regexp (cond
                    ((string-match "^[[:space:]]+$" sentence)
                     ;; invalid sentence only have whitespace,
                     ;; search with around sentence.
                     (concat
                      "\\("
                      (let* ((count (length sentence))
                             (spaces (format "[[:space:]\n]\\{%d\\}" count)))
                        spaces)
                      "\\)"
                      ;; considered truncated spaces that is caused by
                      ;; `langtool--sentence-to-fuzzy'
                      "[[:space:]]*?"
                      ;; to match the correct block
                      ;; suffix of invalid spaces.
                      (langtool--sentence-to-fuzzy
                       (let ((from (min end (length msg1))))
                         ;;TODO magic number.
                         (substring msg1 from (min (length msg1) (+ from 20)))))))
                    (t
                     (concat "\\("
                             (langtool--sentence-to-fuzzy sentence)
                             "\\)")))))
      regexp)))


(defun langtool--process-file-name (path)
  "Correct the file name depending on the underlying platform.

PATH: The file-name path to be corrected.

Currently corrects the file-name-path when running under Cygwin."
  (setq path (expand-file-name path))
  (cond
   ((eq system-type 'cygwin)
    ;; no need to catch error. (e.g. cygpath is not found)
    ;; this failure means LanguageTools is not working completely.
    (with-temp-buffer
      (call-process "cygpath" nil t nil "--windows" path)
      (langtool--chomp (buffer-string))))
   (t
    path)))

(defcustom langtool-process-coding-system
  (cond
   ((eq system-type 'cygwin)
    'dos)
   (t nil))
  "LanguageTool process coding-system.
Ordinary no need to change this."
  :group 'langtool
  :type 'coding-system)

(defun langtool--custom-arguments (var)
  (let ((value (symbol-value var))
        args)
    (cond
     ((functionp value)
      (setq args (funcall value)))
     ((consp value)
      (setq args value)))
    (copy-sequence args)))

(defun langtool--invoke-process (file begin finish &optional lang)
  (when (listp mode-line-process)
    (add-to-list 'mode-line-process '(t langtool-mode-line-message)))
  ;; clear previous check
  (langtool--clear-buffer-overlays)
  (cl-destructuring-bind (command args)
      (langtool--basic-command&args)
    ;; Construct arguments pass to jar file.
    (setq args (append
                args
                (list "-c" (langtool--java-coding-system
                            buffer-file-coding-system)
                      "-l" (or lang langtool-default-language)
                      "-d" (langtool--disabled-rules))))
    (when langtool-mother-tongue
      (setq args (append args (list "-m" langtool-mother-tongue))))
    (setq args (append args (langtool--custom-arguments 'langtool-user-arguments)))
    (setq args (append args (list (langtool--process-file-name file))))
    (langtool--debug "Command" "%s: %s" command args)
    (let* ((buffer (langtool--process-create-buffer))
           (proc (langtool--with-java-environ
                  (apply 'start-process "LanguageTool" buffer command args))))
      (set-process-filter proc 'langtool--process-filter)
      (set-process-sentinel proc 'langtool--process-sentinel)
      (process-put proc 'langtool-source-buffer (current-buffer))
      (process-put proc 'langtool-region-begin begin)
      (process-put proc 'langtool-region-finish finish)
      (setq langtool-buffer-process proc)
      (setq langtool-mode-line-message
            (list " LanguageTool"
                  (propertize ":run" 'face compilation-info-face))))))

(defun langtool--process-sentinel (proc event)
  (when (memq (process-status proc) '(exit signal))
    (let ((source (process-get proc 'langtool-source-buffer))
          (code (process-exit-status proc))
          (pbuf (process-buffer proc))
          dead marks msg face)
      (when (/= code 0)
        (setq face compilation-error-face))
      (cond
       ((buffer-live-p source)
        (with-current-buffer source
          (setq marks (langtool--overlays-region (point-min) (point-max)))
          (setq face (if marks compilation-info-face compilation-warning-face))
          (setq langtool-buffer-process nil)
          (setq langtool-mode-line-message
                (list " LanguageTool"
                      (propertize ":exit" 'face face)))))
       (t (setq dead t)))
      (cond
       (dead)
       ((/= code 0)
        (let ((msg
               (if (buffer-live-p pbuf)
                   ;; Get first line of output.
                   (with-current-buffer pbuf
                     (goto-char (point-min))
                     (buffer-substring (point) (point-at-eol)))
                 "Buffer was dead")))
          (message "LanguageTool exited abnormally with code %d (%s)"
                   code msg)))
       (marks
        (run-hooks 'langtool-error-exists-hook)
        (message "%s"
                 (substitute-command-keys
                  "Type \\[langtool-correct-buffer] to correct buffer.")))
       (t
        (run-hooks 'langtool-noerror-hook)
        (message "LanguageTool successfully finished with no error.")))
      (when (buffer-live-p pbuf)
        (kill-buffer pbuf)))))

(defun langtool--cleanup-process ()
  ;; cleanup mode-line
  (let ((cell (rassoc '(langtool-mode-line-message) mode-line-process)))
    (when cell
      (remq cell mode-line-process)))
  (when langtool-buffer-process
    (delete-process langtool-buffer-process))
  (kill-local-variable 'langtool-buffer-process)
  (kill-local-variable 'langtool-mode-line-message)
  (kill-local-variable 'langtool-local-disabled-rules)
  (langtool--clear-buffer-overlays)
  (run-hooks 'langtool-finish-hook))

;;FIXME
;; https://docs.oracle.com/javase/6/docs/technotes/guides/intl/encoding.doc.html
(defun langtool--java-coding-system (coding-system)
  (let* ((cs (coding-system-base coding-system))
         (csname (symbol-name cs))
         (aliases (langtool--coding-system-aliases cs))
         (names (mapcar 'symbol-name aliases))
         (case-fold-search nil)
         tmp)
    (cond
     ((string-match "utf-8" csname)
      "utf8")
     ((string-match "utf-16" csname)
      (cond
       ((memq cs '(utf-16le utf-16-le))
        "UnicodeLittleUnmarked")
       ((memq cs '(utf-16be utf-16-be))
        "UnicodeBigUnmarked")
       (t
        "utf-16")))
     ((or (string-match "euc.*jp" csname)
          (string-match "japanese-iso-.*8bit" csname))
      "euc_jp")
     ((string-match "shift.jis" csname)
      "sjis")
     ((string-match "iso.*2022.*jp" csname)
      "iso2022jp")
     ((memq cs '(euc-kr euc-corea korean-iso-8bit))
      "euc_kr")
     ((setq tmp
            (cl-loop for x in names
                     if (string-match "iso-8859-\\([0-9]+\\)" x)
                     return x))
      (concat "ISO8859_" (match-string 1 tmp)))
     ((memq cs '(binary us-ascii raw-text undecided no-conversion))
      "ascii")
     ((memq cs '(cyrillic-koi8))
      "koi8-r")
     ((memq cs '(gb2312))
      "euc_cn")
     ((string-match "\\`\\(cp\\|ibm\\)[0-9]+" csname)
      (downcase csname))
     ((setq tmp
            (cl-loop for x in names
                     if (string-match "^windows-[0-9]+$" x)
                     return x))
      tmp)
     (t
      ;; simply guessed as same name.
      (downcase csname)))))

(defun langtool--coding-system-aliases (coding-system)
  (if (fboundp 'coding-system-aliases)
      ;; deceive elint
      (funcall 'coding-system-aliases coding-system)
    (coding-system-get coding-system 'alias-coding-systems)))

(defun langtool--available-languages ()
  (cl-destructuring-bind (command args)
      (langtool--basic-command&args)
    ;; Construct arguments pass to jar file.
    (setq args (append args (list "--list")))
    (let (res)
      (with-temp-buffer
        (when (and command args
                   (executable-find command)
                   (= (langtool--with-java-environ
                       (apply 'call-process command nil t nil args) 0)))
          (goto-char (point-min))
          (while (re-search-forward "^\\([^\s\t]+\\)" nil t)
            (setq res (cons (match-string 1) res)))
          (nreverse res))))))

;;
;; interactive correction
;;

(defun langtool--ignore-rule (rule overlays)
  (cl-loop for ov in overlays
           do (let ((r (overlay-get ov 'langtool-rule-id)))
                (when (equal r rule)
                  (langtool--erase-overlay ov)))))

(defun langtool--correction (overlays)
  (let ((conf (current-window-configuration)))
    (unwind-protect
        (let ((next (car overlays)))
          (while (setq next (langtool--correction-loop next overlays))))
      (langtool--expire-buffer-overlays)
      (set-window-configuration conf)
      (kill-buffer (langtool--correction-buffer)))))

(defun langtool--correction-loop (ov overlays)
  (let* ((suggests (overlay-get ov 'langtool-suggestions))
         (msg (overlay-get ov 'langtool-simple-message))
         (alist (langtool--correction-popup msg suggests)))
    (catch 'next
      (while (progn
               (goto-char (overlay-start ov))
               (let (message-log-max)
                 (message (concat "C-h or ? for more options; "
                                  "SPC to leave unchanged, "
                                  "Digit to replace word")))
               (let* ((echo-keystrokes) ; suppress echoing
                      (c (downcase (read-char)))
                      (pair (assq c alist)))
                 (cond
                  (pair
                   (let ((sug (nth 1 pair)))
                     ;;TODO when region contains newline.
                     ;; -> insert newline after suggestion.
                     (delete-region (overlay-start ov) (overlay-end ov))
                     (insert sug)
                     (langtool--erase-overlay ov))
                   nil)
                  ((memq c '(?q))
                   (keyboard-quit))
                  ((memq c '(?c))
                   (langtool--erase-overlay ov)
                   nil)
                  ((memq c '(?e))
                   (message (substitute-command-keys
                             "Type \\[exit-recursive-edit] to finish the edit."))
                   (recursive-edit)
                   ;; stay current cursor and wait next user command.
                   (throw 'next ov))
                  ((memq c '(?i))
                   (let ((rule (overlay-get ov 'langtool-rule-id)))
                     (unless (member rule langtool-local-disabled-rules)
                       (setq langtool-local-disabled-rules
                             (cons rule langtool-local-disabled-rules)))
                     (langtool--ignore-rule rule overlays))
                   nil)
                  ((memq c '(?\C-h ?\?))
                   (langtool--correction-help)
                   t)
                  ((memq c '(?\d))
                   (throw 'next (langtool--prev-overlay ov overlays)))
                  ((memq c '(?\s)) nil)
                  (t (ding) t)))))
      ;; next item
      (langtool--next-overlay ov overlays))))

(defun langtool--correction-popup (msg suggests)
  (let ((buf (langtool--correction-buffer)))
    (delete-other-windows)
    (let ((win (split-window)))
      (set-window-buffer win buf))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert msg "\n\n")
        (cl-loop for s in suggests
                 for c across langtool--correction-keys
                 do (progn
                      (insert "(" c ") ")
                      (let ((start (point)))
                        (insert s)
                        ;; colorize suggestion.
                        ;; suggestion may contains whitespace.
                        (let ((ov (make-overlay start (point))))
                          (overlay-put ov 'face 'langtool-correction-face)))
                      (insert "\n"))
                 collect (list c s))))))

(defun langtool--correction-help ()
  (let ((help-1 "[q/Q]uit correction; [c/C]lear the colorized text; ")
        (help-2 "[i/I]gnore the rule over current session.")
        (help-3 "[e/E]dit the buffer manually")
        (help-4 "SPC skip; DEL move backward;")
        )
    (save-window-excursion
      (unwind-protect
          (let ((resize-mini-windows 'grow-only))
            (select-window (minibuffer-window))
            (erase-buffer)
            (message nil)
            ;;(set-minibuffer-window (selected-window))
            (enlarge-window 2)
            (insert (concat help-1 "\n" help-2 "\n" help-3 "\n" help-4))
            (sit-for 5))
        (erase-buffer)))))

(defun langtool--correction-buffer ()
  (get-buffer-create "*Langtool Correction*"))

;;
;; Misc UI
;;

(defun langtool--show-message-buffer (msg)
  (let ((buf (get-buffer-create langtool-error-buffer-name)))
    (with-current-buffer buf
      (erase-buffer)
      (insert msg))
    (save-window-excursion
      (display-buffer buf)
      (let* ((echo-keystrokes)
             (event (read-event)))
        (setq unread-command-events (list event))))))

;;
;; initialize
;;

(defun langtool--guess-language ()
  (let ((env (or (getenv "LANG")
                 (getenv "LC_ALL")))
        (supported-langs (langtool--available-languages))
        lang country mems)
    (and env
         (string-match "\\`\\(..\\)_\\(..\\)?" env)
         (setq lang (downcase (match-string 1 env)))
         (setq country (and (match-string 2 env)
                            (upcase (match-string 2 env)))))
    (or
     (and
      lang country
      (setq mems (member (format "%s-%s" lang country) supported-langs))
      (car mems))
     (and
      lang
      (setq mems (cl-member-if
                  (lambda (x) (string-match
                               (concat "\\`" (regexp-quote lang)) x))
                  supported-langs))
      (car mems)))))

;;
;; autoshow message
;;

(defcustom langtool-autoshow-message-function
  'langtool-autoshow-default-message
  "Function with one argument which displaying error overlays reported by LanguageTool.
These overlays hold some useful properties:
 `langtool-simple-message', `langtool-rule-id', `langtool-suggestions' .
`langtool-autoshow-default-message' is a default/sample implementations.
See the Commentary section for `popup' implementation."
  :group 'langtool
  :type '(choice
          (const nil)
          function))

(defcustom langtool-autoshow-idle-delay 0.5
  "Number of seconds while idle time to wait before showing error message."
  :group 'langtool
  :type 'number)

(defvar langtool-autoshow--current-idle-delay nil)

(defvar langtool-autoshow--timer nil
  "Hold idle timer watch every LanguageTool processed buffer.")

(defun langtool-autoshow-default-message (overlays)
  ;; Do not interrupt current message
  (unless (current-message)
    (let ((msg (langtool-simple-error-message overlays)))
      (message "%s" msg))))

(defun langtool-autoshow--maybe ()
  (when langtool-autoshow-message-function
    (let ((delay (langtool-autoshow--idle-delay)))
      (cond
       ((equal langtool-autoshow--current-idle-delay delay))
       (t
        (setq langtool-autoshow--current-idle-delay delay)
        (timer-set-idle-time langtool-autoshow--timer
                             langtool-autoshow--current-idle-delay t))))
    (condition-case err
        (let ((error-overlays (langtool--current-error-overlays)))
          (when error-overlays
            (funcall langtool-autoshow-message-function error-overlays)))
      (error
       (message "langtool: %s" err)))))

(defun langtool-autoshow--idle-delay ()
  (if (numberp langtool-autoshow-idle-delay)
      langtool-autoshow-idle-delay
    (default-value 'langtool-autoshow-idle-delay)))

(defun langtool-autoshow-ensure-timer ()
  (unless (and (timerp langtool-autoshow--timer)
               (memq langtool-autoshow--timer timer-idle-list))
    (setq langtool-autoshow--timer
          (run-with-idle-timer
           (langtool-autoshow--idle-delay) t 'langtool-autoshow--maybe)))
  (add-hook 'kill-buffer-hook 'langtool-autoshow-cleanup-timer-maybe nil t))

(defun langtool-autoshow-cleanup-timer-maybe ()
  (unless (langtool-working-p)
    (when (timerp langtool-autoshow--timer)
      (cancel-timer langtool-autoshow--timer)
      (setq langtool-autoshow--timer nil))))

;;;
;;; interactive commands
;;;

(defun langtool-read-lang-name ()
  (let ((completion-ignore-case t))
    (completing-read "Lang: "
                     (or (mapcar 'list (langtool--available-languages))
                         locale-language-names))))

(defun langtool-goto-next-error ()
  "Obsoleted function. Should use `langtool-correct-buffer'.
Go to next error."
  (interactive)
  (let ((overlays (langtool--overlays-region (point) (point-max))))
    (langtool--goto-error
     overlays
     (lambda (ov) (< (point) (overlay-start ov))))))

(defun langtool-goto-previous-error ()
  "Obsoleted function. Should use `langtool-correct-buffer'.
Goto previous error."
  (interactive)
  (let ((overlays (langtool--overlays-region (point-min) (point))))
    (langtool--goto-error
     (reverse overlays)
     (lambda (ov) (< (overlay-end ov) (point))))))

(defun langtool-show-message-at-point ()
  "Show error details at point."
  (interactive)
  (let ((ovs (langtool--current-error-overlays)))
    (if (null ovs)
        (message "No errors")
      (let ((msg (langtool-details-error-message ovs)))
        (langtool--show-message-buffer msg)))))

(defun langtool-show-brief-message-at-point ()
  "Show error brief message at point."
  (interactive)
  (let ((msgs (langtool--current-error-messages)))
    (if (null msgs)
        (message "No errors")
      (langtool--show-message-buffer
       (mapconcat 'identity msgs "\n")))))

(defun langtool-check-done ()
  "Finish LanguageTool process and cleanup existing colorized texts."
  (interactive)
  (langtool--cleanup-process)
  (force-mode-line-update)
  (message "Cleaned up LanguageTool."))

;;;###autoload
(defalias 'langtool-check 'langtool-check-buffer)

;;;###autoload
(defun langtool-check-buffer (&optional lang)
  "Check context current buffer and light up errors.
Optional \\[universal-argument] read LANG name.

You can change the `langtool-default-language' to apply all session.
Restrict to selection when region is activated.
"
  (interactive
   (when current-prefix-arg
     (list (langtool-read-lang-name))))
  (langtool--check-command)
  ;; probablly ok...
  (let* ((file (buffer-file-name))
         (region-p (langtool-region-active-p))
         (begin (and region-p (region-beginning)))
         (finish (and region-p (region-end))))
    (when region-p
      (deactivate-mark))
    (unless langtool-temp-file
      (setq langtool-temp-file (make-temp-file "langtool-")))
    ;; create temporary file to pass the text contents to LanguageTool
    (when (or (null file)
              (buffer-modified-p)
              region-p
              ;; 1 is dos EOL style, this must convert to unix
              (eq (coding-system-eol-type buffer-file-coding-system) 1))
      (save-restriction
        (widen)
        (let ((coding-system-for-write
               ;; convert EOL style to unix (LF).
               ;; dos (CR-LF) style EOL may destroy position of marker.
               (coding-system-change-eol-conversion
                buffer-file-coding-system 'unix)))
          ;; BEGIN nil means entire buffer
          (write-region begin finish langtool-temp-file nil 'no-msg))
        (setq file langtool-temp-file)))
    (langtool--invoke-process file begin finish lang)
    (force-mode-line-update)))

;;;###autoload
(defun langtool-switch-default-language (lang)
  "Switch `langtool-read-lang-name' to LANG"
  (interactive (list (langtool-read-lang-name)))
  (setq langtool-default-language lang)
  (message "Now default language is `%s'" lang))

(defun langtool-correct-buffer ()
  "Execute interactive correction after `langtool-check'"
  (interactive)
  (let ((ovs (langtool--overlays-region (point-min) (point-max))))
    (if (null ovs)
        (message "No error found. %s"
                 (substitute-command-keys
                  (concat
                   "Type \\[langtool-check-done] to finish checking "
                   "or type \\[langtool-check] to re-check buffer")))
      (barf-if-buffer-read-only)
      (langtool--correction ovs))))

(defun langtool-toggle-debug ()
  "Toggle LanguageTool debugging."
  (interactive)
  (setq langtool--debug (not langtool--debug))
  (if langtool--debug
      (message "LanguageTool debug ON.")
    (message "LanguageTool debug off.")))

;;;
;;; initialize
;;;

;; initialize custom variables guessed from environment.
(let ((mt (langtool--guess-language)))
  (unless langtool-mother-tongue
    (setq langtool-mother-tongue mt))
  (unless langtool-default-language
    (setq langtool-default-language (or mt "en-GB"))))

(provide 'langtool)

;;; langtool.el ends here
