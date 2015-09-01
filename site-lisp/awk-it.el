;;; awk-it.el --- Run AWK interactively on region!

;; Copyright (C) 2013, by Igor Sikaček

;; Author: Igor Sikaček <isikacek@gmail.com>
;; Maintainer: Igor Sikaček <isikacek@gmail.com>
;; Created: 17 Sep 2013
;; Version: 0.77
;; Keywords: awk

;; This file is not part of Emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; AWK it! allows you to see AWK output as you are typing the script;
;; it sends selected region to awk and uses yasnippet as interactive UI.

;; There are 3 modes of AWK code: simplified syntax(default, see below),
;; single line AWK syntax (regular AWK syntax but only inside the default
;; match) and raw AWK syntax(full AWK code). AWK it! can transfrom code
;; from one mode to another(not perfect, but it will make an effort) and
;; there is also support for multiple lines. Data is expanded with selected
;; yasnippet expand keybinding.

;;; Usage:

;; Simplest usage is selecting region and running M-x awk-it.
;; Default field separator is space. AWK it! matches every non empty
;; row in region ($0 !~ /^$/).

;; After invoking command buffer will change to show the following interface:

;; Data: <First line with most fields>
;; AWK pattern: <AWK code; may be multiple lines without extra formatting>
;; <AWK output>

;; Example:

;; From:

;; John 26 London
;; Mark 27 Seattle 50
;; Scott 26 Sydney

;; to (ignoring the extra field in example pattern):

;; Data: Mark 27 Seattle 50
;; AWK pattern: <person name="$1" age="$2">
;;     <location>$3</location>
;; </person>
;; <person name="John" age="26">
;;     <location>London</location>
;; </person>
;; <person name="Mark" age="27">
;;     <location>Seattle</location>
;; </person>
;; <person name="Scott" age="26">
;;     <location>Sydney</location>
;; </person>

;; and after expansion:

;; <person name="John" age="26">
;;     <location>London</location>
;; </person>
;; <person name="Mark" age="27">
;;     <location>Seattle</location>
;; </person>
;; <person name="Scott" age="26">
;;     <location>Sydney</location>
;; </person>

;; The expanded lines are automaticaly indented. Buffer undo goes back to
;; before awk-it invocation (both options can be changed).

;; During completion the folowing options are available:
;;   - C-c s - change field separator
;;   - C-c t - toggle space and tab trimming around custom field separator
;;   - C-c <up> - next AWK it! mode (simple -> single -> raw -> simple -> ...)
;;   - C-c <down> - previous AWK it! mode (raw -> single -> simple -> raw ...)

;; After completion you can run:
;;   - M-x awk-it-to-kill-ring - copies last AWK code to kill ring
;;   - M-x awk-it-to-file - copies last AWK code(raw or converted to raw) to file

;; Simplified AWK code differs from regular in that it:
;;   - prints code(print "<code>")
;;   - escapes double and single quotes (latter for shell interaction)
;;   - escapes newline
;;   - concatenates fields with rest of the text

;; The single mode is regular AWK code run for each default match. The previous
;; example written in single AWK code would be:

;; print "<person name=\"" $1 "\" age=\"" $2 "\">\n\
;;     <location>" $3 "</location>\n\
;; </person>"

;; The raw mode is raw, or full, AWK code needed for data processing. The previous
;; example would be:

;; $0 !~ /^$/ {
;;     print "<person name=\"" $1 "\" age=\"" $2 "\">\n\
;;     <location>" $3 "</location>\n\
;; </person>";
;; }
;;
;; /^$/ { print }

;; AWK it! can also be invoked with every mode as starting mode, with custom
;; separator, with contents of file inserted in interactive UI code field(in
;; raw mode), or automatically process region with contents of file(as raw AWK).

;; Combining everything the following functions are available:
;;   - awk-it                             - basic AWK it! - starts in simple mode
;;   - awk-it-with-separator              - simple mode with custom field separator
;;   - awk-it-single                      - single mode AWK it!
;;   - awk-it-single-with-separator       - single mode with custom field separator
;;   - awk-it-raw                         - AWK it! using raw(full) AWK syntax
;;   - awk-it-file                        - automatically transform with AWK file
;;   - awk-it-with-file                   - raw mode with code from AWK file
;;   - awk-it-to-kill-ring                - place last AWK code in kill ring
;;   - awk-it-to-file                     - output last raw AWK code to file

;; Also AWK it! can be customized in External -> Awk it:
;;   - awk-it-load-hook; Hook that gets run after the AWK it! has been loaded
;;   - awk-it-default-separator           - default AWK field separator - ' '
;;   - awk-it-default-row-filter          - default AWK row filter - '$0 !~ /^$/'
;;   - awk-it-file-first-line             - first line inserted in AWK file
;;   - awk-it-default-mode                - default starting mode for awk-it
;;   - awk-it-undo                        - toggles if undo ignores AWK it! edits
;;   - awk-it-indent                      - toggles is expanded text will be indented
;;   - awk-it-extra-awk-code              - extra AWK code that is inserted in raw AWK
;;   - awk-it-toggle-trim-keybinding      - keybinding for toggling trimming
;;   - awk-it-field-separator-keybinding  - keybinding for change field separator
;;   - awk-it-next-mode-keybinding        - keybinding for next mode
;;   - awk-it-previous-mode-keybinding    - keybinding for previousmode

;;; Change Log:

;; 2012.09.10. - 0.5
;;   first version
;; 2013.01.26. - 0.75
;;   fix:
;;     - extra newline at end
;;     - better ' handling
;;     - \ field separator
;;   feature:
;;     - toggle trimming around separator while in completion
;;     - switch field separator while in completion
;;     - auto indent after expansion
;;     - 3 types of awk code: simple, single, raw
;;     - load code from file
;;     - save code to kill-ring and file(raw)
;;     - undo before awk-it
;;     - extra functions variable
;; 2013.01.31. - 0.76
;;   fix:
;;     - minor dependency fix
;; 2013.09.17. - 0.77
;;   fix:
;;     - minor dependency fix

;;; Code:


(require 'yasnippet)

(require 'cl)


(defgroup awk-it nil
  "Run awk interactively on region."
  :version "0.77"
  :group 'external)

(defcustom awk-it-load-hook nil
  "*Hook that gets run after the awk-it has been loaded."
  :type 'hook
  :group 'awk-it)

(defcustom awk-it-default-separator " "
  "*Default AWK field separator - if nil AWK default is used."
  :type 'string
  :group 'awk-it)

(defcustom awk-it-default-row-filter "$0 !~ /^$/"
  "*Default AWK row filter - if nil '$0 !~ /^$/' is used."
  :type 'string
  :group 'awk-it)

(defcustom awk-it-file-first-line "#!/bin/awk"
  "*First line inserted when writing AWK file."
  :type 'string
  :group 'awk-it)

(defcustom awk-it-default-mode 1
  "*Default AWK it! mode (1 - simplified; 2 - raw single match; 3 - full raw)."
  :type 'number
  :group 'awk-it)

(defcustom awk-it-undo t
  "*AWK it! undo; after expansion undo to before awk-it, nil to disable."
  :type 'boolean
  :group 'awk-it)

(defcustom awk-it-indent t
  "*Toggles if epanded data should be indented."
  :type 'boolean
  :group 'awk-it)

(defcustom awk-it-extra-awk-code nil
  "*Extra AWK code that AWK it! will insert into final script."
  :type 'string
  :group 'awk-it)

(defcustom awk-it-toggle-trim-keybinding "C-c t"
  "*AWK it! toogle field separator trim keybinding."
  :type 'string
  :group 'awk-it)

(defcustom awk-it-field-separator-keybinding "C-c s"
  "*AWK it! field separator change keybinding."
  :type 'string
  :group 'awk-it)

(defcustom awk-it-next-mode-keybinding "C-c <up>"
  "*AWK it! next mode change keybinding."
  :type 'string
  :group 'awk-it)

(defcustom awk-it-previous-mode-keybinding "C-c <down>"
  "*AWK it! previous mode change keybinding."
  :type 'string
  :group 'awk-it)


(defvar awk-it-fs awk-it-default-separator "AWK field separator.")

(defvar awk-it-type awk-it-default-mode "Type of code (1 - simplified; 2 - raw single match; 3 - full raw).")

(defvar awk-it-trim nil "Trim spaces/tabs around field separator.")

(defvar awk-it-old-trim-keybinding nil "Holds old command called by toggle trim keystroke.")

(defvar awk-it-old-fs-keybinding nil "Holds old command called by change field separator keystroke.")

(defvar awk-it-old-next-mode-keybinding nil "Holds old command called by next mode keystroke.")

(defvar awk-it-old-previous-mode-keybinding nil "Holds old command called by previous mode keystroke.")

(defvar awk-it-beginning nil "Starting point od data/expansion.")

(defvar awk-it-data nil "Data for AWK to process.")

(defvar awk-it-code nil "AWK code to transform data.")

(defvar awk-it-point nil "Begining of data/head.")

(defvar awk-it-count 0 "Number of chars of expansion.")

(defvar awk-it-undo-before nil "Buffer undo list before AWK it!")


(defconst AWK-IT-M-STRING "\"\\(\\\\.+\\|[^\"]+\\)\"" "Regex match for strings.")

(defconst AWK-IT-M-STRING-REPLACEMENT-PREFIX "___" "Prefix for string replacement token.")


;;;###autoload
(defun awk-it (beg end)
  "Run AWK for each line between point and mark."
  (interactive "r")
  (setq awk-it-type 1)
  (awk-it-full beg end 'awk-it-process awk-it-default-separator))

;;;###autoload
(defun awk-it-with-separator (beg end fs)
  "Run AWK for each line between point and mark, specifying custom
field separator."
  (interactive "r\nsAWK it! field separator: ")
  (setq awk-it-type 1)
  (awk-it-full beg end 'awk-it-process fs))

;;;###autoload
(defun awk-it-single (beg end)
  "Run AWK code(single) for each line between point and mark."
  (interactive "r")
  (setq awk-it-type 2)
  (awk-it-full beg end 'awk-it-process " "))

;;;###autoload
(defun awk-it-single-with-separator (beg end fs code)
  "Run AWK code(single) for each line between point and mark,
specifying custom field separator."
  (interactive "r\nsAWK it! field separator: ")
  (setq awk-it-type 2)
  (awk-it-full beg end 'awk-it-process fs))

;;;###autoload
(defun awk-it-raw (beg end)
  "Run AWK code(raw) for each line between point and mark."
  (interactive "r")
  (setq awk-it-type 3)
  (awk-it-full beg end 'awk-it-process awk-it-default-separator))

;;;###autoload
(defun awk-it-file (beg end file)
  "Run AWK code on a region from FILE(auto expands)."
  (interactive "r\nfAWK file: ")
  (delete-region beg end)
  (insert (shell-command-to-string (concat "echo \"" awk-it-data "\" | awk -f " file))))

;;;###autoload
(defun awk-it-with-file (beg end file)
  "Run AWK it! with code from FILE(inserts code into template field)."
  (interactive "r\nfAWK file: ")
  (setq awk-it-code
          (with-temp-buffer
            (insert-file-contents file)
            (buffer-string))
        awk-it-type 3)
  (awk-it-full beg end 'awk-it-process " " t))

;;;###autoload
(defun awk-it-to-file (file)
  "Save last AWK it! code to file(as raw AWK code)."
  (interactive "GAWK file: ")
  (with-temp-buffer
    (insert (concat
      awk-it-file-first-line "

"
      (replace-regexp-in-string "\" *auto_quote *\"" "'"
        (cond
         ((= awk-it-type 1)
          (awk-it-single-2-raw (awk-it-simple-2-single awk-it-code)))
         ((= awk-it-type 2)
          (awk-it-single-2-raw awk-it-code))
         ((= awk-it-type 3)
          awk-it-code)))))
    (write-file file)))

;;;###autoload
(defun awk-it-to-kill-ring ()
  "Save last AWK it! code to kill-ring(as specified by mode)."
  (interactive)
  (kill-new awk-it-code))

;;;###autoload
(defun awk-it-version ()
  "Returns current AWK it! version."
  "0.77")


(defun awk-it-fs ()
  "Returns actual AWK field separator to be used."
  (let ((fs-temp (cond
                  ((string= awk-it-fs "\\") "\\\\")
                  (t awk-it-fs))))
    (if awk-it-trim (concat "[ \\t]*" fs-temp "[ \\t]*") fs-temp)))


(defun awk-it-full (beg end func &optional fs file)
  "AWK it! - full func.; captures data and sets up yasnippet."
  (when awk-it-undo (setq buffer-undo-list (cons 'AWK-IT buffer-undo-list)))
  (save-window-excursion
    (setq awk-it-beginning beg
          awk-it-fs fs)

    (setq awk-it-old-next-mode-keybinding (local-key-binding (awk-it-macro-expand-value kbd awk-it-next-mode-keybinding)))
    (local-set-key (awk-it-macro-expand-value kbd awk-it-next-mode-keybinding) 'awk-it-next-type)

    (setq awk-it-old-previous-mode-keybinding (local-key-binding (awk-it-macro-expand-value kbd awk-it-previous-mode-keybinding)))
    (local-set-key (awk-it-macro-expand-value kbd awk-it-previous-mode-keybinding) 'awk-it-previous-type)

    (setq awk-it-old-trim-keybinding (local-key-binding (awk-it-macro-expand-value kbd awk-it-toggle-trim-keybinding)))
    (local-set-key (awk-it-macro-expand-value kbd awk-it-toggle-trim-keybinding)
      (lambda ()
        (interactive)
        (setq awk-it-trim (not awk-it-trim))
        (let ((s (car (yas--snippets-at-point))))
          (if s (yas--update-mirrors s)))))

    (setq awk-it-old-fs-keybinding (local-key-binding (awk-it-macro-expand-value kbd awk-it-field-separator-keybinding)))
    (local-set-key (awk-it-macro-expand-value kbd awk-it-field-separator-keybinding)
      (lambda (x)
        (interactive "sAWK it! field separator: ")
        (setq awk-it-trim nil
              awk-it-fs x)
        (let ((s (car (yas--snippets-at-point))))
          (if s (yas--update-mirrors s)))))

    (setq awk-it-data (buffer-substring beg end)
          awk-it-point beg)
    (add-hook 'yas/after-exit-snippet-hook 'awk-it-yas-completed nil t)
    (yas/expand-snippet (concat
      "Data: " (awk-it-get-line-with-max-separators beg end) "
AWK pattern: ${1:"(if file (replace-regexp-in-string "\\(\\$\\|`\\)" "\\\\\\1" awk-it-code) "pattern") "}
${1:$(" (symbol-name func) " yas-text)}") beg end)))


(defun awk-it-process (code)
  "Sends AWK code and data to the shell."
  (let ((result ""))
    (setq awk-it-code code
          result (shell-command-to-string (concat
      "echo \"" awk-it-data "\" | awk -v auto_quote=\"'\" ' "
      (replace-regexp-in-string "'" "\" auto_quote \""
        (cond
         ((= awk-it-type 1)
          (awk-it-single-2-raw (awk-it-simple-2-single code)))
         ((= awk-it-type 2)
          (awk-it-single-2-raw code))
         ((= awk-it-type 3)
          code)))
      " ' ")))
    (when (< 0 (length result))
      (setq result (substring result 0 (- (length result) 1))))
    (setq awk-it-count (length result))
    result))


(defun awk-it-yas-completed ()
  "After yas completion hook - removes header from buffer and itself
from hook."
  (when awk-it-point
    (goto-char awk-it-point)
    (kill-line (+ 2 (count ?
      (append awk-it-code nil)))))
  (local-set-key (awk-it-macro-expand-value kbd awk-it-toggle-trim-keybinding) awk-it-old-trim-keybinding)
  (local-set-key (awk-it-macro-expand-value kbd awk-it-field-separator-keybinding) awk-it-old-fs-keybinding)
  (local-set-key (awk-it-macro-expand-value kbd awk-it-next-mode-keybinding) awk-it-old-next-mode-keybinding)
  (local-set-key (awk-it-macro-expand-value kbd awk-it-previous-mode-keybinding) awk-it-old-previous-mode-keybinding)
  (remove-hook 'yas/after-exit-snippet-hook 'awk-it-yas-completed t)
  (when awk-it-indent
    (indent-region awk-it-beginning (+ awk-it-beginning awk-it-count)))
  (when awk-it-undo
    (setq buffer-undo-list
      (let ((found nil))
        (loop for x in buffer-undo-list
              when (eql x 'AWK-IT) do (setq found t)
              when (and (or found x) (not (eql x 'AWK-IT)))
              collect x)))))


(defun awk-it-update-yas-field ()
  "Updates yasnippet field(AWK code)."
  (let ((snippet (car (yas--snippets-at-point))))
    (when snippet
        (let ((field (car (yas--snippet-fields snippet))))
          (goto-char (yas--field-start field))
          (insert awk-it-code)
          (delete-region (point) (yas--field-end field))))))


(defun awk-it-next-type ()
  "Converts AWK code to next type(mode)."
  (interactive)
  (when (= awk-it-type 3)
    (setq awk-it-type 0))
  (setq awk-it-type (+ awk-it-type 1)
        awk-it-code (cond
    ((= awk-it-type 1)
     (awk-it-single-2-simple (awk-it-raw-2-single awk-it-code)))
    ((= awk-it-type 2)
     (awk-it-simple-2-single awk-it-code))
    ((= awk-it-type 3)
     (awk-it-single-2-raw awk-it-code))))
  (let ((s (car (yas--snippets-at-point))))
    (awk-it-update-yas-field)
    (if s (yas--update-mirrors s))))


(defun awk-it-previous-type ()
  "Converts AWK code to previous type(mode)."
  (interactive)
  (when (= awk-it-type 1)
    (setq awk-it-type 4))
  (setq awk-it-type (- awk-it-type 1)
        awk-it-code (cond
    ((= awk-it-type 1)
     (awk-it-single-2-simple awk-it-code))
    ((= awk-it-type 2)
     (awk-it-raw-2-single awk-it-code))
    ((= awk-it-type 3)
     (awk-it-single-2-raw (awk-it-simple-2-single awk-it-code)))))
  (let ((s (car (yas--snippets-at-point))))
    (awk-it-update-yas-field)
    (if s (yas--update-mirrors s))))


; ---[ AWK code functions ]-------------------------------------------------------------------------------------------------

; Collection of not well thought out and hastily put together AWK functions.


(defun awk-it-simple-2-single (code)
  "Converts simple CODE to single. "
  (awk-it-n-regex-replace
    (concat "print \""
      (awk-it-n-regex-replace code
        '(("\""                     "\\\\\"")
          ("\\(\\$[1234567890]+\\)" "\" \\1 \"")
          ("
" "\\\\n\\\\
")
          ))
      "\"")
    '(("print *\"\" *" "print ")
      (" *[^\\]\"\" *$" ""))))


(defun awk-it-single-2-raw (code)
  "Converts single CODE to raw."
  (let ((fs (awk-it-fs))
           (EL "
"))
    (concat
      EL
      (if (not (string= fs " ")) (concat "BEGIN {" EL "    FS=\"" fs "\";" EL "}" EL EL))
      (if awk-it-default-row-filter awk-it-default-row-filter "$0 !~ /^$/")
      " { " EL
      "    " code (unless (string-match "; *$" code)  ";") EL
      "}" EL
      EL
      "/^$/ { print }"
      (when awk-it-extra-awk-code (concat EL EL awk-it-extra-awk-code)))))


(defun awk-it-raw-2-single (code)
  "Converts raw CODE to single."
  (destructuring-bind (fs scode) (awk-it-find-single code)
    (setq awk-it-fs fs)
    scode))


(defun awk-it-single-2-simple (code)
  "Converts single CODE to simple."
  (replace-regexp-in-string "" "\\1"
    (awk-it-n-regex-replace (replace-regexp-in-string "^ *print *\\(.*\\)$" "\\1" code)
      '(("
" "#AWK-IT-NEWLINE#")
        (" *\"\\(.*\\)\" *" "\\1")
        ("; *$" "")
        (" *$" "")
        ("\\\\\""    "\"")
        ("\" \\($[1234567890]+\\) \"" "\\1")
        ("\\\\n\\\\" "")
        ("#AWK-IT-NEWLINE#" "
")))))


(defun awk-it-flat-clean-awk (string)
  "Removes comments and newlines from AWK code in STRING."
  (apply 'concat
    (remove-if (lambda (x) (string= "" x))
      (mapcar (lambda (x) (awk-it-n-regex-replace x
        '((" *#.*" "")
          ("^ *\\(.*\\) *$" "\\1"))))
        (split-string string "
" t)))))


(defun awk-it-extract-awk-matches (string)
  "Retuns list of (match code) pairs from AWK code in STRING."
  (let ((found nil)
        (lpos 0)
        (pos 0)
        (pc 0)
        (curr-match ""))
    (while (string-match "[{}]" string pos)
      (setq pos (match-end 0))
      (if (and (match-beginning 0)
               (string= "{" (substring string (match-beginning 0) (match-end 0))))
          (progn
            (when (< pc 1)
              (setq curr-match (substring string lpos (- pos 1))
                    lpos (- pos 1)))
            (setq pc (+ 1 pc)))
        (setq pc (- pc 1))
        (when (< pc 1)
          (setq found (append found (list (list curr-match (substring string lpos pos))))
                lpos pos))))
    found))


(defun awk-it-find-single (string)
  "Finds field separator (or returns default) and default row filter
code (if any) from AWK code in STRING."
  (let* ((strings (awk-it-extract-strings string))
        (matches (awk-it-extract-awk-matches (awk-it-flat-clean-awk (awk-it-n-regex-replace string
          (mapcar*
           (lambda (x y)
             (list (concat "\"" (replace-regexp-in-string "\\\\" "\\\\\\\\" y) "\"") (concat AWK-IT-M-STRING-REPLACEMENT-PREFIX (number-to-string x))))
           (number-sequence 0 (length strings))
           strings) t))))
        (fs awk-it-default-separator)
        (code ""))
    (mapc (lambda (x)
      (destructuring-bind (a b) x
        (when (string-match " *BEGIN *" a)
          (when (string-match (concat "FS *=[^;\"]*" AWK-IT-M-STRING-REPLACEMENT-PREFIX "\\([1234567890]+\\)") b)
            (setq fs (nth (string-to-number
                           (and (match-beginning 1)
                                (substring b (match-beginning 1) (match-end 1)))) strings))))
        (when (string-match (concat " *" awk-it-default-row-filter " *") a)
          (setq code (substring b 1 (- (length b) 1)))))) matches)
    (list fs (awk-it-return-strings code strings))))



; ---[ Utility ]------------------------------------------------------------------------------------------------------------


(defun awk-it-extract-strings (string &optional start)
  "Extracts substrings from STRING. Starts from START or 0."
  (unless start (setq start 0))
  (if (string-match AWK-IT-M-STRING string start)
      (let ((head (match-string 1 string) ))
        (append (list head) (awk-it-extract-strings string (+ (match-end 0)))))
    nil))


(defun awk-it-return-strings (string strings)
  "Replaces substring placeholders from STRING with values
in STRINGS."
  (awk-it-n-regex-replace string
    (mapcar*
     (lambda (x y)
       (list (concat AWK-IT-M-STRING-REPLACEMENT-PREFIX (number-to-string x)) (concat "\"" y "\"")))
     (number-sequence 0 (length strings))
     strings) t))


(defun awk-it-get-line-with-max-separators (beg end &optional separator)
  "Returns line with max # of separators inside region."
  (save-window-excursion
    (save-restriction
      (narrow-to-region beg end)
      (goto-char (point-min))
      (let ((count 0)
            (final-point (point)))
        (while (not (eobp))
          (let ((x (count-matches (if (not separator) " " separator) (line-beginning-position) (line-end-position))))
            (when (< count x)
              (setq count x
                    final-point (line-beginning-position))))
          (forward-line))
        (goto-char final-point)
        (buffer-substring (line-beginning-position) (line-end-position))))))


(defun awk-it-n-regex-replace (string list &optional literal)
  "Makes multiple regex replacements using ((search replace) . )
syntax."
  (if list
      (destructuring-bind ((a b) . rest) list
        (awk-it-n-regex-replace (replace-regexp-in-string a b string nil literal) rest literal))
    string))


(defmacro awk-it-macro-expand-value (macro &rest list)
  "Expands MACRO with values of variables in LIST."
  `(,(symbol-function macro) ,@(mapcar 'symbol-value list)))


(provide 'awk-it)


(run-hooks 'awk-it-load-hook)


;;; awk-it.el ends here
