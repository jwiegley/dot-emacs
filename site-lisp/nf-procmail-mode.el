;;; nf-procmail-mode.el --- major mode for editing procmail recipe files

;; Copyright (C) 2006 Noah S. Friedman

;; Author: Noah Friedman <friedman@splode.com>
;; Maintainer: friedman@splode.com
;; Created: 2006-05-15

;; $Id: nf-procmail-mode.el,v 1.1 2006/06/20 20:51:22 friedman Exp $

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, you can either send email to this
;; program's maintainer or write to: The Free Software Foundation,
;; Inc.; 51 Franklin Street, Fifth Floor; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This is a mode for editing .procmailrc.
;; There are many others like it but this one is mine.

;;; Code:

(require 'font-lock)
(require 'derived)

(defgroup nf-procmail nil
  "procmail-related applications."
  :prefix "nf-procmail-"
  :group  'languages)

(defconst nf-procmail-mode-builtin-variable-keywords
  '("COMSAT"      "LOCKEXT"      "MSGPREFIX"          "SHIFT"
    "DEFAULT"     "LOCKFILE"     "NORESRETRY"         "SUSPEND"
    "DELIVERED"   "LOCKSLEEP"    "ORGMAIL"            "SWITCHRC"
    "DROPPRIVS"   "LOCKTIMEOUT"  "PROCMAIL_OVERFLOW"  "TIMEOUT"
    "EXITCODE"    "LOG"          "PROCMAIL_VERSION"   "TRAP"
    "HOST"        "LOGABSTRACT"  "SENDMAIL"           "UMASK"
    "INCLUDERC"   "LOGFILE"      "SENDMAILFLAGS"      "VERBOSE"
    "LASTFOLDER"  "MAILDIR"      "SHELLFLAGS"
    "LINEBUF"     "MATCH"        "SHELLMETAS"))

(defconst nf-procmail-mode-regexp-token-keywords
  '("FROM_DAEMON" "FROM_MAILER" "TO" "TO_"))

;; Not sure if these rules are optimal from a scanning perspective
(defconst nf-procmail-mode-font-lock-keywords
  (let ((kwre   (regexp-opt nf-procmail-mode-builtin-variable-keywords))
        (rekwre (regexp-opt nf-procmail-mode-regexp-token-keywords)))

    `(;; assignments of builtin variables
      (,(format "^\\s-*\\(%s\\)=" kwre)
       (1 font-lock-keyword-face))

      ;; other variable assignments
      ("^\\s-*\\(\\w+\\)="
       (1 font-lock-variable-name-face))

      ;; reference to builtin variables
      (,(format "\\${?\\(%s\\)}?\\>" kwre)
       (1 font-lock-keyword-face))

      ;; reference other variables
      ("\\${?\\(\\w+\\)}?\\>"
       (1 font-lock-variable-name-face))

      ("^\\s-*\\(:0?[^:\n]*:?\\)\\(.*\\)?" ;; start of rules
       (1 font-lock-function-name-face nil t) ; flags
       (2 font-lock-doc-face nil t))          ; optional lockfile

      ;; regular expression lines
      ("^\\s-*\\*\\(?:\\s-+[0-9^]*\\)?\\s-+\\(?:[!$<>]\\)?"
       . ((0 font-lock-constant-face)

          (".*"
           nil nil
           (0 font-lock-preprocessor-face))

          ("\\b\\([A-Z][A-Za-z0-9]*\\(?:-[A-Za-z0-9]+\\)*\\):"
           (beginning-of-line) nil
           (1 font-lock-type-face t))

          (,(format "\\(\\^\\(?:%s\\)\\)\\(:?\\)" rekwre)
           (beginning-of-line) nil
           (1 font-lock-keyword-face t)
           (2 'trailing-whitespace   t))

          ("\\\\/"
           (beginning-of-line) nil
           (0 font-lock-warning-face t)
           (0 'bold prepend))))

      ("`.*?`"
       (0 font-lock-string-face keep))

      ("[\t]+" ;; emphasize literal tabs in non-comments
       (0 font-lock-warning-face prepend)
       (0 'underline             prepend))

      ("#.*"
       (0 font-lock-comment-face t)))))

;;;###autoload
(define-derived-mode nf-procmail-mode text-mode "Procmail"
  "Major mode for editing procmail recipes."
  :group 'nf-procmail

  (setq comment-start      "#")
  (setq comment-start-skip "#\\W*")

  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '((nf-procmail-mode-font-lock-keywords)
			     nil nil ((?\_ . "w")))))

;;;###autoload (add-to-list 'auto-mode-alist '("\\.?procmail\\.?rc\\'" . nf-procmail-mode))

(provide 'nf-procmail-mode)

;; nf-procmail-mode.el ends here
