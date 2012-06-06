;;; fetchmail-mode.el --- Mode for editing .fetchmailrc files  -*- Emacs-Lisp -*-
;;
;; Created:    <Mon Oct 30 20:13:15 EST 2000>
;; Time-stamp: <17.02.2001 17:59:43>
;; Version:    0.1
;; Keywords:   fetchmail,config
;; Author:     Alex Shinn <foof@debian.org>
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public
;; License along with this program; if not, write to the Free
;; Software Foundation, Inc., 59 Temple Place, Suite 330, Boston,
;; MA 02111-1307 USA
 
;; Commentary:
;;
;; This file provides a major mode for editing .fetchmailrc files.
;; It offers syntax highlighting and indentation.
;;
;; To use it, put the following in your .emacs:
;;
;; (autoload 'fetchmail-mode "fetchmail-mode.el" "Mode for editing .fetchmailrc files" t)
;;
;; You may also want something like:
;;
;; (setq auto-mode-alist
;;       (append '(("\..fetchmailrc$" . fetchmail-mode))
;;               auto-mode-alist))
 
;; Create mode-specific tables.
(defvar fetchmail-mode-syntax-table nil
  "Syntax table used while in fetchmail-mode" )
(if fetchmail-mode-syntax-table
    ()              ; Do not change the table if it is already set up.
  (setq fetchmail-mode-syntax-table (make-syntax-table))
  (modify-syntax-entry ?\\ "\\   " fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\,  "." fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\:  "." fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\;  "." fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\"  "\"" fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\'  "\"" fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\n  "> " fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\#  "< " fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\( "()   " fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\) ")(   " fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\[ "(]   " fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\] ")[   " fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\{ "(}   " fetchmail-mode-syntax-table)
  (modify-syntax-entry ?\} "){   " fetchmail-mode-syntax-table)
  )
 
(defvar fetchmail-mode-map nil
  "Keymap used in fetchmail-mode" )
 
(if fetchmail-mode-map nil
  (setq fetchmail-mode-map (make-sparse-keymap))
  (define-key fetchmail-mode-map "\t" 'fetchmail-complete)
  (define-key fetchmail-mode-map "\C-c\C-c" 'comment-region) )
(defvar fetchmail-mode-hook nil
  "Hooks to run in fetchmail-mode" )
 
(defvar fetchmail-keywords nil
  "Keywords used for fetchmail-mode" )
 
(unless fetchmail-keywords
   (setq fetchmail-keywords
          '("poll" "skip" "via" "in" "proto" "protocol" "uidl" "no"
"port" "auth" "authenticate" "timeout" "envelope" "qvirtual" "envelope"
"aka" "localdomains" "interface" "monitor" "dns" "user" "username" "is"
"folder" "pass" "password" "smtp" "smtphost" "smtpaddress" "antispam"
"mda" "pre" "preconnect" "post" "postconnect" "keep" "flush" "fetchall"
"rewrite" "forcecr" "stripcr" "pass8bits" "dropstatus" "limit"
"fetchlimit" "batchlimit" "expunge" "pop2" "POP2" "pop3" "POP3" "imap"
"IMAP" "imap-k4" "IMAP-K4" "apop" "APOP" "rpop" "RPOP" "kpop" "KPOP"
"etrn" "ETRN" "login" "kerberos" "kerberos_v5" "logfile" "daemon"
"syslog" "invisible" "and" "with" "has" "wants" "options" "here" "there"
"aka" "set")))
 
(defvar fetchmail-keyword-table nil
  "Completion table for fetchmail-mode" )
(unless fetchmail-keyword-table
  (setq fetchmail-keyword-table (make-vector 8 0))
  (mapcar (lambda (x) (intern x fetchmail-keyword-table))
          fetchmail-keywords))
 
(defvar fetchmail-font-lock-keywords nil
  "Default expressions to highlight in fetchmail-mode" )
 
(unless fetchmail-font-lock-keywords
  (setq fetchmail-font-lock-keywords
        (list (list (concat "\\b" (regexp-opt
                                   fetchmail-keywords t) "\\b")
                    0 'font-lock-keyword-face ))))
 
(defun fetchmail-complete ()
  "Tab completion for fetchmail-mode"
  (interactive)
  (let* ((end (point))
         (beg (save-excursion
                (skip-syntax-backward "w")
                (point)))
         (pattern (buffer-substring beg end))
         (table fetchmail-keyword-table)
         (completion (try-completion pattern table)))
    (cond ((eq completion t))
          ((null completion)
           (error "Can't find completion for \"%s\"" pattern))
          ((not (string-equal pattern completion))
           (delete-region beg end)
           (insert completion))
          (t
           (message "Making completion list...")
           (let ((list (all-completions pattern table)))
             (if (fboundp 'prettify)
                 (setq list (funcall 'prettify list)))
             (with-output-to-temp-buffer "*Help*"
               (display-completion-list list)))
           (message "Making completion list...%s" "done")))))
 
;;;###autoload 
(defun fetchmail-mode ()
  "Mode for editing .fetchmailrc files"
  (interactive)
  (kill-all-local-variables)
  (use-local-map fetchmail-mode-map)    ; This provides the localkeymap.
  (setq mode-name "Fetchmail")          ; This name goes into themodeline.
  (setq major-mode 'fetchmail-mode)     ; Used by `describe-mode'
  (run-hooks 'fetchmail-mode-hook)      ; Run each time mode is called
  (set-syntax-table fetchmail-mode-syntax-table)
 
  ;; -cc-
  ;; Font lock support
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(fetchmail-font-lock-keywords nil t))
 
  (setq comment-start "#")
  )
 
 
 
(provide 'fetchmail-mode)
;;; fetchmail-mode.el ends here
