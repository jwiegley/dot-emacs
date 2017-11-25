;;; py-report-comint-variable-setting.el ---

;; Copyright (C) 2015  Andreas Röhler

;; Author: Andreas Röhler <andreas.roehler@easy-emacs.de>

;; Keywords: languages, processes, python

;; Keywords: lisp

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

;;; Code:

(defun py-report-comint-variable-setting ()
  "Print values of comint-variables.

Used for debugging in \"*Python*\" shell buffer for example"
  (interactive)
  (with-output-to-temp-buffer "*Help*"
    (set-buffer "*Help*")
    (and (boundp 'comint-accum-marker)
	 (insert (concat "comint-accum-marker" " --> " (prin1-to-string comint-accum-marker) "\n")))
    (and (boundp 'comint-buffer-maximum-size)
	 (insert (concat "comint-buffer-maximum-size" " --> " (prin1-to-string comint-buffer-maximum-size) "\n")))
    (and (boundp 'comint-completion-addsuffix)
	 (insert (concat "comint-completion-addsuffix" " --> " (prin1-to-string comint-completion-addsuffix) "\n")))
    (and (boundp 'comint-completion-autolist)
	 (insert (concat "comint-completion-autolist" " --> " (prin1-to-string comint-completion-autolist) "\n")))
    (and (boundp 'comint-completion-fignore)
	 (insert (concat "comint-completion-fignore" " --> " (prin1-to-string comint-completion-fignore) "\n")))
    (and (boundp 'comint-completion-recexact)
	 (insert (concat "comint-completion-recexact" " --> " (prin1-to-string comint-completion-recexact) "\n")))
    (and (boundp 'comint-delimiter-argument-list)
	 (insert (concat "comint-delimiter-argument-list" " --> " (prin1-to-string comint-delimiter-argument-list) "\n")))
    (and (boundp 'comint-displayed-dynamic-completions)
	 (insert (concat "comint-displayed-dynamic-completions" " --> " (prin1-to-string comint-displayed-dynamic-completions) "\n")))
    (and (boundp 'comint-dynamic-complete-functions)
	 (insert (concat "comint-dynamic-complete-functions" " --> " (prin1-to-string comint-dynamic-complete-functions) "\n")))
    (and (boundp 'comint-dynamic-list-completions-config)
	 (insert (concat "comint-dynamic-list-completions-config" " --> " (prin1-to-string comint-dynamic-list-completions-config) "\n")))
    (and (boundp 'comint-eol-on-send)
	 (insert (concat "comint-eol-on-send" " --> " (prin1-to-string comint-eol-on-send) "\n")))
    (and (boundp 'comint-exec-hook)
	 (insert (concat "comint-exec-hook" " --> " (prin1-to-string comint-exec-hook) "\n")))
    (and (boundp 'comint-file-name-chars)
	 (insert (concat "comint-file-name-chars" " --> " (prin1-to-string comint-file-name-chars) "\n")))
    (and (boundp 'comint-file-name-prefix)
	 (insert (concat "comint-file-name-prefix" " --> " (prin1-to-string comint-file-name-prefix) "\n")))
    (and (boundp 'comint-file-name-quote-list)
	 (insert (concat "comint-file-name-quote-list" " --> " (prin1-to-string comint-file-name-quote-list) "\n")))
    (and (boundp 'comint-get-old-input)
	 (insert (concat "comint-get-old-input" " --> " (prin1-to-string comint-get-old-input) "\n")))
    (and (boundp 'comint-history-isearch)
	 (insert (concat "comint-history-isearch" " --> " (prin1-to-string comint-history-isearch) "\n")))
    (and (boundp 'comint-history-isearch-message-overlay)
	 (insert (concat "comint-history-isearch-message-overlay" " --> " (prin1-to-string comint-history-isearch-message-overlay) "\n")))
    (and (boundp 'comint-inhibit-carriage-motion)
	 (insert (concat "comint-inhibit-carriage-motion" " --> " (prin1-to-string comint-inhibit-carriage-motion) "\n")))
    (and (boundp 'comint-input-autoexpand)
	 (insert (concat "comint-input-autoexpand" " --> " (prin1-to-string comint-input-autoexpand) "\n")))
    (and (boundp 'comint-input-filter)
	 (insert (concat "comint-input-filter" " --> " (prin1-to-string comint-input-filter) "\n")))
    (and (boundp 'comint-input-filter-functions)
	 (insert (concat "comint-input-filter-functions" " --> " (prin1-to-string comint-input-filter-functions) "\n")))
    (and (boundp 'comint-input-history-ignore)
	 (insert (concat "comint-input-history-ignore" " --> " (prin1-to-string comint-input-history-ignore) "\n")))
    (and (boundp 'comint-input-ignoredups)
	 (insert (concat "comint-input-ignoredups" " --> " (prin1-to-string comint-input-ignoredups) "\n")))
    ;; (insert (concat "comint-input-ring" " --> " (prin1-to-string comint-input-ring) "\n")))
    (and (boundp 'comint-input-ring-file-name)
	 (insert (concat "comint-input-ring-file-name" " --> " (prin1-to-string comint-input-ring-file-name) "\n")))
    (and (boundp 'comint-input-ring-index)
	 (insert (concat "comint-input-ring-index" " --> " (prin1-to-string comint-input-ring-index) "\n")))
    (and (boundp 'comint-input-ring-separator)
	 (insert (concat "comint-input-ring-separator" " --> " (prin1-to-string comint-input-ring-separator) "\n")))
    (and (boundp 'comint-input-ring-size)
	 (insert (concat "comint-input-ring-size" " --> " (prin1-to-string comint-input-ring-size) "\n")))
    (and (boundp 'comint-input-sender)
	 (insert (concat "comint-input-sender" " --> " (prin1-to-string comint-input-sender) "\n")))
    (and (boundp 'comint-input-sender-no-newline)
	 (insert (concat "comint-input-sender-no-newline" " --> " (prin1-to-string comint-input-sender-no-newline) "\n")))
    (and (boundp 'comint-insert-previous-argument-last-index)
	 (insert (concat "comint-insert-previous-argument-last-index" " --> " (prin1-to-string comint-insert-previous-argument-last-index) "\n")))
    (and (boundp 'comint-insert-previous-argument-last-start-pos)
	 (insert (concat "comint-insert-previous-argument-last-start-pos" " --> " (prin1-to-string comint-insert-previous-argument-last-start-pos) "\n")))
    (and (boundp 'comint-last-input-end)
	 (insert (concat "comint-last-input-end" " --> " (prin1-to-string comint-last-input-end) "\n")))
    (and (boundp 'comint-last-input-start)
	 (insert (concat "comint-last-input-start" " --> " (prin1-to-string comint-last-input-start) "\n")))
    (and (boundp 'comint-last-output-start)
	 (insert (concat "comint-last-output-start" " --> " (prin1-to-string comint-last-output-start) "\n")))
    (and (boundp 'comint-last-prompt-overlay)
	 (insert (concat "comint-last-prompt-overlay" " --> " (prin1-to-string comint-last-prompt-overlay) "\n")))
    (and (boundp 'comint-matching-input-from-input-string)
	 (insert (concat "comint-matching-input-from-input-string" " --> " (prin1-to-string comint-matching-input-from-input-string) "\n")))
    ;; (insert (concat "comint-mode-abbrev-table" " --> " (prin1-to-string comint-mode-abbrev-table) "\n")))
    (and (boundp 'comint-mode-hook)
	 (insert (concat "comint-mode-hook" " --> " (prin1-to-string comint-mode-hook) "\n")))
    ;; (insert (concat "comint-mode-map" " --> " (prin1-to-string comint-mode-map) "\n")))
    ;; (insert (concat "comint-mode-syntax-table" " --> " (prin1-to-string comint-mode-syntax-table) "\n")))
    (and (boundp 'comint-move-point-for-output)
	 (insert (concat "comint-move-point-for-output" " --> " (prin1-to-string comint-move-point-for-output) "\n")))
    (and (boundp 'comint-output-filter-functions)
	 (insert (concat "comint-output-filter-functions" " --> " (prin1-to-string comint-output-filter-functions) "\n")))
    (and (boundp 'comint-password-prompt-regexp)
	 (insert (concat "comint-password-prompt-regexp" " --> " (prin1-to-string comint-password-prompt-regexp) "\n")))
    (and (boundp 'comint-preoutput-filter-functions)
	 (insert (concat "comint-preoutput-filter-functions" " --> " (prin1-to-string comint-preoutput-filter-functions) "\n")))
    (and (boundp 'comint-process-echoes)
	 (insert (concat "comint-process-echoes" " --> " (prin1-to-string comint-process-echoes) "\n")))
    (and (boundp 'comint-prompt-read-only)
	 (insert (concat "comint-prompt-read-only" " --> " (prin1-to-string comint-prompt-read-only) "\n")))
    (and (boundp 'comint-prompt-regexp)
	 (insert (concat "comint-prompt-regexp" " --> " (prin1-to-string comint-prompt-regexp) "\n")))
    (and (boundp 'comint-ptyp)
	 (insert (concat "comint-ptyp" " --> " (prin1-to-string comint-ptyp) "\n")))
    (and (boundp 'comint-redirect-completed)
	 (insert (concat "comint-redirect-completed" " --> " (prin1-to-string comint-redirect-completed) "\n")))
    (and (boundp 'comint-redirect-echo-input)
	 (insert (concat "comint-redirect-echo-input" " --> " (prin1-to-string comint-redirect-echo-input) "\n")))
    (and (boundp 'comint-redirect-filter-functions)
	 (insert (concat "comint-redirect-filter-functions" " --> " (prin1-to-string comint-redirect-filter-functions) "\n")))
    (and (boundp 'comint-redirect-finished-regexp)
	 (insert (concat "comint-redirect-finished-regexp" " --> " (prin1-to-string comint-redirect-finished-regexp) "\n")))
    (and (boundp 'comint-redirect-insert-matching-regexp)
	 (insert (concat "comint-redirect-insert-matching-regexp" " --> " (prin1-to-string comint-redirect-insert-matching-regexp) "\n")))
    (and (boundp 'comint-redirect-original-filter-function)
	 (insert (concat "comint-redirect-original-filter-function" " --> " (prin1-to-string comint-redirect-original-filter-function) "\n")))
    (and (boundp 'comint-redirect-original-mode-line-process)
	 (insert (concat "comint-redirect-original-mode-line-process" " --> " (prin1-to-string comint-redirect-original-mode-line-process) "\n")))
    (and (boundp 'comint-redirect-output-buffer)
	 (insert (concat "comint-redirect-output-buffer" " --> " (prin1-to-string comint-redirect-output-buffer) "\n")))
    (and (boundp 'comint-redirect-perform-sanity-check)
	 (insert (concat "comint-redirect-perform-sanity-check" " --> " (prin1-to-string comint-redirect-perform-sanity-check) "\n")))
    (and (boundp 'comint-redirect-subvert-readonly)
	 (insert (concat "comint-redirect-subvert-readonly" " --> " (prin1-to-string comint-redirect-subvert-readonly) "\n")))
    (and (boundp 'comint-redirect-verbose)
	 (insert (concat "comint-redirect-verbose" " --> " (prin1-to-string comint-redirect-verbose) "\n")))
    (and (boundp 'comint-save-input-ring-index)
	 (insert (concat "comint-save-input-ring-index" " --> " (prin1-to-string comint-save-input-ring-index) "\n")))
    (and (boundp 'comint-scroll-show-maximum-output)
	 (insert (concat "comint-scroll-show-maximum-output" " --> " (prin1-to-string comint-scroll-show-maximum-output) "\n")))
    (and (boundp 'comint-scroll-to-bottom-on-input)
	 (insert (concat "comint-scroll-to-bottom-on-input" " --> " (prin1-to-string comint-scroll-to-bottom-on-input) "\n")))
    (and (boundp 'comint-scroll-to-bottom-on-output)
	 (insert (concat "comint-scroll-to-bottom-on-output" " --> " (prin1-to-string comint-scroll-to-bottom-on-output) "\n")))
    (and (boundp 'comint-stored-incomplete-input)
	 (insert (concat "comint-stored-incomplete-input" " --> " (prin1-to-string comint-stored-incomplete-input) "\n")))
    (and (boundp 'comint-use-prompt-regexp)
	 (insert (concat "comint-use-prompt-regexp" " --> " (prin1-to-string comint-use-prompt-regexp) "\n")))
    (and (boundp 'comint-use-prompt-regexp-instead-of-fields)
	 (insert (concat "comint-use-prompt-regexp-instead-of-fields" " --> " (prin1-to-string comint-use-prompt-regexp-instead-of-fields) "\n")))))

(provide 'py-report-comint-variable-setting)
;;; py-report-comint-variable-setting.el ends here
