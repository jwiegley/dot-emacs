;;; mdformat.el --- Format Markdown buffers via the mdformat tool -*- lexical-binding: t -*-

;; Copyright (C) 2026 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 26 Jun 2026
;; Version: 1.0
;; Package-Requires: ((emacs "28.1"))
;; Keywords: markdown text formatting tools
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; This module reformats the current Markdown buffer in place by piping
;; its entire contents through the external `mdformat' program (run as
;; "mdformat --wrap no -", reading from stdin and writing to stdout).
;;
;; The whole (widened) buffer is filtered, and on success the buffer
;; text is replaced from mdformat's output using `replace-buffer-contents',
;; which applies only the minimal edits.  Point, markers and window-start
;; are preserved, and the change coalesces into a single undo step.  The
;; buffer is left modified but is NOT saved -- the on-disk file changes
;; only when you later save it yourself.
;;
;; On any error (non-zero exit, abnormal termination, missing executable,
;; or empty output for a buffer that holds non-whitespace content) the
;; buffer is left byte-for-byte unchanged and a `user-error' is signalled
;; carrying mdformat's diagnostics.
;;
;; Usage:
;;
;;   M-x mdformat-buffer
;;
;; Or bind it:
;;
;;   (with-eval-after-load 'markdown-mode
;;     (define-key markdown-mode-map (kbd "C-c C-f") #'mdformat-buffer))

;;; Code:

(require 'subr-x)                        ; string-trim, string-empty-p

(defgroup mdformat nil
  "Reformat Markdown buffers with the external `mdformat' tool."
  :group 'text
  :prefix "mdformat-")

(defcustom mdformat-command "mdformat"
  "Executable used to reformat Markdown buffers.
Resolved against `exec-path' if unqualified."
  :type 'string
  :group 'mdformat)

(defcustom mdformat-arguments '("--wrap" "no")
  "Base arguments for `mdformat-command'.
The literal \"-\" argument (meaning read stdin, write stdout) is
appended after these when the command is run."
  :type '(repeat string)
  :group 'mdformat)

;;;###autoload
(defun mdformat-buffer ()
  "Reformat the current buffer with \"mdformat --wrap no\".
Filters the whole (widened) buffer through `mdformat-command' via
stdin/stdout.  On success the text is replaced from the captured output
with `replace-buffer-contents' (preserving point, markers and
window-start, and producing a single undo step); the buffer is left
modified but is NOT saved.  On any non-zero exit (or empty output for a
buffer holding non-whitespace content) the buffer is left untouched and a
`user-error' is signalled, carrying mdformat's stderr when available."
  (interactive)
  (barf-if-buffer-read-only)            ; read-only: stop before any work
  (unless (executable-find mdformat-command)
    (user-error "Cannot find mdformat executable: %s" mdformat-command))
  (save-restriction
    (widen)                             ; filter the whole buffer
    (if (= (point-min) (point-max))
        (message "mdformat: buffer is empty, nothing to do")
      (let ((inbuf   (current-buffer))
            (outbuf  (generate-new-buffer " *mdformat-output*"))
            (errfile (make-temp-file "mdformat-err")))
        (unwind-protect
            (let ((status
                   (let ((coding-system-for-read  'utf-8)        ; decode stdout
                         (coding-system-for-write 'utf-8-unix))  ; encode stdin, LF
                     ;; DELETE=nil -> INBUF is never mutated by the run.
                     ;; DESTINATION=(OUTBUF ERRFILE) -> stdout/stderr split.
                     (apply #'call-process-region
                            (point-min) (point-max) mdformat-command
                            nil (list outbuf errfile) nil
                            (append mdformat-arguments (list "-"))))))
              (if (and (integerp status) (zerop status))
                  ;; --- success: minimal edits, single undo, no fixups ---
                  (if (and (zerop (buffer-size outbuf))
                           (save-excursion
                             (goto-char (point-min))
                             (re-search-forward "[^[:space:]]" nil t)))
                      ;; Exit 0 with empty output for a buffer that holds
                      ;; real content would wipe it; treat that as failure
                      ;; and leave the buffer untouched.  (A whitespace-only
                      ;; buffer may legitimately format to empty, so only
                      ;; guard when non-whitespace content exists.)
                      (user-error
                       "mdformat produced empty output; buffer left unchanged")
                    (let ((win-starts
                           ;; Capture window starts as markers so they track
                           ;; the edits `replace-buffer-contents' makes above
                           ;; the visible region, keeping the displayed top
                           ;; line stable.
                           (mapcar (lambda (w)
                                     (cons w (copy-marker (window-start w))))
                                   (get-buffer-window-list inbuf nil t))))
                      ;; The 0.5s MAX-SECS budget bounds diff time; if it is
                      ;; exceeded Emacs falls back to a wholesale
                      ;; delete+insert, which keeps the content correct and
                      ;; undo a single step, but does NOT relocate point or
                      ;; markers (point typically lands at end).  This trades
                      ;; worst-case point fidelity for bounded latency on
                      ;; very large or dissimilar buffers.
                      (with-undo-amalgamate
                        (replace-buffer-contents outbuf 0.5))
                      (dolist (ws win-starts)
                        (when (window-live-p (car ws))
                          (set-window-start (car ws) (cdr ws) t))
                        (set-marker (cdr ws) nil))
                      (message "mdformat: buffer reformatted")))
                ;; --- failure: buffer untouched, report stderr ---
                (let ((stderr (with-temp-buffer
                                (let ((coding-system-for-read 'utf-8))
                                  (insert-file-contents errfile))
                                (string-trim (buffer-string)))))
                  (user-error "mdformat failed (status %s): %s"
                              status
                              (if (string-empty-p stderr)
                                  "no error output" stderr)))))
          ;; --- always: release temp resources ---
          (when (buffer-live-p outbuf) (kill-buffer outbuf))
          (when (file-exists-p errfile) (delete-file errfile)))))))

(provide 'mdformat)

;;; mdformat.el ends here
