;;; vlf-search.el --- Search functionality for VLF  -*- lexical-binding: t -*-

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Keywords: large files, search
;; Author: Andrey Kotlarski <m00naticus@gmail.com>
;; URL: https://github.com/m00natic/vlfi

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:
;; This package provides search utilities for dealing with large files
;; in constant memory.

;;; Code:

(require 'vlf)

(defvar hexl-bits)
(defvar tramp-verbose)

(defun vlf-re-search (regexp count backward
                             &optional reporter time highlight)
  "Search for REGEXP COUNT number of times forward or BACKWARD.
Use existing REPORTER and start TIME if given.
Highlight match if HIGHLIGHT is non nil.
Return t if search has been at least partially successful."
  (if (<= count 0)
      (error "Count must be positive"))
  (run-hook-with-args 'vlf-before-batch-functions 'search)
  (or reporter (setq reporter (make-progress-reporter
                               (concat "Searching for " regexp "...")
                               (if backward
                                   (- vlf-file-size vlf-end-pos)
                                 vlf-start-pos)
                               vlf-file-size)))
  (or time (setq time (float-time)))
  (let* ((tramp-verbose (if (and (boundp 'tramp-verbose)
                                 tramp-verbose)
                            (min tramp-verbose 1)))
         (case-fold-search t)
         (match-chunk-start vlf-start-pos)
         (match-chunk-end vlf-end-pos)
         (match-start-pos (point))
         (match-end-pos match-start-pos)
         (last-match-pos match-start-pos)
         (to-find count)
         (is-hexl (derived-mode-p 'hexl-mode))
         (tune-types (if is-hexl '(:hexl :raw)
                       '(:insert :encode)))
         (font-lock font-lock-mode))
    (font-lock-mode 0)
    (vlf-with-undo-disabled
     (unwind-protect
         (catch 'end-of-file
           (if backward
               (while (not (zerop to-find))
                 (cond ((re-search-backward regexp nil t)
                        (setq to-find (1- to-find)
                              match-chunk-start vlf-start-pos
                              match-chunk-end vlf-end-pos
                              match-start-pos (match-beginning 0)
                              match-end-pos (match-end 0)
                              last-match-pos match-start-pos))
                       ((zerop vlf-start-pos)
                        (throw 'end-of-file nil))
                       (t (let ((end
                                 (if is-hexl
                                     (progn
                                       (goto-char (point-min))
                                       (forward-line 10)
                                       (if (< last-match-pos (point))
                                           (goto-char last-match-pos))
                                       (+ vlf-start-pos
                                          (* (- 10 (forward-line -10))
                                             hexl-bits)))
                                   (vlf-byte-position
                                    (min 1024 (/ (point-max) 10)
                                         last-match-pos)))))
                            (vlf-tune-batch tune-types)
                            (setq vlf-start-pos end) ;don't adjust end
                            (vlf-move-to-chunk (- end vlf-batch-size)
                                               end))
                          (let ((pmax (point-max)))
                            (goto-char pmax)
                            (setq last-match-pos pmax))
                          (progress-reporter-update
                           reporter (- vlf-file-size
                                       vlf-start-pos)))))
             (while (not (zerop to-find))
               (cond ((re-search-forward regexp nil t)
                      (setq to-find (1- to-find)
                            match-chunk-start vlf-start-pos
                            match-chunk-end vlf-end-pos
                            match-start-pos (match-beginning 0)
                            match-end-pos (match-end 0)
                            last-match-pos match-end-pos))
                     ((>= vlf-end-pos vlf-file-size)
                      (throw 'end-of-file nil))
                     (t (let* ((pmax (point-max))
                               (start
                                (if is-hexl
                                    (progn
                                      (goto-char pmax)
                                      (forward-line -10)
                                      (if (< (point) last-match-pos)
                                          (goto-char last-match-pos))
                                      (- vlf-end-pos
                                         (* (- 10 (forward-line 10))
                                            hexl-bits)))
                                  (vlf-byte-position
                                   (max (- pmax 1024)
                                        (- pmax (/ pmax 10))
                                        last-match-pos)))))
                          (vlf-tune-batch tune-types)
                          (setq vlf-end-pos start) ;don't adjust start
                          (vlf-move-to-chunk start (+ start
                                                      vlf-batch-size)))
                        (let ((pmin (point-min)))
                          (goto-char pmin)
                          (setq last-match-pos pmin))
                        (progress-reporter-update reporter
                                                  vlf-end-pos)))))
           (progress-reporter-done reporter))
       (set-buffer-modified-p nil)
       (if font-lock (font-lock-mode 1))
       (let ((result
              (if backward
                  (vlf-goto-match match-chunk-start match-chunk-end
                                  match-start-pos match-end-pos
                                  count to-find time highlight)
                (vlf-goto-match match-chunk-start match-chunk-end
                                match-end-pos match-start-pos
                                count to-find time highlight))))
         (run-hook-with-args 'vlf-after-batch-functions 'search)
         result)))))

(defun vlf-goto-match (match-chunk-start match-chunk-end
                                         match-start-pos match-end-pos
                                         count to-find time
                                         highlight)
  "Move to MATCH-CHUNK-START MATCH-CHUNK-END surrounding\
MATCH-START-POS and MATCH-END-POS.
According to COUNT and left TO-FIND, show if search has been
successful.  Use start TIME to report how much it took.
Highlight match if HIGHLIGHT is non nil.
Return nil if nothing found."
  (vlf-move-to-chunk match-chunk-start match-chunk-end)
  (goto-char match-start-pos)
  (setq vlf-batch-size (vlf-tune-optimal-load
                        (if (derived-mode-p 'hexl-mode)
                            '(:hexl :raw)
                          '(:insert :encode))))
  (if (= count to-find)
      (progn (message "Not found (%f secs)" (- (float-time) time))
             nil)
    (let ((success (zerop to-find))
          (overlay (make-overlay match-start-pos match-end-pos)))
      (overlay-put overlay 'face 'match)
      (if success
          (message "Match found (%f secs)" (- (float-time) time))
        (message "Moved to the %d match which is last (%f secs)"
                 (- count to-find) (- (float-time) time)))
      (if highlight
          (unwind-protect (sit-for 1)
            (delete-overlay overlay))
        (delete-overlay overlay)))
    t))

(defun vlf-re-search-forward (regexp count)
  "Search forward for REGEXP prefix COUNT number of times.
Search is performed chunk by chunk in `vlf-batch-size' memory."
  (interactive (if (vlf-no-modifications)
                   (list (read-regexp "Search whole file"
                                      (if regexp-history
                                          (car regexp-history)))
                         (or current-prefix-arg 1))))
  (let ((batch-size vlf-batch-size)
        success)
    (unwind-protect
        (setq success (vlf-re-search regexp count nil nil nil t))
      (or success (setq vlf-batch-size batch-size)))))

(defun vlf-re-search-backward (regexp count)
  "Search backward for REGEXP prefix COUNT number of times.
Search is performed chunk by chunk in `vlf-batch-size' memory."
  (interactive (if (vlf-no-modifications)
                   (list (read-regexp "Search whole file backward"
                                      (if regexp-history
                                          (car regexp-history)))
                         (or current-prefix-arg 1))))
  (let ((batch-size vlf-batch-size)
        success)
    (unwind-protect
        (setq success (vlf-re-search regexp count t nil nil t))
      (or success (setq vlf-batch-size batch-size)))))

(defun vlf-goto-line (n)
  "Go to line N.  If N is negative, count from the end of file."
  (interactive (if (vlf-no-modifications)
                   (list (read-number "Go to line: "))))
  (if (derived-mode-p 'hexl-mode)
      (vlf-goto-line-hexl n)
    (run-hook-with-args 'vlf-before-batch-functions 'goto-line)
    (vlf-verify-size)
    (let ((tramp-verbose (if (and (boundp 'tramp-verbose)
                                  tramp-verbose)
                             (min tramp-verbose 1)))
          (start-pos vlf-start-pos)
          (end-pos vlf-end-pos)
          (batch-size vlf-batch-size)
          (pos (point))
          (font-lock font-lock-mode)
          (time (float-time))
          (success nil))
      (font-lock-mode 0)
      (vlf-tune-batch '(:raw))
      (unwind-protect
          (if (< 0 n)
              (let ((start 0)
                    (end (min vlf-batch-size vlf-file-size))
                    (reporter (make-progress-reporter
                               (concat "Searching for line "
                                       (number-to-string n) "...")
                               0 vlf-file-size))
                    (inhibit-read-only t))
                (setq n (1- n))
                (vlf-with-undo-disabled
                 ;; (while (and (< (- end start) n)
                 ;;             (< n (- vlf-file-size start)))
                 ;;   (erase-buffer)
                 ;;   (vlf-tune-insert-file-contents-literally start end)
                 ;;   (goto-char (point-min))
                 ;;   (while (re-search-forward "[\n\C-m]" nil t)
                 ;;     (setq n (1- n)))
                 ;;   (vlf-verify-size)
                 ;;   (vlf-tune-batch '(:raw))
                 ;;   (setq start end
                 ;;         end (min vlf-file-size (+ start
                 ;;                                   vlf-batch-size)))
                 ;;   (progress-reporter-update reporter start))
                 (when (< n (- vlf-file-size end))
                   (vlf-tune-batch '(:insert :encode))
                   (vlf-move-to-chunk start (+ start vlf-batch-size))
                   (goto-char (point-min))
                   (setq success
                         (or (zerop n)
                             (when (vlf-re-search "[\n\C-m]" n nil
                                                  reporter time)
                               (forward-char) t))))))
            (let ((end vlf-file-size)
                  (reporter (make-progress-reporter
                             (concat "Searching for line -"
                                     (number-to-string n) "...")
                             0 vlf-file-size))
                  (inhibit-read-only t))
              (setq n (- n))
              (vlf-with-undo-disabled
               ;; (let ((start (max 0 (- vlf-file-size vlf-batch-size))))
               ;;   (while (and (< (- end start) n) (< n end))
               ;;     (erase-buffer)
               ;;     (vlf-tune-insert-file-contents-literally start end)
               ;;     (goto-char (point-max))
               ;;     (while (re-search-backward "[\n\C-m]" nil t)
               ;;       (setq n (1- n)))
               ;;     (vlf-tune-batch '(:raw))
               ;;     (setq end start
               ;;           start (max 0 (- end vlf-batch-size)))
               ;;     (progress-reporter-update reporter
               ;;                               (- vlf-file-size end))))
               (when (< n end)
                 (vlf-tune-batch '(:insert :encode))
                 (vlf-move-to-chunk (- end vlf-batch-size) end)
                 (goto-char (point-max))
                 (setq success (vlf-re-search "[\n\C-m]" n t
                                              reporter time))))))
        (if font-lock (font-lock-mode 1))
        (unless success
          (vlf-with-undo-disabled
           (vlf-move-to-chunk start-pos end-pos))
          (goto-char pos)
          (setq vlf-batch-size batch-size)
          (message "Unable to find line"))
        (run-hook-with-args 'vlf-after-batch-functions 'goto-line)))))

(defun vlf-goto-line-hexl (n)
  "Go to line N.  If N is negative, count from the end of file.
Assume `hexl-mode' is active."
  (vlf-tune-load '(:hexl :raw))
  (if (< n 0)
      (let ((hidden-bytes (+ vlf-file-size (* n hexl-bits))))
        (setq hidden-bytes (- hidden-bytes (mod hidden-bytes
                                                vlf-batch-size)))
        (vlf-move-to-batch hidden-bytes)
        (goto-char (point-max))
        (forward-line (+ (round (- vlf-file-size
                                   (min vlf-file-size
                                        (+ hidden-bytes
                                           vlf-batch-size)))
                                hexl-bits)
                         n)))
    (let ((hidden-bytes (1- (* n hexl-bits))))
      (setq hidden-bytes (- hidden-bytes (mod hidden-bytes
                                              vlf-batch-size)))
      (vlf-move-to-batch hidden-bytes)
      (goto-char (point-min))
      (forward-line (- n 1 (/ hidden-bytes hexl-bits))))))

(defun vlf-query-replace (regexp to-string &optional delimited backward)
  "Query replace over whole file matching REGEXP with TO-STRING.
Third arg DELIMITED (prefix arg if interactive), if non-nil, replace
only matches surrounded by word boundaries.  A negative prefix arg means
replace BACKWARD."
  (interactive (let ((common (query-replace-read-args
                              (concat "Query replace over whole file"
                                      (if current-prefix-arg
                                          (if (eq current-prefix-arg '-)
                                              " backward"
                                            " word")
                                        "")
                                      " regexp")
                              t)))
                 (list (nth 0 common) (nth 1 common) (nth 2 common)
                       (nth 3 common))))
  (let ((not-automatic t))
    (while (vlf-re-search regexp 1 backward)
      (cond (not-automatic
             (query-replace-regexp regexp to-string delimited
                                   nil nil backward)
             (if (eq 'automatic (lookup-key query-replace-map
                                            (vector last-input-event)))
                 (setq not-automatic nil)))
            (backward (while (re-search-backward regexp nil t)
                        (replace-match to-string)))
            (t (while (re-search-forward regexp nil t)
                 (replace-match to-string))))
      (if (buffer-modified-p)
          (save-buffer)))))

(provide 'vlf-search)

;;; vlf-search.el ends here
