;;; vlf-occur.el --- Occur-like functionality for VLF  -*- lexical-binding: t -*-

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Keywords: large files, indexing, occur
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
;; This package provides the `vlf-occur' command which builds
;; index of search occurrences in large file just like occur.

;;; Code:

(require 'vlf)

(defvar vlf-occur-vlf-file nil "VLF file that is searched.")
(make-variable-buffer-local 'vlf-occur-vlf-file)

(defvar vlf-occur-vlf-buffer nil "VLF buffer that is scanned.")
(make-variable-buffer-local 'vlf-occur-vlf-buffer)

(defvar vlf-occur-regexp)
(make-variable-buffer-local 'vlf-occur-regexp)

(defvar vlf-occur-hexl nil "Is `hexl-mode' active?")
(make-variable-buffer-local 'vlf-occur-hexl)

(defvar vlf-occur-lines 0 "Number of lines scanned by `vlf-occur'.")
(make-variable-buffer-local 'vlf-occur-lines)

(defvar tramp-verbose)
(defvar hexl-bits)

(defvar vlf-occur-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "n" 'vlf-occur-next-match)
    (define-key map "p" 'vlf-occur-prev-match)
    (define-key map "\C-m" 'vlf-occur-visit)
    (define-key map "\M-\r" 'vlf-occur-visit-new-buffer)
    (define-key map [mouse-1] 'vlf-occur-visit)
    (define-key map "o" 'vlf-occur-show)
    (define-key map [remap save-buffer] 'vlf-occur-save)
    map)
  "Keymap for command `vlf-occur-mode'.")

(define-derived-mode vlf-occur-mode special-mode "VLF[occur]"
  "Major mode for showing occur matches of VLF opened files."
  (add-hook 'write-file-functions 'vlf-occur-save nil t))

(defun vlf-occur-next-match ()
  "Move cursor to next match."
  (interactive)
  (if (eq (get-text-property (point) 'face) 'match)
      (goto-char (next-single-property-change (point) 'face)))
  (goto-char (or (text-property-any (point) (point-max) 'face 'match)
                 (text-property-any (point-min) (point)
                                    'face 'match))))

(defun vlf-occur-prev-match ()
  "Move cursor to previous match."
  (interactive)
  (if (eq (get-text-property (point) 'face) 'match)
      (goto-char (previous-single-property-change (point) 'face)))
  (while (not (eq (get-text-property (point) 'face) 'match))
    (goto-char (or (previous-single-property-change (point) 'face)
                   (point-max)))))

(defun vlf-occur-show (&optional event)
  "Visit current `vlf-occur' link in a vlf buffer but stay in the \
occur buffer.  If original VLF buffer has been killed,
open new VLF session each time.
EVENT may hold details of the invocation."
  (interactive (list last-nonmenu-event))
  (let ((occur-buffer (if event
                          (window-buffer (posn-window
                                          (event-end event)))
                        (current-buffer))))
    (vlf-occur-visit event)
    (pop-to-buffer occur-buffer)))

(defun vlf-occur-visit-new-buffer ()
  "Visit `vlf-occur' link in new vlf buffer."
  (interactive)
  (let ((current-prefix-arg t))
    (vlf-occur-visit)))

(defun vlf-occur-visit (&optional event)
  "Visit current `vlf-occur' link in a vlf buffer.
With prefix argument or if original VLF buffer has been killed,
open new VLF session.
EVENT may hold details of the invocation."
  (interactive (list last-nonmenu-event))
  (when event
    (set-buffer (window-buffer (posn-window (event-end event))))
    (goto-char (posn-point (event-end event))))
  (let* ((pos (point))
         (pos-relative (- pos (previous-single-char-property-change
                               pos 'vlf-match)))
         (chunk-start (get-text-property pos 'chunk-start)))
    (if chunk-start
        (let ((chunk-end (get-text-property pos 'chunk-end))
              (file (if (file-exists-p vlf-occur-vlf-file)
                        vlf-occur-vlf-file
                      (setq vlf-occur-vlf-file
                            (read-file-name
                             (concat vlf-occur-vlf-file
                                     " doesn't exist, locate it: ")))))
              (vlf-buffer vlf-occur-vlf-buffer)
              (not-hexl (not vlf-occur-hexl))
              (occur-buffer (current-buffer))
              (match-pos (+ (get-text-property pos 'line-pos)
                            pos-relative)))
          (cond (current-prefix-arg
                 (let ((original-occur-buffer vlf-occur-vlf-buffer))
                   (setq vlf-buffer (vlf file t))
                   (if (buffer-live-p original-occur-buffer)
                       (vlf-tune-copy-profile original-occur-buffer)))
                 (or not-hexl (hexl-mode))
                 (switch-to-buffer occur-buffer))
                ((not (buffer-live-p vlf-buffer))
                 (unless (catch 'found
                           (dolist (buf (buffer-list))
                             (set-buffer buf)
                             (and vlf-mode
                                  (equal file buffer-file-name)
                                  (eq (not (derived-mode-p 'hexl-mode))
                                      not-hexl)
                                  (setq vlf-buffer buf)
                                  (throw 'found t))))
                   (setq vlf-buffer (vlf file t))
                   (or not-hexl (hexl-mode)))
                 (switch-to-buffer occur-buffer)
                 (setq vlf-occur-vlf-buffer vlf-buffer)))
          (pop-to-buffer vlf-buffer)
          (vlf-move-to-chunk chunk-start chunk-end)
          (goto-char match-pos)))))

(defun vlf-occur-other-buffer (regexp)
  "Make whole file occur style index for REGEXP branching to new buffer.
Prematurely ending indexing will still show what's found so far."
  (let ((vlf-buffer (current-buffer))
        (file buffer-file-name)
        (file-size vlf-file-size)
        (batch-size vlf-batch-size)
        (is-hexl (derived-mode-p 'hexl-mode)))
    (with-temp-buffer
      (setq buffer-file-name file
            buffer-file-truename file
            buffer-undo-list t
            vlf-file-size file-size)
      (set-buffer-modified-p nil)
      (set (make-local-variable 'vlf-batch-size) batch-size)
      (when vlf-tune-enabled
        (vlf-tune-copy-profile vlf-buffer)
        (vlf-tune-batch (if is-hexl
                            '(:hexl :raw)
                          '(:insert :encode)) t))
      (vlf-mode 1)
      (if is-hexl (hexl-mode))
      (goto-char (point-min))
      (vlf-build-occur regexp vlf-buffer)
      (if vlf-tune-enabled
          (vlf-tune-copy-profile (current-buffer) vlf-buffer)))))

(defun vlf-occur (regexp)
  "Make whole file occur style index for REGEXP.
Prematurely ending indexing will still show what's found so far."
  (interactive (list (read-regexp "List lines matching regexp"
                                  (if regexp-history
                                      (car regexp-history)))))
  (run-hook-with-args 'vlf-before-batch-functions 'occur)
  (if (or (buffer-modified-p)
          (consp buffer-undo-list)
          (< vlf-batch-size vlf-start-pos))
      (vlf-occur-other-buffer regexp)
    (let ((start-pos vlf-start-pos)
          (end-pos vlf-end-pos)
          (pos (point))
          (batch-size vlf-batch-size))
      (vlf-tune-batch (if (derived-mode-p 'hexl-mode)
                          '(:hexl :raw)
                        '(:insert :encode)) t)
      (vlf-move-to-batch 0)
      (goto-char (point-min))
      (unwind-protect (vlf-build-occur regexp (current-buffer))
        (vlf-move-to-chunk start-pos end-pos)
        (goto-char pos)
        (setq vlf-batch-size batch-size))))
  (run-hook-with-args 'vlf-after-batch-functions 'occur))

(defun vlf-build-occur (regexp vlf-buffer)
  "Build occur style index for REGEXP over VLF-BUFFER."
  (let* ((tramp-verbose (if (and (boundp 'tramp-verbose)
                                 tramp-verbose)
                            (min tramp-verbose 1)))
         (case-fold-search t)
         (line 1)
         (last-match-line 0)
         (total-matches 0)
         (first-line-offset 0)
         (first-line-incomplete nil)
         (match-start-point (point-min))
         (match-end-point match-start-point)
         (last-match-insert-point nil)
         (occur-buffer (generate-new-buffer
                        (concat "*VLF-occur " (file-name-nondirectory
                                               buffer-file-name)
                                "*")))
         (is-hexl (derived-mode-p 'hexl-mode))
         (end-of-file nil)
         (time (float-time))
         (tune-types (if is-hexl '(:hexl :raw)
                       '(:insert :encode)))
         (reporter (make-progress-reporter
                    (concat "Building index for " regexp "...")
                    vlf-start-pos vlf-file-size)))
    (with-current-buffer occur-buffer
      (setq buffer-undo-list t))
    (unwind-protect
        (progn
          (while (not end-of-file)
            (if (re-search-forward regexp nil t)
                (progn
                  (setq line (+ line -1
                                (count-lines match-start-point
                                             (1+ (match-beginning 0))))
                        match-start-point (match-beginning 0)
                        match-end-point (match-end 0))
                  (let* ((chunk-start vlf-start-pos)
                         (chunk-end vlf-end-pos)
                         (line-pos (save-excursion
                                     (goto-char match-start-point)
                                     (line-beginning-position)))
                         (line-text (buffer-substring
                                     line-pos (line-end-position))))
                    (if (/= line-pos (point-min))
                        (setq first-line-offset 0
                              first-line-incomplete nil))
                    (with-current-buffer occur-buffer
                      (unless (= line last-match-line) ;new match line
                        (insert "\n:") ; insert line number
                        (let* ((column-point (1- (point)))
                               (overlay-pos column-point)
                               (overlay (make-overlay
                                         overlay-pos
                                         (1+ overlay-pos))))
                          (overlay-put overlay 'before-string
                                       (propertize
                                        (number-to-string line)
                                        'face 'shadow))
                          (overlay-put overlay 'vlf-match t)
                          (setq last-match-insert-point column-point
                                first-line-offset 0)))
                      (when (or first-line-incomplete
                                (/= line last-match-line))
                        (insert (propertize
                                 (if first-line-incomplete
                                     (substring line-text
                                                first-line-incomplete)
                                   line-text)
                                 'chunk-start chunk-start
                                 'chunk-end chunk-end
                                 'mouse-face '(highlight)
                                 'line-pos line-pos
                                 'help-echo
                                 (format "Move to line %d"
                                         line)))
                        (setq first-line-incomplete nil))
                      (setq last-match-line line
                            total-matches (1+ total-matches))
                      (let ((line-start (+ last-match-insert-point
                                           first-line-offset 1
                                           (- line-pos))))
                        (add-text-properties ; mark match
                         (+ line-start match-start-point)
                         (+ line-start match-end-point)
                         (list 'face 'match
                               'help-echo (format "Move to match %d"
                                                  total-matches)))))))
              (setq end-of-file (= vlf-end-pos vlf-file-size))
              (unless end-of-file
                (let ((start
                       (if is-hexl
                           (progn
                             (goto-char (point-max))
                             (forward-line -10)
                             (setq line
                                   (+ line
                                      (if (< match-end-point (point))
                                          (count-lines match-start-point
                                                       (point))
                                        (goto-char match-end-point)
                                        (1- (count-lines match-start-point
                                                         match-end-point)))))
                             (- vlf-end-pos (* (- 10 (forward-line 10))
                                               hexl-bits)))
                         (let* ((pmax (point-max))
                                (batch-step (min 1024 (/ vlf-batch-size
                                                         10)))
                                (batch-point
                                 (max match-end-point
                                      (or
                                       (byte-to-position
                                        (- vlf-batch-size batch-step))
                                       (progn
                                         (goto-char pmax)
                                         (let ((last (line-beginning-position)))
                                           (if (= last (point-min))
                                               (1- (point))
                                             last)))))))
                           (goto-char batch-point)
                           (setq first-line-offset
                                 (- batch-point (line-beginning-position))
                                 line
                                 (+ line
                                    (count-lines match-start-point
                                                 batch-point)
                                    (if (< 0 first-line-offset) -1 0)))
                           ;; last match is on the last line?
                           (goto-char match-end-point)
                           (forward-line)
                           (setq first-line-incomplete
                                 (if (= (point) pmax)
                                     (- pmax match-end-point)))
                           (vlf-byte-position batch-point)))))
                  (vlf-tune-batch tune-types)
                  (setq vlf-end-pos start) ;not to adjust start
                  (vlf-move-to-chunk start (+ start vlf-batch-size)))
                (setq match-start-point (point-min)
                      match-end-point match-start-point)
                (goto-char match-end-point)
                (progress-reporter-update reporter vlf-start-pos))))
          (progress-reporter-done reporter))
      (set-buffer-modified-p nil)
      (if (zerop total-matches)
          (progn (kill-buffer occur-buffer)
                 (message "No matches for \"%s\" (%f secs)"
                          regexp (- (float-time) time)))
        (let ((file buffer-file-name)
              (dir default-directory))
          (with-current-buffer occur-buffer
            (insert "\n")
            (goto-char (point-min))
            (insert (propertize
                     (format "%d matches from %d lines for \"%s\" \
in file: %s" total-matches line regexp file)
                     'face 'underline))
            (set-buffer-modified-p nil)
            (forward-char 2)
            (vlf-occur-mode)
            (setq default-directory dir
                  vlf-occur-vlf-file file
                  vlf-occur-vlf-buffer vlf-buffer
                  vlf-occur-regexp regexp
                  vlf-occur-hexl is-hexl
                  vlf-occur-lines line)))
        (display-buffer occur-buffer)
        (message "Occur finished for \"%s\" (%f secs)"
                 regexp (- (float-time) time))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; save, load vlf-occur data

(defun vlf-occur-save (file)
  "Serialize `vlf-occur' results to FILE which can later be reloaded."
  (interactive (list (or buffer-file-name
                         (read-file-name "Save vlf-occur results in: "
                                         nil nil nil
                                         (concat
                                          (file-name-nondirectory
                                           vlf-occur-vlf-file)
                                          ".vlfo")))))
  (setq buffer-file-name file)
  (let ((vlf-occur-save-buffer
         (generate-new-buffer (concat "*VLF-occur-save "
                                      (file-name-nondirectory file)
                                      "*"))))
    (with-current-buffer vlf-occur-save-buffer
      (setq buffer-file-name file
            buffer-undo-list t)
      (insert ";; -*- eval: (vlf-occur-load) -*-\n"))
    (prin1 (list vlf-occur-vlf-file vlf-occur-regexp vlf-occur-hexl
                 vlf-occur-lines)
           vlf-occur-save-buffer)
    (save-excursion
      (goto-char (point-min))
      (let ((pmax (point-max)))
        (while (/= pmax (goto-char (next-single-char-property-change
                                    (1+ (point)) 'vlf-match)))
          (let* ((pos (1+ (point)))
                 (line (get-char-property (1- pos) 'before-string)))
            (if line
                (prin1 (list (string-to-number line)
                             (get-text-property pos 'chunk-start)
                             (get-text-property pos 'chunk-end)
                             (get-text-property pos 'line-pos)
                             (buffer-substring-no-properties
                              pos (1- (next-single-char-property-change
                                       pos 'vlf-match))))
                       vlf-occur-save-buffer))))))
    (with-current-buffer vlf-occur-save-buffer
      (save-buffer))
    (kill-buffer vlf-occur-save-buffer))
  t)

;;;###autoload
(defun vlf-occur-load ()
  "Load serialized `vlf-occur' results from current buffer."
  (interactive)
  (goto-char (point-min))
  (let* ((vlf-occur-data-buffer (current-buffer))
         (header (read vlf-occur-data-buffer))
         (vlf-file (nth 0 header))
         (regexp (nth 1 header))
         (all-lines (nth 3 header))
         (file buffer-file-name)
         (vlf-occur-buffer
          (generate-new-buffer (concat "*VLF-occur "
                                       (file-name-nondirectory file)
                                       "*"))))
    (switch-to-buffer vlf-occur-buffer)
    (setq buffer-file-name file
          buffer-undo-list t)
    (goto-char (point-min))
    (let ((match-count 0)
          (form 0))
      (while (setq form (ignore-errors (read vlf-occur-data-buffer)))
        (goto-char (point-max))
        (insert "\n:")
        (let* ((overlay-pos (1- (point)))
               (overlay (make-overlay overlay-pos (1+ overlay-pos)))
               (line (number-to-string (nth 0 form)))
               (pos (point)))
          (overlay-put overlay 'before-string
                       (propertize line 'face 'shadow))
          (overlay-put overlay 'vlf-match t)
          (insert (propertize (nth 4 form) 'chunk-start (nth 1 form)
                              'chunk-end (nth 2 form)
                              'mouse-face '(highlight)
                              'line-pos (nth 3 form)
                              'help-echo (concat "Move to line "
                                                 line)))
          (goto-char pos)
          (while (re-search-forward regexp nil t)
            (add-text-properties
             (match-beginning 0) (match-end 0)
             (list 'face 'match 'help-echo
                   (format "Move to match %d"
                           (setq match-count (1+ match-count))))))))
      (kill-buffer vlf-occur-data-buffer)
      (goto-char (point-min))
      (insert (propertize
               (format "%d matches from %d lines for \"%s\" in file: %s"
                       match-count all-lines regexp vlf-file)
               'face 'underline)))
    (set-buffer-modified-p nil)
    (vlf-occur-mode)
    (setq vlf-occur-vlf-file vlf-file
          vlf-occur-regexp regexp
          vlf-occur-hexl (nth 2 header)
          vlf-occur-lines all-lines)))

(provide 'vlf-occur)

;;; vlf-occur.el ends here
