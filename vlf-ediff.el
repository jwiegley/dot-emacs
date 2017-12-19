;;; vlf-ediff.el --- VLF ediff functionality  -*- lexical-binding: t -*-

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Keywords: large files, compare, ediff
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
;; This package provides ediff functionality for VLF managed buffers
;; in face of the `vlf-ediff-buffers' and `vlf-ediff-files' commands.

;;; Code:

(require 'vlf)
(require 'ediff)

(defvar vlf-ediff-session nil
  "If non nil, specifies that ediff is done over VLF buffers.")
(make-variable-buffer-local 'vlf-ediff-session)

(defvar tramp-verbose)

(defun vlf-ediff-buffers (buffer-A buffer-B)
  "Run batch by batch ediff over VLF buffers BUFFER-A and BUFFER-B.
Batch size is determined by the size in BUFFER-A.
Requesting next or previous difference at the end or beginning
respectively of difference list, runs ediff over the adjacent chunks."
  (interactive
   (let (bf)
     (list (setq bf (read-buffer "Buffer A to compare: "
                                 (ediff-other-buffer "") t))
           (read-buffer "Buffer B to compare: "
                        (progn
                          ;; realign buffers so that two visible bufs will be
                          ;; at the top
                          (save-window-excursion (other-window 1))
                          (ediff-other-buffer bf))
                        t))))
  (set-buffer buffer-A)
  (setq buffer-A (current-buffer)) ;names change, so reference by buffer object
  (let ((batch-size vlf-batch-size))
    (set-buffer buffer-B)
    (setq buffer-B (current-buffer))
    (vlf-set-batch-size batch-size))
  (ediff-buffers buffer-A buffer-B
                 '((lambda () (setq vlf-ediff-session t)
                     (vlf-ediff-next ediff-buffer-A ediff-buffer-B
                                     ediff-control-buffer
                                     'vlf-next-chunk)))))

;;;###autoload
(defun vlf-ediff-files (file-A file-B batch-size)
  "Run batch by batch ediff over FILE-A and FILE-B.
Files are processed with VLF with BATCH-SIZE chunks.
Requesting next or previous difference at the end or beginning
respectively of difference list, runs ediff over the adjacent chunks."
  (interactive
   (let ((dir-A (if ediff-use-last-dir
                    ediff-last-dir-A
                  default-directory))
         dir-B f)
     (list (setq f (ediff-read-file-name
                    "File A to compare"
                    dir-A
                    (ediff-get-default-file-name)
                    'no-dirs))
           (ediff-read-file-name "File B to compare"
                                 (setq dir-B
                                       (if ediff-use-last-dir
                                           ediff-last-dir-B
                                         (file-name-directory f)))
                                 (progn
                                   (ediff-add-to-history
                                    'file-name-history
                                    (ediff-abbreviate-file-name
                                     (expand-file-name
                                      (file-name-nondirectory f)
                                      dir-B)))
                                   (ediff-get-default-file-name f 1)))
           (read-number "Batch size (in bytes): " vlf-batch-size))))
  (let ((buffer-A (vlf file-A t)))
    (set-buffer buffer-A)
    (vlf-set-batch-size batch-size)
    (let ((buffer-B (vlf file-B t)))
      (vlf-ediff-buffers buffer-A buffer-B))))

(defadvice ediff-next-difference (around vlf-ediff-next-difference
                                         compile activate)
  "Move to the next VLF chunk and search for difference if at the end\
of difference list."
  (if (and vlf-ediff-session
           (<= (1- ediff-number-of-differences)
               ediff-current-difference))
      (let ((buffer-A ediff-buffer-A)
            (buffer-B ediff-buffer-B)
            (ediff-buffer (current-buffer)))
        (save-excursion
          (set-buffer buffer-A)
          (vlf-next-chunk)
          (set-buffer buffer-B)
          (vlf-next-chunk)
          (vlf-ediff-next buffer-A buffer-B ediff-buffer
                          'vlf-next-chunk))
        (or (zerop ediff-number-of-differences)
            (ediff-jump-to-difference 1)))
    ad-do-it))

(defadvice ediff-previous-difference (around vlf-ediff-prev-difference
                                             compile activate)
  "Move to the previous VLF chunk and search for difference if at the\
beginning of difference list."
  (if (and vlf-ediff-session
           (<= ediff-current-difference 0))
      (let ((buffer-A ediff-buffer-A)
            (buffer-B ediff-buffer-B)
            (ediff-buffer (current-buffer)))
        (save-excursion
          (set-buffer buffer-A)
          (vlf-prev-chunk)
          (set-buffer buffer-B)
          (vlf-prev-chunk)
          (vlf-ediff-next buffer-A buffer-B ediff-buffer
                          'vlf-prev-chunk))
        (or (zerop ediff-number-of-differences)
            (ediff-jump-to-difference -1)))
    ad-do-it))

(defun vlf-next-chunk ()
  "Move to next chunk."
  (vlf-move-to-chunk vlf-end-pos (+ vlf-end-pos vlf-batch-size)))

(defun vlf-prev-chunk ()
  "Move to previous chunk."
  (vlf-move-to-chunk (- vlf-start-pos vlf-batch-size) vlf-start-pos))

(defun vlf-ediff-next (buffer-A buffer-B ediff-buffer
                                &optional next-func)
  "Find next pair of chunks that differ in BUFFER-A and BUFFER-B\
governed by EDIFF-BUFFER.  NEXT-FUNC is used to jump to the next
logical chunks in case there is no difference at the current ones."
  (set-buffer buffer-A)
  (run-hook-with-args 'vlf-before-batch-functions 'ediff)
  (setq buffer-A (current-buffer)) ;names change, so reference by buffer object
  (let ((end-A (= vlf-start-pos vlf-end-pos))
        (chunk-A (cons vlf-start-pos vlf-end-pos))
        (point-max-A (point-max))
        (font-lock-A font-lock-mode)
        (min-file-size vlf-file-size)
        (forward-p (eq next-func 'vlf-next-chunk))
        (is-hexl (derived-mode-p 'hexl-mode)))
    (font-lock-mode 0)
    (set-buffer buffer-B)
    (run-hook-with-args 'vlf-before-batch-functions 'ediff)
    (setq buffer-B (current-buffer)
          min-file-size (min min-file-size vlf-file-size)
          is-hexl (or is-hexl (derived-mode-p 'hexl-mode)))
    (let ((tramp-verbose (if (and (boundp 'tramp-verbose)
                                  tramp-verbose)
                             (min tramp-verbose 1)))
          (end-B (= vlf-start-pos vlf-end-pos))
          (chunk-B (cons vlf-start-pos vlf-end-pos))
          (font-lock-B font-lock-mode)
          (done nil)
          (reporter (make-progress-reporter
                     "Searching for difference..."
                     (if forward-p vlf-start-pos
                       (- min-file-size vlf-end-pos))
                     min-file-size)))
      (font-lock-mode 0)
      (unwind-protect
          (progn
            (while (and (or (not end-A) (not end-B))
                        (or (zerop (compare-buffer-substrings
                                    buffer-A (point-min) point-max-A
                                    buffer-B (point-min) (point-max)))
                            (with-current-buffer ediff-buffer
                              (ediff-update-diffs)
                              (and (not end-A) (not end-B) (not is-hexl)
                                   (vlf-ediff-refine buffer-A
                                                     buffer-B))
                              (zerop ediff-number-of-differences))))
              (funcall next-func)
              (setq end-B (= vlf-start-pos vlf-end-pos))
              (with-current-buffer buffer-A
                (funcall next-func)
                (setq end-A (= vlf-start-pos vlf-end-pos)
                      point-max-A (point-max)))
              (progress-reporter-update reporter
                                        (if forward-p vlf-end-pos
                                          (- vlf-file-size
                                             vlf-start-pos))))
            (progress-reporter-done reporter)
            (when (and end-A end-B)
              (if forward-p
                  (let ((max-file-size vlf-file-size))
                    (vlf-move-to-chunk (- max-file-size vlf-batch-size)
                                       max-file-size)
                    (set-buffer buffer-A)
                    (setq max-file-size (max max-file-size
                                             vlf-file-size))
                    (vlf-move-to-chunk (- max-file-size
                                          vlf-batch-size)
                                       max-file-size))
                (vlf-move-to-batch 0)
                (set-buffer buffer-A)
                (vlf-move-to-batch 0))
              (set-buffer ediff-buffer)
              (ediff-update-diffs)
              (or is-hexl
                  (if (or (not forward-p)
                          (and (not end-A) (not end-B)))
                      (vlf-ediff-refine buffer-A buffer-B))))
            (setq done t))
        (unless done
          (set-buffer buffer-A)
          (set-buffer-modified-p nil)
          (vlf-move-to-chunk (car chunk-A) (cdr chunk-A))
          (set-buffer buffer-B)
          (set-buffer-modified-p nil)
          (vlf-move-to-chunk (car chunk-B) (cdr chunk-B))
          (set-buffer ediff-buffer)
          (ediff-update-diffs)
          (or is-hexl
              (vlf-ediff-refine buffer-A buffer-B)))
        (set-buffer buffer-A)
        (if font-lock-A (font-lock-mode 1))
        (run-hook-with-args 'vlf-after-batch-functions 'ediff)
        (set-buffer buffer-B)
        (if font-lock-B (font-lock-mode 1))
        (run-hook-with-args 'vlf-after-batch-functions 'ediff)))))

(defun vlf-ediff-refine (buffer-A buffer-B)
  "Try to minimize differences between BUFFER-A and BUFFER-B.
This can happen if first or last difference is at the start/end of
buffer."
  (or (zerop ediff-number-of-differences)
      (let ((adjust-p (vlf-ediff-adjust buffer-A buffer-B)))
        (setq adjust-p (or (vlf-ediff-adjust buffer-A buffer-B t)
                           adjust-p))
        (if adjust-p (ediff-update-diffs)))))

(defun vlf-ediff-adjust (buf-A buf-B &optional end)
  "Additionally adjust buffer borders for BUF-A and BUF-B.
Adjust beginning if END is nil.  Return t if refining is needed,
nil otherwise."
  (let* ((diff-num (if end (1- ediff-number-of-differences) 0))
         (diff-A (ediff-get-diff-overlay diff-num 'A))
         (diff-B (ediff-get-diff-overlay diff-num 'B))
         diff-A-str diff-B-str adjust-p)
    (with-current-buffer buf-A
      (setq adjust-p (if end (= (overlay-end diff-A) (point-max))
                       (= (overlay-start diff-A) (point-min)))
            diff-A-str (and adjust-p (buffer-substring-no-properties
                                      (overlay-start diff-A)
                                      (overlay-end diff-A))))
      (set-buffer buf-B)
      (setq adjust-p (and adjust-p
                          (if end (= (overlay-end diff-B) (point-max))
                            (= (overlay-start diff-B) (point-min))))
            diff-B-str (and adjust-p (buffer-substring-no-properties
                                      (overlay-start diff-B)
                                      (overlay-end diff-B))))
      (if adjust-p
          (let ((len-A (length diff-A-str))
                (len-B (length diff-B-str))
                (adjust-func (if end 'vlf-ediff-adjust-end
                               'vlf-ediff-adjust-start)))
            (cond
             ((< len-A len-B)
              (or (funcall adjust-func diff-A-str diff-B-str buf-B)
                  (setq adjust-p nil)))
             ((< len-B len-A)
              (or (funcall adjust-func diff-B-str diff-A-str buf-A)
                  (setq adjust-p nil)))
             (t (setq adjust-p nil))))))
    adjust-p))

(defun vlf-ediff-adjust-start (diff-short diff-long vlf-buffer)
  "Remove difference between DIFF-SHORT and DIFF-LONG from beginning\
of VLF-BUFFER."
  (when (string-suffix-p diff-short diff-long)
    (set-buffer vlf-buffer)
    (vlf-move-to-chunk (+ vlf-start-pos
                          (length (encode-coding-string
                                   (substring diff-long 0
                                              (- (length diff-long)
                                                 (length diff-short)))
                                   buffer-file-coding-system t)))
                       vlf-end-pos)))

(defun vlf-ediff-adjust-end (diff-short diff-long vlf-buffer)
  "Remove difference between DIFF-SHORT and DIFF-LONG from the end of\
VLF-BUFFER."
  (when (string-prefix-p diff-short diff-long)
    (set-buffer vlf-buffer)
    (vlf-move-to-chunk vlf-start-pos
                       (- vlf-end-pos
                          (length (encode-coding-string
                                   (substring diff-long
                                              (length diff-short))
                                   buffer-file-coding-system t))))))

(unless (fboundp 'string-suffix-p)
  (defun string-suffix-p (suffix string  &optional ignore-case)
    "Return non-nil if SUFFIX is a suffix of STRING.
If IGNORE-CASE is non-nil, the comparison is done without paying
attention to case differences."
    (let ((start-pos (- (length string) (length suffix))))
      (and (>= start-pos 0)
           (eq t (compare-strings suffix nil nil string start-pos nil
                                  ignore-case))))))

(provide 'vlf-ediff)

;;; vlf-ediff.el ends here
