;;; vlf-tune.el --- VLF tuning operations  -*- lexical-binding: t -*-

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Keywords: large files, batch size, performance
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
;; This package provides wrappers for basic chunk operations that add
;; profiling and automatic tuning of `vlf-batch-size'.

;;; Code:

(defgroup vlf nil "View Large Files in Emacs."
  :prefix "vlf-" :group 'files)

(defcustom vlf-batch-size 1000000
  "Defines how large each batch of file data initially is (in bytes)."
  :group 'vlf :type 'integer)
(put 'vlf-batch-size 'permanent-local t)

(defcustom vlf-tune-enabled t
  "Whether to allow automatic change of batch size.
If nil, completely disable.  If `stats', maintain measure statistics,
but don't change batch size.  If t, measure and change."
  :group 'vlf :type '(choice (const :tag "Enabled" t)
                             (const :tag "Just statistics" stats)
                             (const :tag "Disabled" nil)))

(defvar vlf-file-size 0 "Total size in bytes of presented file.")
(make-variable-buffer-local 'vlf-file-size)
(put 'vlf-file-size 'permanent-local t)

(defun vlf-tune-ram-size ()
  "Try to determine RAM size in bytes."
  (if (executable-find "free")
      (let* ((free (shell-command-to-string "free"))
             (match-from (string-match "[[:digit:]]+" free)))
        (if match-from
            (* 1000 (string-to-number (substring free match-from
                                                 (match-end 0))))))))

(defcustom vlf-tune-max (max (let ((ram-size (vlf-tune-ram-size)))
                               (if ram-size
                                   (/ ram-size 20)
                                 0))
                             large-file-warning-threshold)
  "Maximum batch size in bytes when auto tuning.
Avoid increasing this after opening file with VLF."
  :group 'vlf :type 'integer)

(defcustom vlf-tune-step (/ vlf-tune-max 10000)
  "Step used for tuning in bytes.
Avoid decreasing this after opening file with VLF."
  :group 'vlf :type 'integer)

(defcustom vlf-tune-load-time 1.0
  "How many seconds should batch take to load for best user experience."
  :group 'vlf :type 'float)

(defvar vlf-tune-insert-bps nil
  "Vector of bytes per second insert measurements.")
(make-variable-buffer-local 'vlf-tune-insert-bps)
(put 'vlf-tune-insert-bps 'permanent-local t)

(defvar vlf-tune-insert-raw-bps nil
  "Vector of bytes per second non-decode insert measurements.")
(make-variable-buffer-local 'vlf-tune-insert-raw-bps)
(put 'vlf-tune-insert-raw-bps 'permanent-local t)

(defvar vlf-tune-encode-bps nil
  "Vector of bytes per second encode measurements.")
(make-variable-buffer-local 'vlf-tune-encode-bps)
(put 'vlf-tune-encode-bps 'permanent-local t)

(defvar vlf-tune-write-bps nil
  "Vector of bytes per second write measurements.")

(defvar vlf-tune-hexl-bps nil
  "Vector of bytes per second hexlify measurements.")

(defvar vlf-tune-dehexlify-bps nil
  "Vector of bytes per second dehexlify measurements.")

(defvar vlf-start-pos)
(defvar hexl-bits)
(defvar hexl-max-address)
(declare-function hexl-line-displen "hexl")
(declare-function dehexlify-buffer "hexl")

(defun vlf-tune-copy-profile (from-buffer &optional to-buffer)
  "Copy specific profile vectors of FROM-BUFFER to TO-BUFFER.
If TO-BUFFER is nil, copy to current buffer."
  (let (insert-bps insert-raw-bps encode-bps)
    (with-current-buffer from-buffer
      (setq insert-bps vlf-tune-insert-bps
            insert-raw-bps vlf-tune-insert-raw-bps
            encode-bps vlf-tune-encode-bps))
    (if to-buffer
        (with-current-buffer to-buffer
          (setq vlf-tune-insert-bps insert-bps
                vlf-tune-insert-raw-bps insert-raw-bps
                vlf-tune-encode-bps encode-bps))
      (setq vlf-tune-insert-bps insert-bps
            vlf-tune-insert-raw-bps insert-raw-bps
            vlf-tune-encode-bps encode-bps))))

(defun vlf-tune-closest-index (size)
  "Get closest measurement index corresponding to SIZE."
  (let ((step (float vlf-tune-step)))
    (max 0 (1- (min (round size step) (round vlf-tune-max step))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; profiling

(defun vlf-tune-initialize-measurement ()
  "Initialize measurement vector."
  (make-vector (1- (/ vlf-tune-max vlf-tune-step)) nil))

(defmacro vlf-tune-add-measurement (vec size time)
  "Add at an appropriate position in VEC new SIZE TIME measurement.
VEC is a vector of (mean time . count) elements ordered by size."
  `(when (and vlf-tune-enabled (not (zerop ,size)))
     (or ,vec (setq ,vec (vlf-tune-initialize-measurement)))
     (let* ((idx (vlf-tune-closest-index ,size))
            (existing (aref ,vec idx)))
       (aset ,vec idx (if (consp existing)
                          (let ((count (1+ (cdr existing)))) ;recalculate mean
                            (cons (/ (+ (* (1- count) (car existing))
                                        (/ ,size ,time))
                                     count)
                                  count))
                        (cons (/ ,size ,time) 1))))))

(defmacro vlf-time (&rest body)
  "Get timing consed with result of BODY execution."
  `(if vlf-tune-enabled
       (let* ((time (float-time))
              (result (progn ,@body)))
         (cons (- (float-time) time) result))
     (let ((result (progn ,@body)))
       (cons nil result))))

(defun vlf-tune-insert-file-contents (start end)
  "Extract decoded file bytes START to END and save time it takes."
  (let ((result (vlf-time (insert-file-contents buffer-file-name
                                                nil start end))))
    (vlf-tune-add-measurement vlf-tune-insert-bps
                              (- end start) (car result))
    (cdr result)))

(defun vlf-tune-insert-file-contents-literally (start end &optional file)
  "Insert raw file bytes START to END and save time it takes.
FILE if given is filename to be used, otherwise `buffer-file-name'."
  (let ((result (vlf-time (insert-file-contents-literally
                           (or file buffer-file-name) nil start end))))
    (vlf-tune-add-measurement vlf-tune-insert-raw-bps
                              (- end start) (car result))
    (cdr result)))

(defun vlf-tune-encode-length (start end)
  "Get length of encoded region START to END and save time it takes."
  (let ((result (vlf-time (length (encode-coding-region
                                   start end
                                   buffer-file-coding-system t)))))
    (vlf-tune-add-measurement vlf-tune-encode-bps
                              (cdr result) (car result))
    (cdr result)))

(defun vlf-tune-write (start end append visit size &optional file-name)
  "Save buffer and save time it takes.
START, END, APPEND, VISIT have same meaning as in `write-region'.
SIZE is number of bytes that are saved.
FILE-NAME if given is to be used instead of `buffer-file-name'."
  (let* ((file (or file-name buffer-file-name))
         (time (car (vlf-time (write-region start end file append
                                            visit)))))
    (or (file-remote-p file) ;writing to remote files can include network copying
        (vlf-tune-add-measurement vlf-tune-write-bps size time))))

(defun vlf-hexl-adjust-addresses ()
  "Adjust hexl address indicators according to `vlf-start-pos'."
  (let ((pos (point))
        (address vlf-start-pos))
    (goto-char (point-min))
    (while (re-search-forward "^[[:xdigit:]]+" nil t)
      (replace-match (format "%08x" address))
      (setq address (+ address hexl-bits)))
    (goto-char pos)))

(defun vlf-tune-hexlify ()
  "Activate `hexl-mode' and save time it takes."
  (let* ((no-adjust (zerop vlf-start-pos))
         (time (car (vlf-time (hexlify-buffer)
                              (or no-adjust
                                  (vlf-hexl-adjust-addresses))))))
    (setq hexl-max-address (+ (* (/ (1- (buffer-size))
                                    (hexl-line-displen)) 16) 15))
    (or no-adjust
        (vlf-tune-add-measurement vlf-tune-hexl-bps
                                  hexl-max-address time))))

(defun vlf-tune-dehexlify ()
  "Exit `hexl-mode' and save time it takes."
  (let ((time (car (vlf-time (dehexlify-buffer)))))
    (vlf-tune-add-measurement vlf-tune-dehexlify-bps
                              hexl-max-address time)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; tuning

(defun vlf-tune-approximate-nearby (vec index)
  "VEC has value for INDEX, approximate to closest available."
  (let ((val 0)
        (left-idx (1- index))
        (right-idx (1+ index))
        (min-idx (max 0 (- index 5)))
        (max-idx (min (+ index 6)
                      (1- (/ (min vlf-tune-max
                                  (/ (1+ vlf-file-size) 2))
                             vlf-tune-step)))))
    (while (and (zerop val) (or (<= min-idx left-idx)
                                (< right-idx max-idx)))
      (if (<= min-idx left-idx)
          (let ((left (aref vec left-idx)))
            (cond ((consp left) (setq val (car left)))
                  ((numberp left) (setq val left)))))
      (if (< right-idx max-idx)
          (let ((right (aref vec right-idx)))
            (if (consp right)
                (setq right (car right)))
            (and (numberp right) (not (zerop right))
                 (setq val (if (zerop val)
                               right
                             (/ (+ val right) 2))))))
      (setq left-idx (1- left-idx)
            right-idx (1+ right-idx)))
    val))

(defmacro vlf-tune-get-value (vec index &optional dont-approximate)
  "Get value from VEC for INDEX.
If missing, approximate from nearby measurement,
unless DONT-APPROXIMATE is t."
  `(if ,vec
       (let ((val (aref ,vec ,index)))
         (cond ((consp val) (car val))
               ((null val)
                ,(if dont-approximate
                     `(aset ,vec ,index 0)
                   `(vlf-tune-approximate-nearby ,vec ,index)))
               ((zerop val) ;index has been tried before, yet still no value
                ,(if dont-approximate
                     `(aset ,vec ,index
                            (vlf-tune-approximate-nearby ,vec ,index))
                   `(vlf-tune-approximate-nearby ,vec ,index)))
               (t val)))
     most-positive-fixnum))

(defmacro vlf-tune-get-vector (key)
  "Get vlf-tune vector corresponding to KEY."
  `(cond ((eq ,key :insert) vlf-tune-insert-bps)
         ((eq ,key :raw) vlf-tune-insert-raw-bps)
         ((eq ,key :encode) vlf-tune-encode-bps)
         ((eq ,key :write) vlf-tune-write-bps)
         ((eq ,key :hexl) vlf-tune-hexl-bps)
         ((eq ,key :dehexlify) vlf-tune-dehexlify-bps)))

(defun vlf-tune-assess (type coef index &optional approximate)
  "Get measurement value according to TYPE, COEF and INDEX.
If APPROXIMATE is t, do approximation for missing values."
  (* coef (or (if approximate
                  (vlf-tune-get-value (vlf-tune-get-vector type)
                                      index)
                (vlf-tune-get-value (vlf-tune-get-vector type)
                                    index t))
              0)))

(defun vlf-tune-score (types index &optional approximate time-max)
  "Calculate cumulative speed over TYPES for INDEX.
If APPROXIMATE is t, do approximation for missing values.
If TIME-MAX is non nil, return cumulative time instead of speed.
If it is number, stop as soon as cumulative time gets equal or above."
  (catch 'result
    (let ((time 0)
          (size (* (1+ index) vlf-tune-step))
          (cut-time (numberp time-max)))
      (dolist (el types (if time-max time
                          (/ size time)))
        (let ((bps (if (consp el)
                       (vlf-tune-assess (car el) (cadr el) index
                                        approximate)
                     (vlf-tune-assess el 1.0 index approximate))))
          (if (zerop bps)
              (throw 'result nil)
            (setq time (+ time (/ size bps)))
            (and cut-time (<= time-max time)
                 (throw 'result nil))))))))

(defun vlf-tune-conservative (types &optional index)
  "Adjust `vlf-batch-size' to best nearby value over TYPES.
INDEX if given, specifies search independent of current batch size."
  (if (eq vlf-tune-enabled t)
      (let* ((half-max (/ (1+ vlf-file-size) 2))
             (idx (or index (vlf-tune-closest-index vlf-batch-size)))
             (curr (if (< half-max (* idx vlf-tune-step)) t
                     (vlf-tune-score types idx))))
        (if curr
            (let ((prev (if (zerop idx) t
                          (vlf-tune-score types (1- idx)))))
              (if prev
                  (let ((next (if (or (eq curr t)
                                      (< half-max (* (1+ idx)
                                                     vlf-tune-step)))
                                  t
                                (vlf-tune-score types (1+ idx)))))
                    (cond ((null next)
                           (setq vlf-batch-size (* (+ 2 idx)
                                                   vlf-tune-step)))
                          ((eq curr t)
                           (or (eq prev t)
                               (setq vlf-batch-size
                                     (* idx vlf-tune-step))))
                          (t (let ((best-idx idx))
                               (and (numberp prev) (< curr prev)
                                    (setq curr prev
                                          best-idx (1- idx)))
                               (and (numberp next) (< curr next)
                                    (setq best-idx (1+ idx)))
                               (setq vlf-batch-size
                                     (* (1+ best-idx)
                                        vlf-tune-step))))))
                (setq vlf-batch-size (* idx vlf-tune-step))))
          (setq vlf-batch-size (* (1+ idx) vlf-tune-step))))))

(defun vlf-tune-binary (types min max)
  "Adjust `vlf-batch-size' to optimal value using binary search, \
optimizing over TYPES.
MIN and MAX specify interval of indexes to search."
  (let ((sum (+ min max)))
    (if (< (- max min) 3)
        (vlf-tune-conservative types (/ sum 2))
      (let* ((left-idx (round (+ sum (* 2 min)) 4))
             (left (vlf-tune-score types left-idx)))
        (if left
            (let* ((right-idx (round (+ sum (* 2 max)) 4))
                   (right (vlf-tune-score types right-idx)))
              (cond ((null right)
                     (setq vlf-batch-size (* (1+ right-idx)
                                             vlf-tune-step)))
                    ((< left right)
                     (vlf-tune-binary types (/ (1+ sum) 2) max))
                    (t (vlf-tune-binary types min (/ sum 2)))))
          (setq vlf-batch-size (* (1+ left-idx) vlf-tune-step)))))))

(defun vlf-tune-linear (types max-idx)
  "Adjust `vlf-batch-size' to optimal known value using linear search.
Optimize over TYPES up to MAX-IDX."
  (let ((best-idx 0)
        (best-bps 0)
        (idx 0))
    (while (< idx max-idx)
      (let ((bps (vlf-tune-score types idx t)))
        (and bps (< best-bps bps)
             (setq best-idx idx
                   best-bps bps)))
      (setq idx (1+ idx)))
    (setq vlf-batch-size (* (1+ best-idx) vlf-tune-step))))

(defun vlf-tune-batch (types &optional linear file)
  "Adjust `vlf-batch-size' to optimal value optimizing on TYPES.
TYPES is alist of elements that may be of form (type coef) or
non list values in which case coeficient is assumed 1.
Types can be :insert, :raw, :encode, :write, :hexl or :dehexlify.
If LINEAR is non nil, use brute-force.  In case requested measurement
is missing, stop search and set `vlf-batch-size' to this value.
FILE if given is filename to be used, otherwise `buffer-file-name'.
Suitable for multiple batch operations."
  (if (eq vlf-tune-enabled t)
      (let ((max-idx (1- (/ (min vlf-tune-max
                                 (/ (1+ vlf-file-size) 2))
                            vlf-tune-step))))
        (if linear
            (vlf-tune-linear types max-idx)
          (let ((batch-size vlf-batch-size))
            (cond ((file-remote-p (or file buffer-file-name))
                   (vlf-tune-conservative types))
                  ((<= 1 max-idx)
                   (if (< max-idx 3)
                       (vlf-tune-conservative types (/ max-idx 2))
                     (vlf-tune-binary types 0 max-idx))))
            (if (= batch-size vlf-batch-size) ;local maxima?
                (vlf-tune-linear types max-idx)))))))

(defun vlf-tune-optimal-load (types &optional min-idx max-idx)
  "Get best batch size according to existing measurements over TYPES.
Best considered where primitive operations total is closest to
`vlf-tune-load-time'.  If MIN-IDX and MAX-IDX are given,
confine search to this region."
  (if (eq vlf-tune-enabled t)
      (progn
        (setq min-idx (max 0 (or min-idx 0))
              max-idx (min (or max-idx vlf-tune-max)
                           (1- (/ (min vlf-tune-max
                                       (/ (1+ vlf-file-size) 2))
                                  vlf-tune-step))))
        (let* ((idx min-idx)
               (best-idx idx)
               (best-time-diff vlf-tune-load-time)
               (all-less t)
               (all-more t))
          (while (and (not (zerop best-time-diff)) (< idx max-idx))
            (let ((time-diff (vlf-tune-score types idx t
                                             (+ vlf-tune-load-time
                                                best-time-diff))))
              (if time-diff
                  (progn
                    (setq time-diff (if (< vlf-tune-load-time time-diff)
                                        (progn (setq all-less nil)
                                               (- time-diff
                                                  vlf-tune-load-time))
                                      (setq all-more nil)
                                      (- vlf-tune-load-time time-diff)))
                    (if (< time-diff best-time-diff)
                        (setq best-idx idx
                              best-time-diff time-diff)))
                (setq all-less nil)))
            (setq idx (1+ idx)))
          (* vlf-tune-step (1+ (cond ((or (zerop best-time-diff)
                                          (eq all-less all-more))
                                      best-idx)
                                     (all-less max-idx)
                                     (t min-idx))))))
    vlf-batch-size))

(defun vlf-tune-load (types &optional region)
  "Adjust `vlf-batch-size' slightly to better load time.
Optimize on TYPES on the nearby REGION.  Use 2 if REGION is nil."
  (when (eq vlf-tune-enabled t)
    (or region (setq region 2))
    (let ((idx (vlf-tune-closest-index vlf-batch-size)))
      (setq vlf-batch-size (vlf-tune-optimal-load types (- idx region)
                                                  (+ idx 1 region))))))

(provide 'vlf-tune)

;;; vlf-tune.el ends here
