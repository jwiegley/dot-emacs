;;; memory-usage.el --- Analyze the memory usage of Emacs in various ways

;; Copyright (C) 2002, 2004, 2012  Free Software Foundation, Inc.

;; Author: Stefan Monnier <monnier@cs.yale.edu>
;; Keywords: maint
;; Version: 0.1

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
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

;; This package provides the command `memory-usage', which lists all
;; buffers and how much memory they use.

;;; Code:

(defvar memory-usage-word-size (ceiling (/ (log most-positive-fixnum 2) 8))
  "Size of a Lisp word box in bytes.")

(defun memory-usage-buffer-size-bytes (b)
  "Return total number of bytes in the buffer contents."
  (with-current-buffer b
    (save-restriction
      (widen)
      (- (position-bytes (point-max)) (position-bytes (point-min))))))

(defun memory-usage-buffer-gap-bytes (b)
  "Return total number of bytes in the buffer gap."
  (with-current-buffer b
    (gap-size)))

(defun memory-usage-buffer-total-bytes (b)
  "Return total number of ralloc bytes used by buffer."
  (with-current-buffer b
    (save-restriction
      (widen)
      (+ (position-bytes (point-max))
	 (- (position-bytes (point-min)))
	 (gap-size)))))

(defun memory-usage-mult-cons (n c)
  (setq n (* n memory-usage-word-size))
  (cons (* n (car c)) (* n (cdr c))))

(defun memory-usage-format (bytes)
  (setq bytes (/ bytes 1024.0))
  (let ((units '(;; "B"
                 "kB" "MB" "GB" "TB")))
    (while (>= bytes 1024)
      (setq bytes (/ bytes 1024.0))
      (setq units (cdr units)))
    (cond
     ;; ((integerp bytes) (format "%4d%s" bytes (car units)))
     ((>= bytes 100) (format "%4.0f%s" bytes (car units)))
     ((>= bytes 10) (format "%4.1f%s" bytes (car units)))
     (t (format "%4.2f%s" bytes (car units))))))

;;;###autoload
(defun memory-usage ()
  "List all buffers and their memory usage."
  (interactive)
  (pop-to-buffer (get-buffer-create "*Buffer Details*"))
  (erase-buffer)
  (let* ((bufs (buffer-list))
	 (num (length bufs))
	 (gc-stats (garbage-collect))
	 (conses    (memory-usage-mult-cons 2 (nth 0 gc-stats)))
	 (symbols   (memory-usage-mult-cons 6 (nth 1 gc-stats)))
	 (markers   (memory-usage-mult-cons 5 (nth 2 gc-stats)))
	 (chars     (nth 3 gc-stats))
	 (vectors   (nth 4 gc-stats))
	 (floats    (memory-usage-mult-cons 2 (nth 5 gc-stats)))
	 (intervals (memory-usage-mult-cons 7 (nth 6 gc-stats)))
         (strings   (memory-usage-mult-cons 4 (nth 7 gc-stats))))
    (if (consp vectors) (setq vectors (cdr vectors)))
    (insert (format "Garbage collection stats:\n%s\n\n =>" gc-stats))
    (dolist (x `(("cons cells" . ,conses)
                 ("symbols" . ,symbols)
                 ("markers" . ,markers)
                 ("floats" . ,floats)
                 ("intervals" . ,intervals)
                 ("string headers" . ,strings)))
      (insert (format "\t%s (+ %s dead) in %s\n"
                    (memory-usage-format (cadr x))
                    (memory-usage-format (cddr x))
                    (car x))))
    (insert (format "\t%s of string chars\n" (memory-usage-format chars)))
    (insert (format "\t%s of vector slots\n" (memory-usage-format vectors)))
    (let ((live (+ (car conses)
                   (car symbols)
                   (car markers)
                   (car floats)
                   (car intervals)
                   (car strings)
                   chars
		   vectors))
          (dead (+ (cdr conses)
                   (cdr symbols)
                   (cdr markers)
                   (cdr floats)
                   (cdr intervals)
                   (cdr strings))))

      (insert (format "\nTotal in lisp objects: %s (live %s, dead %s)\n\n"
                      (memory-usage-format (+ dead live))
                      (memory-usage-format live)
                      (memory-usage-format dead))))

    (insert
     (format "Buffer ralloc memory usage:\n%d buffers\n%s total (%s in gaps)\n"
             num
             (memory-usage-format
              (apply #'+ (mapcar #'memory-usage-buffer-total-bytes bufs)))
             (memory-usage-format
              (apply #'+ (mapcar #'memory-usage-buffer-gap-bytes bufs)))))
    (insert (format "%10s\t%s\t%s\n\n" "Size" "Gap" "Name"))
    (insert (mapconcat
	     (lambda (b)
	       (format "%10d\t%s\t%s"
		       (memory-usage-buffer-size-bytes b)
		       (memory-usage-buffer-gap-bytes b)
		       (buffer-name b)))
	     (sort bufs (lambda (b1 b2)
			  (> (memory-usage-buffer-size-bytes b1)
                             (memory-usage-buffer-size-bytes b2))))
	     "\n"))
    (insert "\n"))
  (goto-char (point-min)))

(defun memory-usage-find-large-variables ()
  "Find variables whose printed representation takes over 100KB."
  (interactive)
  (let ((min-size (* 100 1024)))
    (pop-to-buffer "*Memory Explorer*")
    (delete-region (point-min) (point-max))
    ;; First find large global variables.
    (mapatoms
     (lambda (sym)
       (let ((size (or (and (boundp sym)
                            (length (prin1-to-string (symbol-value sym))))
                       0)))
         (when (> size min-size)
           (insert (format "%d\tGlobal\t%s\n"
                           size
                           (symbol-name sym)))))))
    ;; Second find large buffer-local variables.
    (mapc
     (lambda (buffer)
       (let ((holder ""))
         (with-current-buffer buffer
           (mapc
            (lambda (var-cons)
              (let ((size (or (and (consp var-cons)
                                   (length (prin1-to-string (cdr var-cons))))
                              0)))
                (if (> size min-size)
                    (setq holder (format "%d\t%s\t%s\n"
                                         size (buffer-name buffer)
                                         (symbol-name (car var-cons)))))))
            (buffer-local-variables)))
         (insert holder)))
     (buffer-list))
    (sort-numeric-fields 1 (point-min) (point-max))))

(provide 'memory-usage)
;;; memory-usage.el ends here
