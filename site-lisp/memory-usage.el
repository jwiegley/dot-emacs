;;; memory-usage.el --- Analyze the memory usage of Emacs in various ways

;; Copyright (C) 2002, 2004  Free Software Foundation, Inc.

;; Author: Stefan Monnier <monnier@cs.yale.edu>
;; Keywords: maint

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

;; 

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
    (insert (format "Garbage collection stats:\n%s\n\n =>" gc-stats))
    (insert (format "\t%d+%d bytes in cons cells\n" (car conses) (cdr conses)))
    (insert (format "\t%d+%d bytes in symbols\n" (car symbols) (cdr symbols)))
    (insert (format "\t%d+%d bytes in markers\n" (car markers) (cdr markers)))
    (insert (format "\t%d+%d bytes in floats\n" (car floats) (cdr floats)))
    (insert (format "\t%d+%d bytes in intervals\n" (car intervals) (cdr intervals)))
    (insert (format "\t%d+%d bytes in string headers\n" (car strings) (cdr strings)))
    (insert (format "\t%d bytes of string chars\n" chars))
    (insert (format "\t%d bytes of vector headers\n" (* 2 memory-usage-word-size (car vectors))))
    (insert (format "\t%d bytes of vector slots\n" (* memory-usage-word-size (cdr vectors))))

    (let ((live (+ (car conses)
                   (car symbols)
                   (car markers)
                   (car floats)
                   (car intervals)
                   (car strings)
                   chars
                   (* 2 memory-usage-word-size (car vectors))
                   (* memory-usage-word-size (cdr vectors))))
          (dead (+ (cdr conses)
                   (cdr symbols)
                   (cdr markers)
                   (cdr floats)
                   (cdr intervals)
                   (cdr strings))))

      (insert (format "\nTotal bytes in lisp objects: %d (live %d, dead %d)\n\n"
                      (+ dead live) live dead)))

    (insert (format "Buffer ralloc memory usage:\n%d buffers\n%d bytes total (%d in gaps)\n"
		    num
		    (apply #'+ (mapcar #'memory-usage-buffer-total-bytes bufs))
		    (apply #'+ (mapcar #'memory-usage-buffer-gap-bytes bufs))))
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


(provide 'memory-usage)
;; arch-tag: 04e012f0-3c59-4319-8d1a-e86204671ec5
;;; memory-usage.el ends here
