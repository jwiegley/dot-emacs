;;; lcs.el --- find out the longest common sequence

;;   Copyright (c) 2002-2003 by Alex Shinn, All rights reserved.
;;   Copyright (c) 2002-2003 by Shiro Kawai, All rights reserved.
;;   Copyright (c) 2006, 2012 by Jorgen Schaefer, All rights reserved.

;; Authors: Alex Shinn, Shiro Kawai
;; Maintainer: Jorgen Schaefer <forcer@forcix.cx>
;; URL: https://github.com/jorgenschaefer/circe/wiki/lcs

;;   Redistribution and use in source and binary forms, with or without
;;   modification, are permitted provided that the following conditions
;;   are met:

;;   1. Redistributions of source code must retain the above copyright
;;      notice, this list of conditions and the following disclaimer.

;;   2. Redistributions in binary form must reproduce the above copyright
;;      notice, this list of conditions and the following disclaimer in the
;;      documentation and/or other materials provided with the distribution.

;;   3. Neither the name of the authors nor the names of its contributors
;;      may be used to endorse or promote products derived from this
;;      software without specific prior written permission.

;;   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;;   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;;   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;;   A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;;   OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;;   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
;;   TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
;;   PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
;;   LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;   NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;   SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;;; Commentary:

;; lcs.el is a library for other Emacs Lisp programs not useful by
;; itself.

;; This library provides functions to find the Longest Common Sequence
;; (LCS) of two sequences. This is used to create a unified diff of to
;; two lists. See `lcs-unified-diff' for a useful function to be
;; called.

;; The code is more or less a literal translation of (part of)
;; Gauche's util/lcs.scm module to Emacs Lisp.

;;; Code:

(put 'lcs-for 'lisp-indent-function 4)
(defmacro lcs-for (var from to step &rest body)
  "A simple FOR loop macro.
Count VAR from FROM to TO by stepsize STEP. Evaluate BODY in each
iteration."
  (let ((sto (make-symbol "to"))
        (sstep (make-symbol "step")))
    `(let ((,var ,from)
           (,sto ,to)
           (,sstep ,step))
       (while (<= ,var ,sto)
         (progn
           ,@body)
         (setq ,var (+ ,var ,sstep))))))

(defun lcs-split-at (lis pos)
  "Return a cons cell of the first POS elements of LIS and the rest."
  (let ((head nil))
    (while (> pos 0)
      (setq head (cons (car lis)
                       head)
            pos (- pos 1)
            lis (cdr lis)))
    (cons (reverse head)
          lis)))

(defun lcs-finish (M+N V_l vl V_r vr)
  "Finalize the LCS algorithm.
Should be used only by `lcs-with-positions'."
  (let ((maxl 0)
        (r '()))
    (lcs-for i (- M+N) M+N 1
      (when (> (funcall vl i)
               maxl)
        (setq maxl (funcall vl i)
              r (funcall vr i))))
    (list maxl (reverse r))))

(defun lcs-with-positions (a-ls b-ls &optional equalp)
  "Return the longest common subsequence (LCS) of A-LS and B-LS.
EQUALP can be any procedure which returns non-nil when two
elements should be considered equal."
  (let* ((A (vconcat a-ls))
         (B (vconcat b-ls))
         (N (length A))
         (M (length B))
         (M+N (+ M N))
         (V_d (make-vector (+ 1 (* 2 M+N))
                           0))
         (V_r (make-vector (+ 1 (* 2 M+N))
                           nil))
         (V_l (make-vector (+ 1 (* 2 M+N))
                           0))
         (vd (lambda (i &optional x)
               (if x
                   (aset V_d (+ i M+N) x)
                 (aref V_d (+ i M+N)))))
         (vr (lambda (i &optional x)
               (if x
                   (aset V_r (+ i M+N) x)
                 (aref V_r (+ i M+N)))))
         (vl (lambda (i &optional x)
               (if x
                   (aset V_l (+ i M+N) x)
                 (aref V_l (+ i M+N))))))
    (when (not equalp)
      (setq equalp 'equal))
    (catch 'return
      (if (= M+N 0)
          (throw 'return '(0 ()))
        (lcs-for d 0 M+N 1
          (lcs-for k (- d) d 2
            (let ((x nil)
                  (y nil)
                  (l nil)
                  (r nil))
              (if (or (= k (- d))
                      (and (not (= k d))
                           (< (funcall vd (- k 1))
                              (funcall vd (+ k 1)))))
                  (setq x (funcall vd (+ k 1))
                        l (funcall vl (+ k 1))
                        r (funcall vr (+ k 1)))
                (setq x (+ 1 (funcall vd (- k 1)))
                      l (funcall vl (- k 1))
                      r (funcall vr (- k 1))))
              (setq y (- x k))
              (while (and (< x N)
                          (< y M)
                          (funcall equalp (aref A x) (aref B y)))
                (setq r (cons (list (aref A x) x y)
                              r)
                      x (+ x 1)
                      y (+ y 1)
                      l (+ l 1)))
              (funcall vd k x)
              (funcall vr k r)
              (funcall vl k l)
              (when (and (>= x N)
                         (>= y M))
                (throw 'return(lcs-finish M+N V_l vl V_r vr)))))))
      (error "Can't happen"))))

(defun lcs-unified-diff (a b &optional equalp)
  "Return a unified diff of the lists A and B.
EQUALP should can be a procedure that returns non-nil when two
elements of A and B should be considered equal. It's `equal' by
default."
  (let ((common (cadr (lcs-with-positions a b equalp)))
        (a a)
        (a-pos 0)
        (b b)
        (b-pos 0)
        (diff '()))
    (while common
      (let* ((elt (car common))
             (a-off (nth 1 elt))
             (a-skip (- a-off a-pos))
             (b-off (nth 2 elt))
             (b-skip (- b-off b-pos))
             (a-split (lcs-split-at a a-skip))
             (a-head (car a-split))
             (a-tail (cdr a-split))
             (b-split (lcs-split-at b b-skip))
             (b-head (car b-split))
             (b-tail (cdr b-split)))
        (setq diff (append diff
                           (mapcar (lambda (a)
                                     `(- ,a))
                                   a-head)
                           (mapcar (lambda (b)
                                     `(+ ,b))
                                   b-head)
                           `((! ,(car elt))))

              common (cdr common)
              a (cdr a-tail)
              a-pos (+ a-off 1)
              b (cdr b-tail)
              b-pos (+ b-off 1))))
    (append diff
            (mapcar (lambda (a)
                      `(- ,a))
                    a)
            (mapcar (lambda (b)
                      `(+ ,b))
                    b))))

(provide 'lcs)
;;; lcs.el ends here
