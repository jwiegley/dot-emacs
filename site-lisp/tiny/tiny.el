;;; tiny.el --- Quickly generate linear ranges in Emacs

;; Copyright (C) 2013  Oleh Krehel

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/tiny
;; Version: 0.1

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; Setup:
;; In ~/.emacs:
;;     (require 'tiny)
;;     (tiny-setup-default)
;;
;; Usage:
;; This extension's main command is `tiny-expand'.
;; It's meant to quickly generate linear ranges, e.g. 5, 6, 7, 8.
;; Some elisp proficiency is an advantage, since you can transform
;; your numeric range with an elisp expression.
;;
;; There's also some emphasis on the brevity of the expression to be
;; expanded: e.g. instead of typing (+ x 2), you can do +x2.
;; You can still do the full thing, but +x2 would save you some
;; key strokes.
;;
;; You can test out the following snippets
;; by positioning the point at the end of the expression
;; and calling `tiny-expand' (default shortcut is C-;):
;;
;; m10
;; m5 10
;; m5,10
;; m5 10*xx
;; m5 10*xx%x
;; m5 10*xx|0x%x
;; m25+x?a%c
;; m25+x?A%c
;; m97,122(string x)
;; m97,122stringxx
;; m97,120stringxupcasex
;; m97,120stringxupcasex)x
;; m\n;; 10|%(+ x x) and %(* x x) and %s
;; m10*2+3x
;; m\n;; 10expx
;; m5\n;; 20expx%014.2f
;; m7|%(expt 2 x)
;; m, 7|0x%02x
;; m10|%0.2f
;; m1\n14|*** TODO http://emacsrocks.com/e%02d.html
;; m1\n10|convert img%s.jpg -monochrome -resize 50%% -rotate 180 img%s_mono.pdf
;; (setq foo-list '(m1 11+x96|?%c))
;; m1\n10listx+x96|convert img%s.jpg -monochrome -resize 50%% -rotate 180 img%c_mono.pdf
;; m1\n10listxnthxfoo-list|convert img%s.jpg -monochrome -resize 50%% -rotate 180 img%c_mono.pdf
;; m\n;; 16list*xxx)*xx%s:%s:%s
;; m\n8|**** TODO Learning from Data Week %(+ x 2) \nSCHEDULED: <%(date "Oct 7" (* x 7))> DEADLINE: <%(date "Oct 14" (* x 7))>
;;
;; As you might have guessed, the syntax is as follows:
;; m[<range start:=0>][<separator:= >]<range end>[Lisp expr]|[format expr]
;;
;; x is the default var in the elisp expression.  It will take one by one
;; the value of all numbers in the range.
;;
;; | means that elisp expr has ended and format expr has begun.
;; It can be omitted if the format expr starts with %.
;; The keys are the same as for format.
;; In addition %(sexp) forms are allowed.  The sexp can depend on x.
;;
;; Note that multiple % can be used in the format expression.
;; In that case:
;; * if the Lisp expression returns a list, the members of this list
;;   are used in the appropriate place.
;; * otherwise, it's just the result of the expression repeated as
;;   many times as necessary.

;;; Code:

(eval-when-compile
  (require 'cl))
(require 'help-fns)
(require 'org)

(defvar tiny-beg nil
  "Last matched snippet start position.")

(defvar tiny-end nil
  "Last matched snippet end position.")

;;;###autoload
(defun tiny-expand ()
  "Expand current snippet.
It polls the expander functions one by one
if they can expand the thing at point.
First one to return a string succeeds.
These functions are expected to set `tiny-beg' and `tiny-end'
to the bounds of the snippet that they matched.
At the moment, only `tiny-mapconcat' is supported.
`tiny-mapconcat2' should be added to expand rectangles."
  (interactive)
  (let ((str (tiny-mapconcat)))
    (when str
      (delete-region tiny-beg tiny-end)
      (insert str)
      (tiny-replace-this-sexp))))

(defun tiny-setup-default ()
  "Setup shortcuts."
  (global-set-key (kbd "C-;") 'tiny-expand))

;;;###autoload
(defun tiny-replace-this-sexp ()
  "Eval and replace the current sexp.
On error go up list and try again."
  (interactive)
  (if (region-active-p)
      (let ((s (buffer-substring-no-properties
                (region-beginning)
                (region-end))))
        (delete-region (region-beginning)
                       (region-end))
        (insert (format "%s" (eval (read s)))))
    (catch 'success
      (while t
        (ignore-errors
          (unless (looking-back ")")
            (error "Bad location"))
          (let ((sexp (preceding-sexp)))
            (if (eq (car sexp) 'lambda)
                (error "Lambda evaluates to itself")
              (let ((value (eval sexp)))
                (kill-sexp -1)
                (insert (format "%s" value))
                (throw 'success t)))))
        ;; if can't replace, go up list
        (condition-case nil
            (tiny-up-list)
          (error
           (message "reached the highest point, couldn't eval.")
           (throw 'success nil)))))))

(defun tiny-up-list ()
  "An `up-list' that can exit from string.
Must throw an error when can't go up further."
  (interactive)
  ;; check if inside string
  (let ((p (nth 8 (syntax-ppss))))
    (when (eq (char-after p) ?\")
      ;; go to beginning for string
      (goto-char p)))
  (up-list))

(defun tiny-mapconcat ()
  "Format output of `tiny-mapconcat-parse'.
Defaults are used in place of null values."
  (let ((parsed (tiny-mapconcat-parse)))
    (when parsed
      (let* ((n1 (or (nth 0 parsed) "0"))
             (s1 (or (nth 1 parsed) " "))
             (n2 (nth 2 parsed))
             (expr (or (nth 3 parsed) "x"))
             (lexpr (read expr))
             (n-have (if (and (listp lexpr) (eq (car lexpr) 'list))
                         (1- (length lexpr))
                       0))
             (expr (if (zerop n-have) `(list ,lexpr) lexpr))
             (n-have (if (zerop n-have) 1 n-have))
             (tes (tiny-extract-sexps (or (nth 4 parsed) "%s")))
             (fmt (car tes))
             (n-need (cl-count nil (cdr tes)))
             (idx -1)
             (format-expression
              (concat "(mapconcat (lambda(x) (let ((lst %s)) (format %S "
                      (mapconcat (lambda (x)
                                   (or x
                                       (if (>= (1+ idx) n-have)
                                           "x"
                                         (format "(nth %d lst)" (incf idx)))))
                                 (cdr tes)
                                 " ")
                      ")))(number-sequence %s %s) \"%s\")")))
        (unless (>= (read n1) (read n2))
          (format
           format-expression
           expr
           (replace-regexp-in-string "\\\\n" "\n" fmt)
           n1
           n2
           s1))))))

(defconst tiny-format-str
  (let ((flags "[+ #-0]\\{0,1\\}")
        (width "[0-9]*")
        (precision "\\(?:\\.[0-9]+\\)?")
        (character "[sdoxXefgcS]?"))
    (format "\\(%s%s%s%s\\)("
            flags width precision character)))

(defun tiny-extract-sexps (str)
  "Return (STR & FORMS).
Each element of FORMS corresponds to a `format'-style % form in STR.

  * %% forms are skipped
  * %(sexp) is replaced with %s in STR, and put in FORMS
  * the rest of forms are untouched in STR, and put as nil in FORMS"
  (let ((start 0)
        forms beg fexp)
    (condition-case nil
        (while (setq beg (string-match "%" str start))
          (setq start (1+ beg))

          (cond ((= ?% (aref str (1+ beg)))
                 (incf start))

                ((and (eq beg (string-match tiny-format-str str beg))
                      (setq fexp (match-string-no-properties 1 str)))
                 (incf beg (length fexp))
                 (destructuring-bind (sexp . end)
                     (read-from-string str beg)
                   (push
                    (replace-regexp-in-string "(date" "(tiny-date"
                                              (substring str beg end))
                    forms)
                   (setq str (concat (substring str 0 beg)
                                     (if (string= fexp "%") "s" "")
                                     (substring str end)))))
                (t (push nil forms))))
      (error (message "Malformed sexp: %s" (substring str beg))))
    (cons str (nreverse forms))))

(defun tiny-mapconcat-parse ()
  "Try to match a snippet of this form:
m[START][SEPARATOR]END[EXPR]|[FORMAT]

* START     - integer (defaults to 0)
* SEPARATOR - string  (defaults to \" \")
* END       - integer (required)
* EXPR      - Lisp expression: function body with argument x (defaults to x)
  Parens are optional if it's unambiguous:
  - `(* 2 (+ x 3))'  <-> *2+x3
  - `(exp x)'        <-> expx
  A closing paren may be added to resolve ambiguity:
  - `(* 2 (+ x 3) x) <-> *2+x3)
* FORMAT    - string, `format'-style (defaults to \"%s\")
  | separator can be omitted if FORMAT starts with %.

Return nil if nothing was matched, otherwise
 (START SEPARATOR END EXPR FORMAT)"
  (let ((case-fold-search nil)
        n1 s1 n2 expr fmt str
        n-uses)
    (when (catch 'done
            (cond
              ;; either start with a number
              ((looking-back "\\bm\\(-?[0-9]+\\)\\([^\n]*?\\)")
               (setq n1 (match-string-no-properties 1)
                     str (match-string-no-properties 2)
                     tiny-beg (match-beginning 0)
                     tiny-end (match-end 0))
               (when (zerop (length str))
                 (setq n2 n1
                       n1 nil)
                 (throw 'done t)))
              ;; else capture the whole thing
              ((looking-back "\\bm\\([^%|\n]*[0-9][^\n]*\\)")
               (setq str (match-string-no-properties 1)
                     tiny-beg (match-beginning 0)
                     tiny-end (match-end 0))
               (when (zerop (length str))
                 (throw 'done nil)))
              (t (throw 'done nil)))
            ;; at this point, `str' should be either [sep]<num>[expr][fmt]
            ;; or [expr][fmt]
            ;;
            ;; First, try to match [expr][fmt]
            (string-match "^\\(.*?\\)|?\\(%.*\\)?$" str)
            (setq expr (match-string-no-properties 1 str))
            (setq fmt (match-string-no-properties 2 str))
            ;; If it's a valid expression, we're done
            (when (setq expr (tiny-tokenize expr))
              (setq n2 n1
                    n1 nil)
              (throw 'done t))
            ;; at this point, `str' is [sep]<num>[expr][fmt]
            (if (string-match "^\\([^\n0-9]*?\\)\\(-?[0-9]+\\)\\(.*\\)?$" str)
                (setq s1 (match-string-no-properties 1 str)
                      n2 (match-string-no-properties 2 str)
                      str (match-string-no-properties 3 str))
              ;; here there's only n2 that was matched as n1
              (setq n2 n1
                    n1 nil))
            ;; match expr_fmt
            (unless (zerop (length str))
              (if (or (string-match "^\\([^\n%|]*?\\)|\\([^\n]*\\)?$" str)
                      (string-match "^\\([^\n%|]*?\\)\\(%[^\n]*\\)?$" str))
                  (progn
                    (setq expr (tiny-tokenize (match-string-no-properties 1 str)))
                    (setq fmt (match-string-no-properties 2 str)))
                (error "Couldn't match %s" str)))
            t)
      (when (equal expr "")
        (setq expr nil))
      (list n1 s1 n2 expr fmt))))

;; TODO: check for arity: this doesn't work: exptxy
(defun tiny-tokenize (str)
  "Transform shorthand Lisp expression STR to proper Lisp."
  (if (equal str "")
      ""
    (ignore-errors
      (let ((i 0) (j 1)
            (len (length str))
            sym s out allow-spc
            (n-paren 0)
            (expect-fun t))
        (while (< i len)
          (setq s (substring str i j))
          (when (cond
                  ((string= s "x")
                   (push s out)
                   (push " " out))
                  ((string= s " ")
                   (if allow-spc
                       t
                     (error "Unexpected \" \"")))
                  ;; special syntax to read chars
                  ((string= s "?")
                   (setq s (format "%s" (read (substring str i (incf j)))))
                   (push s out)
                   (push " " out))
                  ((string= s ")")
                   ;; expect a close paren only if it's necessary
                   (if (>= n-paren 0)
                       (decf n-paren)
                     (error "Unexpected \")\""))
                   (when (string= (car out) " ")
                     (pop out))
                   (push ")" out)
                   (push " " out))
                  ((string= s "(")
                   ;; open paren is used sometimes
                   ;; when there are numbers in the expression
                   (setq expect-fun t)
                   (incf n-paren)
                   (push "(" out))
                  ((progn (setq sym (intern-soft s))
                          (cond
                            ;; general functionp
                            ((not (eq t (help-function-arglist sym)))
                             (setq expect-fun)
                             (setq allow-spc t)
                             ;; (when (zerop n-paren) (push "(" out))
                             (unless (equal (car out) "(")
                               (push "(" out)
                               (incf n-paren))
                             t)
                            ((and sym (boundp sym) (not expect-fun))
                             t)))
                   (push s out)
                   (push " " out))
                  ((numberp (read s))
                   (let* ((num (string-to-number (substring str i)))
                          (num-s (format "%s" num)))
                     (push num-s out)
                     (push " " out)
                     (setq j (+ i (length num-s)))))
                  (t
                   (incf j)
                   nil))
            (setq i j)
            (setq j (1+ i))))
        ;; last space
        (when (string= (car out) " ")
          (pop out))
        (concat
         (apply #'concat (nreverse out))
         (make-string n-paren ?\)))))))

(defun tiny-date (s &optional shift)
  "Return date representation of S.
`org-mode' format is used.
Optional SHIFT argument is the integer amount of days to shift."
  (let* ((ct (decode-time (current-time)))
         (time (apply 'encode-time
                      (org-read-date-analyze
                       s nil
                       ct)))
         (formatter
          (if (equal (cl-subseq ct 1 3)
                     (cl-subseq (decode-time time) 1 3))
              "%Y-%m-%d %a"
            "%Y-%m-%d %a %H:%M")))
    (when shift
      (setq time (time-add time (days-to-time shift))))
    (format-time-string formatter time)))

(provide 'tiny)
;;; tiny.el ends here
