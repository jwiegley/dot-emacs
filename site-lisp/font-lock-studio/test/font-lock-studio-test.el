;;; font-lock-studio-test.el --- Regression tests for font-lock-studio.

;; Copyright (C) 2013-2014,2016 Anders Lindgren

;; Author: Anders Lindgren
;; Keywords: faces, tools

;; This program is free software: you can redistribute it and/or modify
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

;; This is test for the package `font-lock-studio'.
;;
;; The tests use the `ert' test framework, which is a part of Emacs.
;;
;; Some test use the package `faceup', which contain
;; `font-lock'-specific extensions to `ert'. You can download `faceup'
;; from `https://github.com/Lindydancer/faceup'.
;;
;; The tests in this modue range from unit test of specific functions
;; to back-to-back tests between font-lock-studio and the real
;; font-lock of real-world source code.
;;
;; In addition to `ert' tests, this module provides a number of
;; fictitious major modes, tailor-mode to test different aspected of
;; font-lock keywords.

;;; Code:

;; Note: The words "explain" and "explainer" exist both in the
;; vocabulary of `ert' and of `font-lock-studio', they do not mean the
;; same thing.

(require 'faceup)
(require 'font-lock-profiler)


;; Complex C files of the Emacs source distribution is used for
;; back-to-back tests with the normal font-lock engine and the engine
;; of font-lock-studio. If you Emacs wasn't built from sources, please
;; provide the location where the Emacs source is locate.
(defvar font-lock-studio-test-source-directory
  (let ((dir (expand-file-name "src" source-directory)))
    (when (and (file-directory-p dir) (file-readable-p dir))
      dir))
  "Directory where the C source files of Emacs can be found.
If nil, do not try to find the source code of functions and variables
defined in C.")


;; ----------------------------------------
;; Flatten match data
;;

(defun my-visualize (md)
  (font-lock-studio-flatten-match-data md))

(ert-deftest font-lock-studio-test-visualize-match-data ()
  ;; ----------
  (should (equal (my-visualize '()) '()))
  ;; ----------
  (should (equal (my-visualize '(10 20)) '((0 10 20))))
  ;; ----------
  ;; No overlap
  (should (equal (my-visualize '(10 20 30 40))
                 '((0 10 20) (1 30 40))))
  (should (equal (my-visualize '(10 20 nil nil 30 40))
                 '((0 10 20) (2 30 40))))
  ;; ----------
  ;; Overlaps fully

  ;; Exactly the same.
  (should (equal (my-visualize '(10 20 10 20))
                 '((1 10 20))))
  ;; End match.
  (should (equal (my-visualize '(10 20 0 20))
                 '((1 0 20))))
  ;; Beginning match.
  (should (equal (my-visualize '(10 20 10 30))
                 '((1 10 30))))

  ;; ----------
  ;; Partial overlap.


  ;; At end.
  (should (equal (my-visualize '(10 30 20 30))
                 '((0 10 20)
                   (1 20 30))))
  ;; Over end.
  (should (equal (my-visualize '(10 30 20 40))
                 '((0 10 20)
                   (1 20 40))))
  ;; Over beginning.
  (should (equal (my-visualize '(20 40 10 30))
                 '((0 30 40)
                   (1 10 30))))

  ;; At beginning.
  (should (equal (my-visualize '(10 40 10 30))
                 '((0 30 40)
                   (1 10 30))))

  ;; ----------
  ;; Split
  (should (equal (my-visualize '(10 40 20 30))
                 '((0 10 20)
                   (0 30 40)
                   (1 20 30))))

)


;; ----------------------------------------
;; Regexp group parser.
;;

(ert-deftest font-lock-studio-test-find-groups-in-regexp ()
  ;; ----------
  ;; Basics.

  ;; Empty regexp.
  (should (equal (font-lock-studio-find-groups-in-regexp "")
                 '(0 0)))

  ;; Plain text.
  (should (equal (font-lock-studio-find-groups-in-regexp "abc")
                 '(0 3)))
  ;; ----------
  ;; Groups

  ;; Normal group.
  (should (equal (font-lock-studio-find-groups-in-regexp "\\(abc\\)")
                 '(0 7 0 7)))
  ;; Nested normal groups.
  (should (equal (font-lock-studio-find-groups-in-regexp
                  "abc\\(def\\(ghi\\)jkl\\)mno")
                 '(0 23 3 20 8 15)))
  ;; Shy group.
  (should (equal (font-lock-studio-find-groups-in-regexp "\\(?:abc\\)")
                 '(0 9)))

  ;; Explictly numbered groups.
  (should (equal (font-lock-studio-find-groups-in-regexp "\\(?2:abc\\)")
                 '(0 10 nil nil 0 10)))

  ;; Ensure that further groups have higher numbers.
  (should (equal (font-lock-studio-find-groups-in-regexp
                  "\\(?2:abc\\)\\(def\\)")
                 '(0 17 nil nil 0 10 10 17)))

  ;; Explicit groups overwrite previous groups.
  (should (equal (font-lock-studio-find-groups-in-regexp
                  "\\(abc\\)\\(def\\)\\(?1:ghi\\)")
                 '(0 24 14 24 7 14)))

  ;; Suffices
  (should (equal (font-lock-studio-find-groups-in-regexp "\\(abc\\)+")
                 '(0 8 0 8)))

  (should (equal (font-lock-studio-find-groups-in-regexp "\\(abc\\)?")
                 '(0 8 0 8)))

  (should (equal (font-lock-studio-find-groups-in-regexp "\\(abc\\)*")
                 '(0 8 0 8)))

  (should (equal (font-lock-studio-find-groups-in-regexp "\\(abc\\)\\{20\\}")
                 '(0 13 0 13)))

  (should (equal (font-lock-studio-find-groups-in-regexp "\\(abc\\)\\{,20\\}")
                 '(0 14 0 14)))

  (should (equal (font-lock-studio-find-groups-in-regexp "\\(abc\\)\\{20,\\}")
                 '(0 14 0 14)))

  (should (equal (font-lock-studio-find-groups-in-regexp "\\(abc\\)\\{20,9\\}")
                 '(0 15 0 15)))

  ;; ----------
  ;; Character classes.

  (should (equal (font-lock-studio-find-groups-in-regexp "abc\\([a-z]\\)def")
                 '(0 15 3 12)))

  (should (equal (font-lock-studio-find-groups-in-regexp
                  "abc\\([[:alpha:]]\\)def")
                 '(0 21 3 18)))

  ;; ----------
  ;; Possibly confusing!
  (should (equal (font-lock-studio-find-groups-in-regexp
                  "abc\\([\\)]\\)def")
                 '(0 14 3 11)))

  ;; ----------
  ;; Broken regexp:s

  (should (equal (condition-case nil
                     (font-lock-studio-find-groups-in-regexp "[")
                   (invalid-regexp :an-error-occured))
                 :an-error-occured))

  (should (equal (condition-case nil
                     (font-lock-studio-find-groups-in-regexp "\\(")
                   (invalid-regexp :an-error-occured))
                 :an-error-occured))

  (should (equal (condition-case nil
                     (font-lock-studio-find-groups-in-regexp "\\)")
                   (invalid-regexp :an-error-occured))
                 :an-error-occured))
  )


;; -------------------------------------------------------------------
;; System for comparing font-lock and font-lock-studio.
;;

(defun font-lock-studio-test-font-lock-vs-studio (&optional buffer)
  (interactive)
  (unless buffer
    (setq buffer (current-buffer)))
  (let ((result-font-lock
         (with-current-buffer buffer
           (font-lock-fontify-region (point-min) (point-max))
           (faceup-markup-buffer)))
        (result-studio
         (font-lock-studio-fontify
          (faceup-markup-buffer))))
    (let ((res (faceup-test-equal result-font-lock result-studio)))
      (if (interactive-p)
          (message (if res
                       "Results are equal"
                     "Results are NOT equal")))
      res)))

(faceup-defexplainer font-lock-studio-test-font-lock-vs-studio)


(defun font-lock-studio-test-file (mode file)
  "Ert test function for testing font-lock and font-lock-studio.

FILE is highlighted using major mode MODE using font-lock and
font-lock-studio and the result is compared."
  ;; TODO: Use `with-temp-buffer'.
  (let ((temp-buffer (generate-new-buffer "*Font-Lock-Studio-Test*")))
    (with-current-buffer temp-buffer
      (insert-file-contents-literally file)
      (funcall mode)
      (prog1
          (font-lock-studio-test-font-lock-vs-studio)
        (kill-buffer temp-buffer)))))

(faceup-defexplainer font-lock-studio-test-file)


;; --------------------
;; Logger
;;
;; Using the log feature of the package `font-lock-profiler', it's
;; possible to do back-to-back with the real font-lock and
;; font-lock-studio. This ensures that they keywords are applied in
;; the correct order, with the point at the correct location and with
;; correct match data.
(defun font-lock-studio-test-font-lock-vs-studio-with-log (verbose
                                                           &optional
                                                           match-count
                                                           buffer)
  "Compare the result of font-lock and font-lock-studio when applied to BUFFER.

Return t when the two systems come to the same result. When
`faceup-test-explain' is non-nil, return an Ert-style explanation
of what differs.

Both the end result and the order, point, and match-data of each
part of the font-lock keyword are compared. See the
`font-lock-profiler' package for details.

If BUFFER is nil, the current buffer is used.

If MATCH-COUNT is an integer, make matchers stop matching after
this many matches.

If VERBOSE is non-nil (or when called interactively), a message
is echoed and, if the comparison failed, the log is displayed."
  (interactive '(t))
  (unless buffer
    (setq buffer (current-buffer)))
  (font-lock-set-defaults)
  (let ((font-lock-keywords
         (font-lock-profiler-instrument-keyword-list font-lock-keywords)))
    (let (log-real
          log-studio)
      (let ((faceup-real
             (let ((font-lock-profiler-log '())
                   (font-lock-profiler-remaining-matches match-count))
               (set-match-data (list (point-min) (point-min)))
               (font-lock-fontify-region (point-min) (point-max))
               (setq log-real (font-lock-profiler-result-log :no-time))
               (faceup-markup-buffer)))
            (faceup-studio
             (let ((font-lock-profiler-log '())
                   (font-lock-profiler-remaining-matches match-count))
               (set-match-data (list (point-min) (point-min)))
               (prog1
                   (font-lock-studio-fontify
                    (faceup-markup-buffer))
                 (setq log-studio (font-lock-profiler-result-log :no-time))))))
        (let ((res (faceup-test-equal faceup-real faceup-studio)))
          (if faceup-test-explain
              (if (eq res t)
                  (setq res (ert--explain-equal log-real log-studio)))
            (setq res (and res (equal log-real log-studio))))
          (when verbose
            (assert (not faceup-test-explain))
            (message (if res
                         "Results are equal"
                       "Results are NOT equal"))
            (unless res
              (with-output-to-temp-buffer "*FLST Log*"
                (princ "Common log:\n")
                (while (and log-real
                            log-studio
                            (equal (car log-real)
                                   (car log-studio)))
                  (princ (font-lock-profiler-format-log-entry (pop log-real)))
                  (terpri)
                  (pop log-studio))
                (princ "\n\nFont Lock:\n")
                (dolist (entry log-real)
                  (princ (font-lock-profiler-format-log-entry entry))
                  (terpri))
                (princ "\n\nFont Lock Studio:\n")
                (dolist (entry log-studio)
                  (princ (font-lock-profiler-format-log-entry entry))
                  (terpri))
                (pop-to-buffer standard-output))))
          res)))))


;; -------------------------------------------------------------------
;; Real major modes
;;

(ert-deftest font-lock-studio-test-facit ()
  ;; Silently ignore this test if the Emacs C source files aren't
  ;; available.
  (when font-lock-studio-test-source-directory
    (should (font-lock-studio-test-file
             'c-mode
             (concat font-lock-studio-test-source-directory
                     "/nsterm.h")))
    ;; If I can make it there, I can make it anywhere!
    (should (font-lock-studio-test-file
             'objc-mode
             (concat font-lock-studio-test-source-directory
                     "/nsterm.m")))))



;; -------------------------------------------------------------------
;; Fictitous major modes
;;

;; --------------------

(defvar font-lock-studio-test-keywords1
  '(("abc\\(def\\)\\(xxx\\)?\\(ghi\\)" (0 font-lock-keyword-face))
    ("xxx\\(yyy\\)\\(zzz\\)"
     (1 font-lock-keyword-face)
     ("t\\(a\\)\\(i\\)\\(l\\)"
      (1 font-lock-warning-face)
      (2 font-lock-constant-face)
      (3 font-lock-function-name-face))
     ("s\\(v\\)\\(a\\)\\(n\\)\\(s\\)"
      (1 font-lock-warning-face)
      (2 font-lock-constant-face)
      (3 font-lock-function-name-face)
      (3 font-lock-type-face))
     (2 font-lock-type-face))
    ((lambda (limit) nil)
     (0 font-lock-type-face))))

(define-derived-mode font-lock-studio-test-keywords1-mode fundamental-mode
  "Font-Lock-Studio-Test"
  "Major mode for testing wacky font-lock rules."
  (setq font-lock-defaults '(font-lock-studio-test-keywords1)))


(defun font-lock-studio-test-keywords1-example ()
  (with-temp-buffer
    (font-lock-studio-test-keywords1-mode)
    (insert "abcdefghi")
    (font-lock-studio-test-font-lock-vs-studio-with-log (interactive-p))))

(faceup-defexplainer font-lock-studio-test-keywords1-example)


(ert-deftest font-lock-studio-test-keywords1 ()
  (should (font-lock-studio-test-keywords1-example)))


;; --------------------
;; Check that match data is handled properly, even when set in a form.
;;

(defvar font-lock-studio-test-bogus-match-data-seed nil)

(defun font-lock-studio-test-generate-bogus-match-data ()
  "Set match data to a new, unique (kind-of) value."
  (set-match-data
   (append (match-data)
           (list font-lock-studio-test-bogus-match-data-seed
                 (+ font-lock-studio-test-bogus-match-data-seed 1))))
  (setq font-lock-studio-test-bogus-match-data-seed
        (+ font-lock-studio-test-bogus-match-data-seed 2)))


(defun font-lock-studio-test-bogus-match-data-mode-pattern1 (limit)
  (re-search-forward "abc\\(def\\)\\(xxx\\)?\\(ghi\\)" limit t))

(defvar font-lock-studio-test-bogus-match-data-keywords
  '(
    ;; Reset the "bogus match data" seed.
    (lambda (limit)
      (setq font-lock-studio-test-bogus-match-data-seed 0)
      nil)
    "allan"                             ; Rule with no highlight.
    (font-lock-studio-test-bogus-match-data-mode-pattern1
     (0 (progn
          (font-lock-studio-test-generate-bogus-match-data)
          'font-lock-keyword-face)))
    ("xxx\\(yyy\\)\\(zzz\\)"
     (1 font-lock-keyword-face)
     ("t\\(a\\)\\(i\\)\\(l\\)"
      (progn
        (font-lock-studio-test-generate-bogus-match-data)
        nil)
      (font-lock-studio-test-generate-bogus-match-data)
      (1 font-lock-warning-face)
      (2 font-lock-constant-face)
      (3 (progn
           font-lock-function-name-face)))
     ("s\\(v\\)\\(a\\)\\(n\\)\\(s\\)"
      (progn
        (font-lock-studio-test-generate-bogus-match-data)
        nil)
      (progn
        (font-lock-studio-test-generate-bogus-match-data))
      (1 font-lock-warning-face)
      (2 font-lock-constant-face)
      (3 font-lock-function-name-face)
      (4 (progn
           (font-lock-studio-test-generate-bogus-match-data)
           'font-lock-keyword-face)))
;     (2 font-lock-type-face)
     )
    ((lambda (limit)
       (font-lock-studio-test-generate-bogus-match-data)
       nil)
     (0 font-lock-type-face))))

(define-derived-mode font-lock-studio-test-bogus-match-data-mode
  fundamental-mode
  "Font-Lock-Studio-Test"
  "Major mode for testing wacky font-lock rules."
  (setq font-lock-defaults '(font-lock-studio-test-bogus-match-data-keywords)))


(defun font-lock-studio-test-bogus-match-data-example ()
  (interactive)
  (with-temp-buffer
    (font-lock-studio-test-bogus-match-data-mode)
    (insert "allan\n")
    (insert "abcdefghi\n")
    (insert "abcdefxxxghi\n")
    (insert "xxxyyyzzztailtailtailsvanssvans\n")
    (insert "xxxyyyzzztailtailtail\n")
    (insert "xxxyyyzzztailtailtail\n")
    (insert "xxxyyyzzztailtailtail\n")
    (font-lock-studio-test-font-lock-vs-studio-with-log (interactive-p))))

(faceup-defexplainer font-lock-studio-test-bogus-match-data-example)


(ert-deftest font-lock-studio-test-bogus-match-data ()
  (should (font-lock-studio-test-bogus-match-data-example)))


;; --------------------
;; Point movement between of anchored rules.
;;
;; For some reason, the point isn't moved between calls to matchers in
;; an anchored rule (which could lead to a hanging). However, the
;; point is moved between the main matcher and the sub matcher.
;;

(defvar font-lock-studio-test-anchored-counter nil)

(defvar font-lock-studio-test-anchored-keywords
  '(;; --------------------
    ;; Plain rule, were MATCHER move point.
    ((lambda (limit)
       (re-search-forward "^X" limit t))
     ;; Anchored rule.
     ((lambda (limit)
        (re-search-forward "t" limit t))
      ;; Pre match rule
      (progn
;       (beginning-of-line)
        nil)
      ;; Post match rule
      (progn
;       (end-of-line)
        nil)
      ;; Sub highlights.
      (0 font-lock-keyword-face)))
    ;; --------------------
    ;; Check that point movement is correct after main matcher and
    ;; before the anchored forms are evaluated.
    ((lambda (limit)
       (setq font-lock-studio-test-anchored-counter 5)
       (prog1 (re-search-forward "^X" limit t)
         (goto-char (match-beginning 0))))
     ;; Anchored rule.
     ((lambda (limit)
        (let ((res (not (eq font-lock-studio-test-anchored-counter 0))))
          (when res
            (setq font-lock-studio-test-anchored-counter
                  (- font-lock-studio-test-anchored-counter 1))
            (set-match-data (list (line-beginning-position)
                                  (line-end-position))))
          res))
      ;; Pre match rule
      nil
      ;; Post match rule
      nil
      ;; Sub highlights.
      (0 font-lock-keyword-face)))
    ;; --------------------
    ;; Ditto, with movement in the pre and post match form
    ((lambda (limit)
       (setq font-lock-studio-test-anchored-counter 5)
       (prog1 (re-search-forward "^X" limit t)
         (goto-char (match-beginning 0))))
     ;; Anchored rule.
     ((lambda (limit)
        (let ((res (not (eq font-lock-studio-test-anchored-counter 0))))
          (when res
            (setq font-lock-studio-test-anchored-counter
                  (- font-lock-studio-test-anchored-counter 1))
            (set-match-data (list (line-beginning-position)
                                  (line-end-position))))
          res))
      ;; Pre match rule
      (progn
        (beginning-of-line)
        nil)
      ;; Post match rule
      (progn
        (end-of-line)
        nil)
      ;; Sub highlights.
      (0 font-lock-keyword-face)))))


(define-derived-mode font-lock-studio-test-anchored-mode fundamental-mode
  "Font-Lock-Studio-Test-Anchored"
  "Major mode for testing wacky font-lock rules."
  (setq font-lock-defaults '(font-lock-studio-test-anchored-keywords)))


(defun font-lock-studio-test-anchored-example ()
  (interactive)
  (with-temp-buffer
    (font-lock-studio-test-anchored-mode)
    (insert "\n")
    (insert "Xtest\n")
    (insert "\n")
    (insert "Xabcdefghijklmnopqrstuvwxyz\n")
    (font-lock-studio-test-font-lock-vs-studio-with-log (interactive-p))))

(faceup-defexplainer font-lock-studio-test-anchored-example)


(ert-deftest font-lock-studio-test-anchored ()
  (should (font-lock-studio-test-anchored-example)))


;; --------------------
;; Match data on "wrong" buffer.
;;
;; Font-lock studio should not visualize the match data when in the
;; wrong buffer. Typically, this occurs when code in a matcher
;; performs the highlighting manually and a stray match-data is active
;; at the end.

(defvar font-lock-studio-test-wrong-buffer-keyword
  '(((lambda (limit)
       (if (eobp)
           nil
         (forward-line)
         (with-current-buffer "*scratch*"
           (save-excursion
             (goto-char (point-min))
             (looking-at ".*"))))))))


(define-derived-mode font-lock-studio-test-wrong-buffer-mode fundamental-mode
  "Font-Lock-Studio-Test-Wrong-Buffer-Mode"
  "Major mode for font-lock rules setting match-data in wrong buffer."
  (setq font-lock-defaults '(font-lock-studio-test-wrong-buffer-keyword)))


(defun font-lock-studio-test-wrong-buffer-example ()
  (interactive)
  (with-temp-buffer
    (font-lock-studio-test-wrong-buffer-mode)
    (insert "Alpha\n")
    (insert "Beta\n")
    (insert "Gamma\n")
    (insert "Delta\n")
    (font-lock-studio-test-font-lock-vs-studio-with-log (interactive-p))))

(faceup-defexplainer font-lock-studio-test-wrong-buffer-example)

(ert-deftest font-lock-studio-test-wrong-buffer-mode ()
  (should (font-lock-studio-test-wrong-buffer-example)))


;; --------------------
;; Explainer
;;


(defvar font-lock-studio-test-explainer-keywords
  '(("allan"                             ; Regexp-based rule
     (0 'font-lock-type-face)            ; Face
     (0 font-lock-keyword-face)          ; Bound variable
     (0 an-unbound-variable))            ; Unbound variable
    (a-function
     (0 'foo))
    ((lambda (x) nil)
     (0 'bar))))

(define-derived-mode font-lock-studio-test-explainer-mode fundamental-mode
  "Font-Lock-Studio-Test"
  "Major mode for testing wacky font-lock rules."
  (setq font-lock-defaults '(font-lock-studio-test-explainer-keywords))
  )

(defun font-lock-studio-test-explain-current-state ()
  (let ((state (font-lock-studio-fontify-get-current-state)))
    (if state
        (font-lock-studio-explain-state state)
      nil)))

(defun font-lock-studio-test-explainer ()
  (interactive)
  (with-temp-buffer
    (font-lock-studio-test-explainer-mode)
    (font-lock-set-defaults)
    (insert "allan\n")
    (font-lock-studio-fontify-start)
    (should (equal (font-lock-studio-test-explain-current-state)
                   "Keyword with regexp matcher"))
    ;; Match "allan"
    (should (font-lock-studio-fontify-match-current-keyword))
    (should (equal (font-lock-studio-test-explain-current-state)
                   "Highlight: `font-lock-type-face' face."))
    (should (font-lock-studio-fontify-set-next-highlight))
    (should
     (equal
      (font-lock-studio-test-explain-current-state)
      "Highlight: Face `font-lock-keyword-face' \
\(via variable `font-lock-keyword-face')."))
    (should (font-lock-studio-fontify-set-next-highlight))
    (should
     (equal
      (font-lock-studio-test-explain-current-state)
      "Highlight: Face should come from variable `an-unbound-variable', \
which is unbound (missing quote?)."))
    (should (font-lock-studio-fontify-set-next-keyword))
    (should (equal (font-lock-studio-test-explain-current-state)
                   "Keyword with function name matcher"))
    (should (font-lock-studio-fontify-set-next-keyword))
    (should (equal (font-lock-studio-test-explain-current-state)
                   "Keyword with code-based matcher"))
    ))


(ert-deftest font-lock-studio-test-explainer ()
  (font-lock-studio-test-explainer))


;; ----------------------------------------
;; Broken regexp:s

(defvar font-lock-studio-test-broken-keywords
  '(("["
     (0 'font-lock-keyword-face))))

(define-derived-mode font-lock-studio-test-broken-mode fundamental-mode
  "Font-Lock-Studio-Test"
  "Major mode for testing broken font-lock rules."
  (setq font-lock-defaults '(font-lock-studio-test-broken-keywords))
  )

;; No ert test for this case. Font-Lock Studio issues an error when
;; stepping, which is the intended behaviour.


;; ----------------------------------------
;; (eval . xxx)

(defvar font-lock-studio-test-eval-keywords
  '((eval . (list "abc" (list 0 'font-lock-warning-face)))))

(define-derived-mode font-lock-studio-test-eval-mode fundamental-mode
  "Font-Lock-Studio-Test-Eval"
  "Major mode for testing the (eval . xxx) construct."
  (setq font-lock-defaults '(font-lock-studio-test-eval-keywords)))


;; ----------------------------------------
;; Foreground and background, can font-lock mix faces?
;;

(defface font-lock-studio-test-background-face '((t :background "blue"))
  "Feeling blue.")

(defvar font-lock-studio-test-background-keywords
  '(("abc" (0 'font-lock-studio-test-background-face))
    ("abc" (0 'font-lock-warning-face append))))

(define-derived-mode font-lock-studio-test-background-mode fundamental-mode
  "Font-Lock-Studio-Test-Background"
  "Major mode for testing if faces can be mixed."
  (setq font-lock-defaults '(font-lock-studio-test-background-keywords)))

(defun font-lock-studio-test-background-example ()
  (interactive)
  (with-temp-buffer
    (font-lock-studio-test-background-mode)
    (insert "abc\n")
    (font-lock-studio-test-font-lock-vs-studio-with-log (interactive-p))))

(faceup-defexplainer font-lock-studio-test-background-example)


(ert-deftest font-lock-studio-test-background ()
  (should (font-lock-studio-test-background-example)))


;; ----------------------------------------
;; Identical keywords -- check for breakpoints
;;

(defvar font-lock-studio-test-identical-keywords
  '(("abc" (0 'font-lock-warning-face append))
    ("abc" (0 'font-lock-warning-face append))))

(define-derived-mode font-lock-studio-test-identical-keywords-mode
  fundamental-mode
  "Font-Lock-Studio-Test-Identical"
  "Major mode for testing identical keywords."
  (setq font-lock-defaults '(font-lock-studio-test-identical-keywords)))


(defun font-lock-studio-test-identical-keywords-example ()
  (interactive)
  (with-temp-buffer
    (font-lock-studio-test-identical-keywords-mode)
    (insert "abc\n")
    (font-lock-studio-test-font-lock-vs-studio-with-log (interactive-p))))

(faceup-defexplainer font-lock-studio-test-identical-keywords-example)


(ert-deftest font-lock-studio-test-identical-keywords ()
  (should (font-lock-studio-test-identical-keywords-example)))


;; ----------------------------------------
;; No progress.
;;

(defvar font-lock-studio-test-no-progress-keywords
  '(("#*.*$"
     (0 'font-lock-warning-face append))))

(define-derived-mode font-lock-studio-test-no-progress-keywords-mode
  fundamental-mode
  "Font-Lock-Studio-Test-No-Progress"
  "Major mode for testing keywords that don't move point forward."
  (setq font-lock-defaults '(font-lock-studio-test-no-progress-keywords)))


(defun font-lock-studio-test-no-progress-example ()
  (interactive)
  (with-temp-buffer
    (font-lock-studio-test-no-progress-keywords-mode)
    (insert "# alpha\n")
    (insert "\n")
    (insert "# beta\n")
    (font-lock-studio-test-font-lock-vs-studio-with-log (interactive-p))))

(faceup-defexplainer font-lock-studio-test-no-progress-example)


(ert-deftest font-lock-studio-test-no-progress ()
  (should (font-lock-studio-test-no-progress-example)))


;; ----------------------------------------
;; No progress in anchored subrule.
;;

;; WARNING! This mode will hang Emacs if font-lock is activated.

(defvar font-lock-studio-test-no-anchored-progress-keywords
  '(("^"
     (""
      nil                                ; Pre-match-form
      nil                                ; Post-match-form
      (0 'font-lock-warning-face append)))))

(define-derived-mode font-lock-studio-test-no-anchored-progress-keywords-mode
  fundamental-mode
  "Font-Lock-Studio-Test-No-Anchored-Progress"
  "Major mode for testing keywords that don't move point forward."
  (setq font-lock-defaults
        '(font-lock-studio-test-no-anchored-progress-keywords)))


(defun font-lock-studio-test-no-anchored-progress-example ()
  (interactive)
  (with-temp-buffer
    (font-lock-studio-test-no-anchored-progress-keywords-mode)
    (insert "# alpha\n")
    (insert "\n")
    (insert "# beta\n")
    (font-lock-studio-test-font-lock-vs-studio-with-log (interactive-p)
                                                        50)))

(faceup-defexplainer font-lock-studio-test-no-anchored-progress-example)


(ert-deftest font-lock-studio-test-no-anchored-progress ()
  (should (font-lock-studio-test-no-anchored-progress-example)))


;; ----------------------------------------
;; Move point in face expression.
;;

;; Match "foo:" in "(foo:, foo:, foo:)".

(defvar font-lock-studio-test-move-point-in-face-expression-keywords
  '(("[,(]\\s-*\\([a-z]+\\):\\s-*[,)]"
     (1 (progn
	  (forward-char -1)
	  'font-lock-warning-face)
	append)
     (1 'underline append))))

(define-derived-mode font-lock-studio-test-move-point-in-face-expression-mode
  fundamental-mode
  "Font-Lock-Studio-Test-Move-Point-In-Face-Expression"
  "Major mode for testing point movement in face expression."
  (setq font-lock-defaults
        '(font-lock-studio-test-move-point-in-face-expression-keywords)))


(defun font-lock-studio-test-move-point-in-face-expression-example ()
  (interactive)
  (with-temp-buffer
    (font-lock-studio-test-move-point-in-face-expression-mode)
    (insert "def f(foo:, foo:, foo:)\n")
    (font-lock-studio-test-font-lock-vs-studio-with-log (interactive-p))))

(faceup-defexplainer
 font-lock-studio-test-move-point-in-face-expression-example)


(ert-deftest font-lock-studio-test-move-point-in-face-expression ()
  (should (font-lock-studio-test-move-point-in-face-expression-example)))


;; ----------------------------------------
;; Matcher in anchored
;;

;; ------------------------------------------------------------
;; The end
;;

(provide 'font-lock-studio-test)

;;; font-lock-studio-test.el ends here
