;;; font-lock-studio.el --- interactive debugger for font-lock keywords.

;; Copyright (C) 2013-2014 Anders Lindgren

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

(ert-deftest font-lock-studio-visualize-match-data ()
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

(ert-deftest font-lock-studio-find-groups-in-regexp ()
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
  (let ((temp-buffer (generate-new-buffer "*Font-Lock-Studio-Test*")))
    (with-current-buffer temp-buffer
      (insert-file-contents-literally file)
      (funcall mode)
      (prog1
          (font-lock-studio-test-font-lock-vs-studio)
        (kill-buffer temp-buffer)))))

(faceup-defexplainer font-lock-studio-test-file)


(ert-deftest font-lock-studio-test-back-to-back ()
  (with-temp-buffer
    (font-lock-studio-test-mode)
    (insert "abcdefghi")
;;    (font-lock-mode 1)
;;    (should (equal font-lock-mode t))
    ;;    (should (font-lock-studio-test-font-lock-vs-studio))
    )
  )


;; --------------------

(require 'faceup)

(ert-deftest font-lock-studio-test-facit ()
  (should font-lock-studio-test-source-directory)
  (should (font-lock-studio-test-file
           'c-mode
           (concat font-lock-studio-test-source-directory
                   "/nsterm.h")))
  ;; If I can make it there, I can make it anywhere!
  (should (font-lock-studio-test-file
           'objc-mode
           (concat font-lock-studio-test-source-directory
                   "/nsterm.m")))
  )



;; --------------------
;; Fictitious major mode
;;

(defvar font-lock-studio-test-keywords
  '(("abc\\(def\\)\\(xxx\\)?\\(ghi\\)" (0 font-lock-keyword-face))
    ("xxx\\(yyy\\)\\(zzz\\)"
     (1 font-lock-keyword-face)
     ("t\\(a\\)\\(i\\)\\(l\\)"
      (setq fldb-pre (match-data))
      (setq fldb-post (match-data))
      (1 font-lock-warning-face)
      (2 font-lock-constant-face)
      (3 font-lock-function-name-face))
     ("s\\(v\\)\\(a\\)\\(n\\)\\(s\\)"
      (setq fldb-pre2 (match-data))
      (setq fldb-post2 (match-data))
      (1 font-lock-warning-face)
      (2 font-lock-constant-face)
      (3 font-lock-function-name-face)
      (3 font-lock-type-face))
     (2 font-lock-type-face))
    ((lambda (limit) (setq foo (point)) nil)
     (0 font-lock-type-face))))

(define-derived-mode font-lock-studio-test-mode fundamental-mode
  "Font-Lock-Studio-Test"
  "Major mode for testing wacky font-lock rules."
  (setq font-lock-defaults '(font-lock-studio-test-keywords)))


;; --------------------
;; Logger
;;
;; This is used to log information, used in back-to-back tests with
;; the real font-lock engine, to ensure that things are called in the
;; right order at the correct point and with the same match data.
;; (Requires a special set of font-lock keywords.

(defvar font-lock-studio-test-log-list nil)

(defun font-lock-studio-test-log-position (marker)
  (if (markerp marker)
      (marker-position marker)
    marker))


(defun font-lock-studio-test-log (what)
  (push (list what
              (point)
              (mapcar 'font-lock-studio-test-log-position (match-data)))
        font-lock-studio-test-log-list))

(defun font-lock-studio-test-log-print (log)
  (dolist (entry (reverse log))
    (if (eq (length entry) 3)
        (princ (format "%-22s %5d %s\n"
                       (nth 0 entry) (nth 1 entry) (nth 2 entry)))
      ;; Some other kind of log...
      (princ entry))))

(defvar font-lock-studio-test-log-bogus-match-data-seed nil)

(defun font-lock-studio-test-log-generate-bogus-match-data ()
  (set-match-data
   (append (match-data)
           (list font-lock-studio-test-log-bogus-match-data-seed
                 (+ font-lock-studio-test-log-bogus-match-data-seed 1))))
  (setq font-lock-studio-test-log-bogus-match-data-seed
        (+ font-lock-studio-test-log-bogus-match-data-seed 2)))


(defun font-lock-studio-test-log-mode-pattern1 (limit)
  (prog1
      (re-search-forward "abc\\(def\\)\\(xxx\\)?\\(ghi\\)" limit t)
    (font-lock-studio-test-log 'pattern1-after)))

(defvar font-lock-studio-test-log-keywords
  '("allan"                             ; Rule with no highlight.
    (font-lock-studio-test-log-mode-pattern1
     (0 (progn
          (font-lock-studio-test-log 'rule-0-face-form)
          (font-lock-studio-test-log-generate-bogus-match-data)
          'font-lock-keyword-face)))
    ("xxx\\(yyy\\)\\(zzz\\)"
     (1 font-lock-keyword-face)
     ("t\\(a\\)\\(i\\)\\(l\\)"
      (progn
        (font-lock-studio-test-log 'rule-1-pre-form)
        (font-lock-studio-test-log-generate-bogus-match-data)
        nil)
      (progn
        (font-lock-studio-test-log 'rule-1-post-form)
        (font-lock-studio-test-log-generate-bogus-match-data))
      (1 (progn
           (font-lock-studio-test-log 'rule-1-face-name-form)
           font-lock-warning-face))
      (2 font-lock-constant-face)
      (3 (progn
           font-lock-function-name-face)))
     ("s\\(v\\)\\(a\\)\\(n\\)\\(s\\)"
      (progn
        (font-lock-studio-test-log 'rule-2-pre-form)
        (font-lock-studio-test-log-generate-bogus-match-data)
        nil)
      (progn
        (font-lock-studio-test-log 'rule-2-post-form)
        (font-lock-studio-test-log-generate-bogus-match-data))
      (1 font-lock-warning-face)
      (2 font-lock-constant-face)
      (3 font-lock-function-name-face)
      (4 (progn
           (font-lock-studio-test-log 'rule-2-3-face-form)
           (font-lock-studio-test-log-generate-bogus-match-data)
           'font-lock-keyword-face)))
;     (2 font-lock-type-face)
     )
    ((lambda (limit)
       (font-lock-studio-test-log 'rule-3-matcher)
       (font-lock-studio-test-log-generate-bogus-match-data)
       nil)
     (0 font-lock-type-face))))

(define-derived-mode font-lock-studio-test-log-mode fundamental-mode
  "Font-Lock-Studio-Test"
  "Major mode for testing wacky font-lock rules."
  (setq font-lock-defaults '(font-lock-studio-test-log-keywords))
  )



;; TODO: Join with plain function?
(defun font-lock-studio-test-font-lock-vs-studio-with-log (&optional buffer)
  (interactive)
  (unless buffer
    (setq buffer (current-buffer)))
  (let ((log1 nil)
        (log2 nil))
    (let ((result-font-lock
           (with-current-buffer buffer
             (set-match-data '(0 0))
             (setq font-lock-studio-test-log-bogus-match-data-seed 0)
             (setq font-lock-studio-test-log-list nil)
             (font-lock-fontify-region (point-min) (point-max))
             (setq log1 font-lock-studio-test-log-list)
             (faceup-markup-buffer)))
          (result-studio
           (progn
             (set-match-data '(0 0))
             (setq font-lock-studio-test-log-bogus-match-data-seed 0)
             (setq font-lock-studio-test-log-list nil)
             (prog1
               (font-lock-studio-fontify
                (faceup-markup-buffer))
               (setq log2 font-lock-studio-test-log-list)))))
      (let ((res (faceup-test-equal result-font-lock result-studio)))
        (if faceup-test-explain
            (if (eq res t)
                (setq res (ert--explain-equal log1 log2)))
          (setq res (and (equal log1 log2))))
        (when (interactive-p)
          (message (if res
                       "Results are equal"
                     "Results are NOT equal"))
          (unless res
            (with-output-to-temp-buffer "*FLST Log*"
              (princ "Font Lock:\n")
              (font-lock-studio-test-log-print log1)
              (princ "\n\nFont Lock Studio:\n")
              (font-lock-studio-test-log-print log2)
              (pop-to-buffer standard-output))))
        res))))

(faceup-defexplainer font-lock-studio-test-font-lock-vs-studio-with-log)


(defun font-lock-studio-test-log-mode-example ()
  (with-temp-buffer
    (font-lock-studio-test-log-mode)
    (insert "allan\n")
    (insert "abcdefghi\n")
    (insert "abcdefxxxghi\n")
    (insert "xxxyyyzzztailtailtailsvanssvans\n")
    (insert "xxxyyyzzztailtailtail\n")
    (insert "xxxyyyzzztailtailtail\n")
    (insert "xxxyyyzzztailtailtail\n")
    (font-lock-studio-test-font-lock-vs-studio-with-log)))

(faceup-defexplainer font-lock-studio-test-log-mode-example)


(ert-deftest font-lock-studio-test-log-mode-example ()
  (should (font-lock-studio-test-log-mode-example)))


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


;; ----------------------------------------
;; Identical keywords -- check for breakpoints
;;

(defvar font-lock-studio-test-identical-keywords
  '(("abc" (0 'font-lock-warning-face append))
    ("abc" (0 'font-lock-warning-face append))))

(define-derived-mode font-lock-studio-test-identical-mode fundamental-mode
  "Font-Lock-Studio-Test-Identical"
  "Major mode for testing identical keywords."
  (setq font-lock-defaults '(font-lock-studio-test-identical-keywords)))


;; ----------------------------------------
;; No progress.
;;

(defun font-lock-studio-test-no-progress-matcher (limit)
  (let ((p (point))
        (res (re-search-forward "#*.*$" limit t)))
    (push (list (cons :point-befor p)
                (cons :point-after (point))
                (cons :limit limit)
                (cons :result res))
          font-lock-studio-test-log-list)
    res))

(defvar font-lock-studio-test-no-progress-keywords
  '((font-lock-studio-test-no-progress-matcher
     (0 'font-lock-warning-face append))))

(define-derived-mode font-lock-studio-test-no-progress-keywords-mode
  fundamental-mode
  "Font-Lock-Studio-Test-No-Progress"
  "Major mode for testing keywords that don't move point forward."
  (setq font-lock-defaults '(font-lock-studio-test-no-progress-keywords)))


(defun font-lock-studio-test-no-progress-example ()
  (with-temp-buffer
    (font-lock-studio-test-no-progress-keywords-mode)
    (insert "# alpha\n")
    (insert "\n")
    (insert "# beta\n")
    (font-lock-studio-test-font-lock-vs-studio-with-log)))

(faceup-defexplainer font-lock-studio-test-no-progress-example)


(ert-deftest font-lock-studio-test-no-progress-example ()
  (should (font-lock-studio-test-no-progress-example)))

;; ------------------------------------------------------------
;; The end
;;

(provide 'font-lock-studio-test)

;;; font-lock-studio-test.el ends here
