;;; highlight-numbers.el --- Highlight numbers in source code -*- lexical-binding: t -*-

;; Author: Fanael Linithien <fanael4@gmail.com>
;; URL: https://github.com/Fanael/highlight-numbers
;; Version: 0.2.3
;; Package-Requires: ((emacs "24") (parent-mode "2.0"))

;; This file is NOT part of GNU Emacs.

;; Copyright (c) 2013-2016, Fanael Linithien
;; All rights reserved.
;;
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:
;;
;;   * Redistributions of source code must retain the above copyright
;;     notice, this list of conditions and the following disclaimer.
;;   * Redistributions in binary form must reproduce the above copyright
;;     notice, this list of conditions and the following disclaimer in the
;;     documentation and/or other materials provided with the distribution.
;;
;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
;; IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
;; TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
;; PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
;; OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
;; EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
;; PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
;; PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
;; LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;;; Commentary:

;; This minor mode provides syntax highlighting of numeric literals
;; in source code, like what many editors provide by default.
;;
;; To enable: call `highlight-numbers-mode'.
;;
;; It s customizable: it's easy to add or redefine what exactly consitutes a
;; "number" in given major mode. See `highlight-numbers-modelist'.

;;; Code:

(require 'parent-mode)

(defgroup highlight-numbers nil
  "Highlight numbers in source code."
  :prefix "highlight-numbers-"
  :group 'faces)

(defface highlight-numbers-number
  '((t :inherit font-lock-constant-face))
  "Face used to highlight numeric literals."
  :group 'highlight-numbers)

(defconst highlight-numbers-generic-regexp
  (rx (and
       symbol-start
       digit
       (*? any)
       symbol-end))
  "Generic regexp for number highlighting.

It is used when no mode-specific one is available.")

(defvar highlight-numbers-modelist
  (copy-hash-table
   (eval-when-compile
     (let ((table (make-hash-table :test 'eq)))
       (puthash 'c-mode
                (rx (and
                     symbol-start
                     (or (and (+ digit)
                              (? (and "." (* digit)))
                              (? (and (any "eE")
                                      (? (any "-+"))
                                      (+ digit))))
                         (and "0"
                              (any "xX")
                              (+ hex-digit)))
                     (? (or "f" "F"
                            "u" "U"
                            "l" "L"
                            "ll" "lL" "Ll" "LL"
                            "ul" "uL" "Ul" "UL"
                            "lu" "lU" "Lu" "LU"
                            "ull" "ulL" "uLl" "uLL" "Ull" "UlL" "ULl" "ULL"
                            "llu" "llU" "lLu" "lLU" "Llu" "LlU" "LLu" "LLU"))
                     symbol-end))
                table)
       (puthash 'c++-mode
                (rx (and
                     symbol-start
                     (or (and (+ digit)
                              (? (and "." (* digit)))
                              (? (and (any "eE")
                                      (? (any "-+"))
                                      (+ digit))))
                         (and "0"
                              (any "xX")
                              (+ hex-digit)))
                     (? (and (any "_" "A-Z" "a-z")
                             (* (any "_" "A-Z" "a-z" "0-9"))))
                     symbol-end))
                table)
       (puthash 'lisp-mode
                (rx (and
                     (or (and
                          symbol-start
                          (or
                           (and
                            (? (any "-+"))
                            (+ digit)
                            (? (or (and (any "eE")
                                        (? (any "-+"))
                                        (+ digit))
                                   (and "."
                                        (? (and (+ digit)
                                                (? (and
                                                    (any "eE")
                                                    (? (any "-+"))
                                                    (+ digit))))))
                                   (and "/"
                                        (+ digit)))))
                           (and
                            "."
                            (+ digit)
                            (? (and
                                (any "eE")
                                (? (any "-+"))
                                (+ digit))))))
                         (and "#"
                              symbol-start
                              (or (and (any "bB")
                                       (? (any "-+"))
                                       (+ (any "01")))
                                  (and (any "oO")
                                       (? (any "-+"))
                                       (+ (any "0-7")))
                                  (and (any "xX")
                                       (? (any "-+"))
                                       (+ hex-digit)))))
                     symbol-end))
                table)
       (puthash 'emacs-lisp-mode
                (rx (and
                     (or (and
                          symbol-start
                          (or
                           (and
                            (? (any "-+"))
                            (+ digit)
                            (? (or (and (any "eE")
                                        (? (any "-+"))
                                        (+ digit))
                                   (and "."
                                        (? (and (+ digit)
                                                (? (and
                                                    (any "eE")
                                                    (? (any "-+"))
                                                    (+ digit)))))))))
                           (and
                            "."
                            (+ digit)
                            (? (and
                                (any "eE")
                                (? (any "-+"))
                                (+ digit))))))
                         (and "#"
                              symbol-start
                              (or (and (any "bB")
                                       (? (any "-+"))
                                       (+ (any "01")))
                                  (and (any "oO")
                                       (? (any "-+"))
                                       (+ (any "0-7")))
                                  (and (any "xX")
                                       (? (any "-+"))
                                       (+ hex-digit)))))
                     symbol-end))
                table)
       (puthash 'clojure-mode
                (rx (and symbol-start
                         (? "-")
                         digit
                         (*? any)
                         symbol-end))
                table)
       (puthash 'julia-mode
                (rx (and
                     symbol-start
                     (or (and (+ digit)
                              (? (and "." (* digit)))
                              (? (and (any "eE")
                                      (? (any "-+"))
                                      (+ digit))))
                         (and "0"
                              (any "xX")
                              (+ hex-digit)))))
                table)
       (puthash 'ess-julia-mode
                (rx (and
                     symbol-start
                     (or (and (+ digit)
                              (? (and "." (* digit)))
                              (? (and (any "eE")
                                      (? (any "-+"))
                                      (+ digit))))
                         (and "0"
                              (any "xX")
                              (+ hex-digit)))))
                table)
       table)))
  "Hash table storing the mode-specific number highlighting regexps.

The keys are major mode symbols, the values are regexps or symbol
`do-not-use', which prevents `highlight-numbers-mode' from doing
anything when the buffer is in the specified major mode.

Parent modes are taken into account, e.g. if there's no
`lisp-interaction-mode' in the modelist, but `emacs-lisp-mode'
is there, the highlighting used for the latter will be used for
the former too.")

(defun highlight-numbers--get-from-modelist (modes)
  "Get the regexp for the first matching mode from MODES."
  (catch 'highlight-numbers--get-from-modelist-return
    (dolist (mode modes)
      (let ((elt (gethash mode highlight-numbers-modelist)))
        (when elt
          (throw 'highlight-numbers--get-from-modelist-return elt))))
    nil))

(defun highlight-numbers--get-regexp-for-mode (mode)
  "Get the most appropriate regexp for MODE."
  (let* ((modeparents (nreverse (parent-mode-list mode)))
         (elt (highlight-numbers--get-from-modelist modeparents))
         (regexp (cond
                  ((null elt) highlight-numbers-generic-regexp)
                  ((eq elt 'do-not-use) nil)
                  (t elt))))
    (if regexp
        `((,regexp . 'highlight-numbers-number))
      nil)))

(defvar highlight-numbers--keywords nil)

(defun highlight-numbers--turn-off ()
  "Tear down `highlight-numbers-mode'."
  (when highlight-numbers--keywords
    (font-lock-remove-keywords nil highlight-numbers--keywords)
    (kill-local-variable 'highlight-numbers--keywords)))

(defun highlight-numbers--turn-on ()
  "Set up `highlight-numbers-mode'."
  (let ((regexp (highlight-numbers--get-regexp-for-mode major-mode)))
    (when regexp
      (font-lock-add-keywords nil regexp)
      (set (make-local-variable 'highlight-numbers--keywords) regexp))))

;;;###autoload
(define-minor-mode highlight-numbers-mode
  "Minor mode for highlighting numeric literals in source code.

Toggle Highlight Numbers mode on or off.

With a prefix argument ARG, enable Highlight Numbers mode if ARG is
positive, and disable it otherwise. If called from Lisp, enable
the mode if ARG is omitted or nil, and toggle it if ARG is `toggle'."
  :init-value nil
  :lighter ""
  :keymap nil
  (highlight-numbers--turn-off)
  (when highlight-numbers-mode
    (highlight-numbers--turn-on))
  (when font-lock-mode
    (if (fboundp 'font-lock-flush)
        (font-lock-flush)
      (with-no-warnings (font-lock-fontify-buffer)))))

(provide 'highlight-numbers)
;;; highlight-numbers.el ends here
