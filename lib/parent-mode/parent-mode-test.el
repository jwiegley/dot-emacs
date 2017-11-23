;;; parent-mode-test.el --- parent-mode test suite

;; Author: Fanael Linithien <fanael4@gmail.com>
;; URL: https://github.com/Fanael/parent-mode

;; This file is NOT part of GNU Emacs.

;; Copyright (c) 2014, Fanael Linithien
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

;; `parent-mode' test suite

;;; Code:

(when noninteractive
  (push (file-name-directory load-file-name) load-path))

(require 'parent-mode)
(require 'ert)

(define-derived-mode parent-mode-test-1-mode fundamental-mode "")
(define-derived-mode parent-mode-test-2-mode parent-mode-test-1-mode "")
(defalias 'parent-mode-test-3-parent-mode 'text-mode)
(define-derived-mode parent-mode-test-3-mode parent-mode-test-3-parent-mode "")
(define-derived-mode parent-mode-test-4-mode parent-mode-test-3-mode "")

(ert-deftest parent-mode-simple-mode ()
  (should (equal (parent-mode-list 'parent-mode-test-1-mode)
                 '(parent-mode-test-1-mode))))

(ert-deftest parent-mode-derived-mode ()
  (should (equal (parent-mode-list 'parent-mode-test-2-mode)
                 '(parent-mode-test-1-mode
                   parent-mode-test-2-mode))))

(ert-deftest parent-mode-defalias ()
  (should (equal (parent-mode-list 'parent-mode-test-3-mode)
                 '(text-mode
                   parent-mode-test-3-parent-mode
                   parent-mode-test-3-mode))))

(ert-deftest parent-mode-derived-p-derived ()
  (should (parent-mode-is-derived-p 'parent-mode-test-4-mode 'text-mode)))

(ert-deftest parent-mode-derived-p-not-derived ()
  (should-not (parent-mode-is-derived-p 'parent-mode-test-4-mode 'emacs-lisp-mode)))

(ert-deftest parent-mode-gracefully-handles-nonexistent-modes ()
  (should-error (parent-mode-list 'nonexistent-mode) :type 'void-function))

(provide 'parent-mode-test)
;;; parent-mode-test.el ends here
