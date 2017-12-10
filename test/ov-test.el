;;; ov.el --- Overlay library for Emacs Lisp -*- coding: utf-8; lexical-binding: t -*-

;; Copyright (C) 2014 by Shingo Fukuyama

;; Version: 1.0
;; Author: Shingo Fukuyama - http://fukuyama.co
;; URL: https://github.com/ShingoFukuyama/ov.el
;; Created: Mar 20 2014
;; Keywords: overlay
;; Package-Requires: ((emacs "24.3"))

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be
;; useful, but WITHOUT ANY WARRANTY; without even the implied
;; warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
;; PURPOSE.  See the GNU General Public License for more details.

;;; Code:

;; (ov-smear "\n\n" t)

(defun ov-test-insert-dummy-text ()
  (insert
   ";; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be
;; useful, but WITHOUT ANY WARRANTY; without even the implied
;; warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
;; PURPOSE.  See the GNU General Public License for more details.")
  (goto-char (point-min)))


(ert-deftest ov-test/ov ()
  (ov-test-insert-dummy-text)
  (should (ov? (ov 1 10 'face 'warning 'display "fff")))
  (should (ov? (ov 1 10 '(face 'success 'display "eee"))))
  (should (ov? (ov 1 10)))
  (should-error (ov 10)))

(ert-deftest ov-test/ov-make ()
  (ov-test-insert-dummy-text)
  (should (ov? (ov-make 2 5)))
  (should (ov? (ov-make (point-min) (point-max))))
  (should-error (ov-make))
  (should-error (ov-make 10)))

(ert-deftest ov-test/ov-line ()
  (ov-test-insert-dummy-text)
  (should (ov? (ov-line)))
  (should (ov? (ov-line (point-min))))
  (should (ov? (ov-line (point-max))))
  (should (ov? (ov-line (/ (point-max) 2))))
  (should-error (ov-line "a")))

(ert-deftest ov-test/ov-match ()
  (ov-test-insert-dummy-text)
  (should (listp (ov-match "is")))
  (should (ov? (car (ov-match "t"))))
  (should-error (ov-match 'a))
  (should-error (ov-match 1))
  (should-error (ov-match)))

(ert-deftest ov-test/ov-regexp ()
  (ov-test-insert-dummy-text)
  (should (listp (ov-regexp "^;;")))
  (should (ov? (car (ov-regexp "^;;"))))
  (should-error (ov-regexp 'a))
  (should-error (ov-regexp 1))
  (should-error (ov-regexp)))

;; https://github.com/ShingoFukuyama/ov.el/issues/8
(ert-deftest ov-test/ov-regexp-zero-width-match ()
  "Not infinite loop with zero width match such as `$'"
  (ov-test-insert-dummy-text)
  (should (listp (ov-regexp "$"))))

(ert-deftest ov-test/ov-set ()
  (ov-test-insert-dummy-text)
  (setq ov1 (ov-set (ov-line) 'face 'warning))
  (should (ov? ov1))
  (should (eq 1 (length (ov-all))))
  (ov-clear)
  (setq ov2 (ov-set (ov-line) '(face warning)))
  (should (ov? ov2))
  (should (eq 1 (length (ov-all))))
  (ov-clear)
  (setq ov3 (ov-set (ov-match "the") '(face warning)))
  (should (ov? (car ov3)))
  (should (eq 8 (length (ov-all))))
  (ov-clear)
  (setq ov4 (ov-set "^;;" '(face warning)))
  (should (ov? (car ov4)))
  (should (eq 8 (length (ov-all))))
  (ov-clear)
  (setq ov5 (ov-set "MERCHANTABILITY" '(face success)))
  (should (ov? (car ov5))))

(ert-deftest ov-test/ov-insert ()
  (ov-test-insert-dummy-text)
  (setq ov1 (ov-insert "test"))
  (should (eq 1 (length (ov-all))))
  (should (equal "test"
                 (buffer-substring
                  (ov-beg ov1) (ov-end ov1)))))

(ert-deftest ov-test/ov-clear ()
  (ov-test-insert-dummy-text)
  (ov-set "the" 'face 'underline)
  (ov-clear)
  (should-not (ov-all))
  (ov-set "the" 'face 'underline)
  (ov-clear 'face 'underline)
  (should-not (ov-all))
  (ov-set "the" 'face 'underline)
  (ov-clear 'face 'success)
  (should (< 1 (length (ov-all))))
  (ov-set "the" 'face 'underline)
  (goto-char (point-min))
  (re-search-forward "the" nil t 3)
  (ov-clear (point) (point-max) 'face 'underline)
  (should (< 2 (length (ov-all)))))

(ert-deftest ov-test/ov-reset ()
  (ov-test-insert-dummy-text)
  (setq ov1 10)
  (setq ov2 10)
  (setq ov1 (ov-make 1 10))
  (ov-reset ov1)
  (should-not ov1)
  (setq ov2 (ov-match "the"))
  (ov-set ov2 'display "THE")
  (ov-reset ov2)
  (should-not ov2))

(ert-deftest ov-test/ov-spec ()
  (ov-test-insert-dummy-text)
  (setq ov1 (ov-line))
  (setq ov2 (ov-regexp "^;.+$"))
  (should (listp (ov-spec ov1)))
  (should (listp (ov-spec ov2)))
  (should (eq 4 (length (car (ov-spec ov1)))))
  (should (eq 4 (length (car (ov-spec ov2))))))

(ert-deftest ov-test/ov-at ()
  (ov-test-insert-dummy-text)
  (ov-set "the" 'face '(:overline t :foreground "#ff0000"))
  (re-search-forward "the" nil t 3)
  (should-not (ov? (ov-at))) ;; at the end of an overlay
  (backward-char 1)
  (should     (ov? (ov-at)))
  (re-search-backward "the" nil t)
  (should     (ov? (ov-at)))
  (backward-char 1)
  (should-not (ov? (ov-at))))

(ert-deftest ov-test/ov-in ()
  (ov-test-insert-dummy-text)
  (ov-set "the" 'face 'warning)
  (ov-set "it" 'face 'success)
  (ov-set "is" 'face 'underline 'aaa t)
  (should (eq 23 (length (ov-in))))
  (should (eq 7 (length (ov-in 'aaa))))
  (should (eq 8 (length (ov-in 'face 'warning))))
  (should (eq 3 (length (ov-in 'face 'success 1 253)))))

(ert-deftest ov-test/ov-timeout ()
  (ov-test-insert-dummy-text)
  (ov-timeout 0.3
    '(ov-set "the" 'face 'warning)
    '(ov-clear 'face 'warning))
  (should (< 1 (length (ov-all))))
  (sleep-for 0.5)
  (should-not (ov-all))
  ;; (defun ov-1 () (ov-set "the" 'face 'warning))
  ;; (defun ov-2 () (ov-clear 'face 'warning))
  ;; (ov-timeout 0.3 ov-1 ov-2)
  ;; (should (< 1 (length (ov-all))))
  ;; (sleep-for 0.5)
  ;; (should-not (ov-all))
  )

(ert-deftest ov-test/ov-next ()
  (ov-test-insert-dummy-text)
  (ov-set "the" 'face 'success 'aaa t)
  (ov-set ".$" 'face 'warning 'bbb t)
  (should (eq (save-excursion (re-search-forward "the" nil t))
              (save-excursion (forward-line 1) (ov-end (ov-next)))))
  (should (eq (point-at-eol)
              (ov-end (ov-next nil 'bbb))))
  (should (eq (point-at-eol)
              (ov-end (ov-next nil 'bbb t))))
  (should (eq (point-at-eol)
              (ov-end (ov-next 'bbb))))
  (should (eq (point-at-eol)
              (ov-end (ov-next 'bbb t)))))

(ert-deftest ov-test/ov-prev ()
  (ov-test-insert-dummy-text)
  (ov-set "the" 'face 'success 'aaa t)
  (ov-set "^;" 'face 'warning 'bbb t)
  (goto-char (point-max))
  (should (eq (save-excursion (re-search-backward "the" nil t))
              (ov-beg (ov-prev))))
  (should (eq (point-at-bol)
              (ov-beg (ov-prev nil 'bbb))))
  (should (eq (point-at-bol)
              (ov-beg (ov-prev nil 'bbb t))))
  (should (eq (point-at-bol)
              (ov-beg (ov-prev 'bbb))))
  (should (eq (point-at-bol)
              (ov-beg (ov-prev 'bbb t)))))

(ert-deftest ov-test/ov-goto-next ()
  (ov-test-insert-dummy-text)
  (ov-set "the" 'face 'warning 'aaa t)
  (ov-set "is"  'face 'success 'bbb t)
  (should (eq 19 (save-excursion
                   (goto-char (point-min))
                   (ov-goto-next)
                   (ov-goto-next))))
  (should (eq 101 (save-excursion
                    (goto-char (point-min))
                    (ov-goto-next 'aaa)
                    (ov-goto-next 'aaa))))
  (should (eq 261 (save-excursion
                    (goto-char (point-min))
                    (ov-goto-next 100 'bbb t)
                    (ov-goto-next 'bbb t)))))

(ert-deftest ov-test/ov-goto-prev ()
  (ov-test-insert-dummy-text)
  (ov-set "the" 'face 'warning 'aaa t)
  (ov-set "is"  'face 'success 'bbb t)
  (should (eq 363 (save-excursion
                    (goto-char (point-max))
                    (ov-goto-prev)
                    (ov-goto-prev))))
  (should (eq 270 (save-excursion
                    (goto-char (point-max))
                    (ov-goto-prev 'bbb)
                    (ov-goto-prev 'bbb))))
  (should (eq 17 (save-excursion
                   (goto-char (point-max))
                   (ov-goto-prev 100 'bbb t)
                   (ov-goto-prev 'bbb t)))))

(ert-deftest ov-test/ov-keymap1 ()
  (ov-test-insert-dummy-text)
  (setq ov1 (ov-keymap (ov-regexp "the") "C-n" 'ov-clear))
  (should (ov? (car ov1)))
  (should (eq 8 (length (ov-all))))
  (ov-goto-next)
  (execute-kbd-macro (read-kbd-macro "C-n"))
  (should (eq 0 (length (ov-all)))))

(ert-deftest ov-test/ov-keymap2 ()
  (ov-test-insert-dummy-text)
  (forward-line 2)
  (setq ov1 (ov-line))
  (ov-set ov1 'face 'warning)
  (setq ov2 (ov-keymap ov1 "C-p" 'ov-clear))
  (should (ov? ov2))
  (should (ov? ov1))
  (should (eq (point-at-bol) (ov-beg ov1)))
  (should (eq (point-at-eol) (1- (ov-end ov1))))
  (execute-kbd-macro (read-kbd-macro "C-p"))
  (should (eq 0 (length (ov-all)))))

(ert-deftest ov-test/ov-keymap3 ()
  (ov-test-insert-dummy-text)
  (setq ov1 (ov-keymap 'ov-keymap-test
                       "C-n" '(ov-clear 'keymap)
                       "C-p" '(ov-clear 'keymap)))
  (should (eq (point-min) (ov-beg ov1)))
  (should (eq (point-max) (ov-end ov1)))
  (should (ov? (ov-at)))
  (execute-kbd-macro (read-kbd-macro "C-p"))
  (should-not (ov? (ov-at))))

(ert-deftest ov-test/ov-read-only1 ()
  (ov-test-insert-dummy-text)
  (setq ov1 (ov-match "the"))
  (setq ov2 (ov-read-only ov1))
  (should (ov? (car ov2)))
  (re-search-forward "the" nil t 3)
  (should-error (delete-backward-char 1))
  (delete-region (point-min) (point-max))
  (should (eq (point-min) (point-max))))

(ert-deftest ov-test/ov-read-only2 ()
  (ov-test-insert-dummy-text)
  (setq ov1 (ov-match "the"))
  (setq ov2 (ov-read-only ov1 t t))
  (should (ov? (car ov2)))
  (re-search-forward "the" nil t 2)
  (should-error (insert "a"))
  (re-search-backward "the" nil t 1)
  (should-error (insert "a")))

(ert-deftest ov-test/ov-placeholder ()
  (insert "abcdefghijklmnopqrstuvwxyz")
  (setq ov1 (ov-placeholder (ov-match "ghijklmn")))
  (should (ov? (car ov1)))
  (re-search-backward "g" nil t)
  (insert " ")
  (should (equal (buffer-substring (point-at-bol) (point-at-eol))
                 "abcdef opqrstuvwxyz"))
  (ov-placeholder (ov-match "vwxy"))
  (re-search-forward "v" nil t)
  (delete-backward-char 1)
  (should (equal (buffer-substring (point-at-bol) (point-at-eol))
                 "abcdef opqrstuz")))

(ert-deftest ov-test/ov-length ()
  (ov-test-insert-dummy-text)
  (should (= (ov-length (car (ov-match "the"))) 3))
  (ov-clear)
  (should (= (ov-length (car (ov-match "General"))) 7)))

(ert-deftest ov-test/ov--parse-hex-color ()
  (should (equal (ov--parse-hex-color "#332cfa") '(51 44 250)))
  (should (equal (ov--parse-hex-color "#332") '(51 51 34)))
  (should (equal (ov--parse-hex-color "#FEB") '(255 238 187)))
  (should-not (ov--parse-hex-color "#afs932"))
  (should-not (ov--parse-hex-color "#Bfs")))

(ert-deftest ov-test/ov--random-color ()
  (should (string-match "\\#[0-9a-fA-F]\\{6\\}" (ov--random-color)))
  (should (string-match "\\#[0-9a-fA-F]\\{6\\}" (ov--random-color "#33f")))
  (should (string-match "\\#[0-9a-fA-F]\\{6\\}" (ov--random-color "#fff000" 50))))

(ert-deftest ov-test/ov-smear ()
  (ov-test-insert-dummy-text)
  (should (ov? (car (ov-smear "this" t "red" 70))))
  (should (eq 1 (length (ov-in))))
  (should (ov? (car (ov-smear "the"))))
  (should (eq 7 (length (ov-in)))))

;; (ov-smear "\n\n" t)


(provide 'ov-test)
;;; ov-test.el ends here
