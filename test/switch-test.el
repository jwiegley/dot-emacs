;;; switch-test.el --- Tests for window-purpose-switch.el -*- lexical-binding: t -*-

;; Copyright (C) 2015, 2016 Bar Magal

;; Author: Bar Magal
;; Package: purpose

;; This file is not part of GNU Emacs.

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
;; This file contains tests for window-purpose-switch.el

;;; TODO:
;; - alist entry `reusable-frames'
;; - `purpose-display-reuse-window-buffer-other-frame'
;; - `purpose-display-reuse-window-purpose-other-frame'
;; - `purpose-display-maybe-pop-up-frame'
;; - `purpose-read-buffers-with-purpose'
;; - `purpose-switch-buffer-with-purpose' (other-window, other-frame)
;; - `purpose-switch-buffer-with-some-purpose'

;;; Code:

(ert-deftest purpose-test-switch-buffer ()
  "Test variations of `purpose-switch-buffer'.
- 1 windows, switch to same purpose
- 1 window, switch to different purpose
- 1 window, p-dedicated, switch to same purpose
- 1 window, p-dedicated, switch to different purpose
- 1 window, b-dedicated, switch to same purpose
- 1 window, b-dedicated, switch to different purpose
- 2 windows (purposes p0 and p1), from p1 window, switch to buried p0
  buffer"
  (save-window-excursion
    (unwind-protect
        (let ((purpose-message-on-p t))
          (purpose-with-temp-config
              nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1))
            (purpose-create-buffers-for-test :p0 2 :p1 1)
            (purpose-mode 1)
            ;; 1
            (message "1...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            ;; (purpose-switch-buffer "xxx-p0-1")
            (switch-to-buffer "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-1"))
            ;; 2
            (message "2...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (purpose-switch-buffer "xxx-p1-0")
            ;; (switch-to-buffer "xxx-p1-0")
            (purpose-check-displayed-buffers '("xxx-p1-0"))
            ;; 3
            (message "3...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (purpose-set-window-purpose-dedicated-p nil t)
            ;; (purpose-switch-buffer "xxx-p0-1")
            (switch-to-buffer "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-1"))
            (purpose-set-window-purpose-dedicated-p nil nil)
            ;; 4
            (message "4...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (purpose-set-window-purpose-dedicated-p nil t)
            ;; (purpose-switch-buffer "xxx-p1-0")
            (switch-to-buffer "xxx-p1-0")
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p1-0"))
            (purpose-set-window-purpose-dedicated-p nil nil)
            ;; 5
            (message "5...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-1")
            (set-window-dedicated-p nil t)
            ;; (purpose-switch-buffer "xxx-p0-1")
            (switch-to-buffer "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-1"))
            (set-window-dedicated-p nil nil)
            ;; 6
            (message "6...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (set-window-dedicated-p nil t)
            ;; (purpose-switch-buffer "xxx-p1-0")
            (switch-to-buffer "xxx-p1-0")
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p1-0"))
            (set-window-dedicated-p nil nil)
            ;; 7
            (message "7...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (select-window (split-window))
            (set-window-buffer nil "xxx-p1-0")
            ;; (purpose-switch-buffer "xxx-p0-1")
            (switch-to-buffer "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-1" "xxx-p1-0"))
            (purpose-mode -1)))
      (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p0-1" "xxx-p1-0"))))

(ert-deftest purpose-test-switch-buffer-other-window ()
  "Test variations of `purpose-switch-buffer-other-window'.
- 1 windows, switch to same purpose
- 2 windows (p0 and p1), from p0 window, switch to buried p0 buffer
- 2 windows (p0 and p1), p1 dedicated, from p0 window, switch to buried
  p0 buffer."
  (save-window-excursion
    (unwind-protect
        (let ((purpose-message-on-p t))
          (purpose-with-temp-config
              nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1))
            (purpose-create-buffers-for-test :p0 2 :p1 1)
            (purpose-mode 1)
            ;; 1
            (message "1...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            ;; (purpose-switch-buffer-other-window "xxx-p0-1")
            (switch-to-buffer-other-window "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p0-1"))
            ;; 2
            (message "2...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p1-0")
            (select-window (split-window))
            (set-window-buffer nil "xxx-p0-0")
            (purpose-switch-buffer-other-window "xxx-p0-1")
            ;; (switch-to-buffer-other-window "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p0-1"))
            ;; 3
            (message "3...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p1-0")
            (purpose-set-window-purpose-dedicated-p nil t)
            (select-window (split-window))
            (set-window-buffer nil "xxx-p0-0")
            ;; (purpose-switch-buffer-other-window "xxx-p0-1")
            (switch-to-buffer-other-window "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p0-1" "xxx-p1-0"))
            (purpose-mode -1)))
      (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p0-1" "xxx-p1-0"))))

(ert-deftest purpose-test-pop-buffer ()
  "Test variations of `purpose-pop-buffer'.
- 1 windows, switch to same purpose
- 2 windows (p0 and p1), from p0 window, switch to buried p0 buffer
- 2 windows (p0 and p1), p1 dedicated, from p0 window, switch to buried
  p0 buffer."
  (save-window-excursion
    (unwind-protect
        (let ((purpose-message-on-p t))
          (purpose-with-temp-config
              nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1))
            (purpose-create-buffers-for-test :p0 2 :p1 1)
            (purpose-mode 1)
            ;; 1
            (message "1...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            ;; (purpose-pop-buffer "xxx-p0-1")
            (pop-to-buffer "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-1"))
            ;; 2
            (message "2...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p1-0")
            (select-window (split-window))
            (set-window-buffer nil "xxx-p0-0")
            (purpose-pop-buffer "xxx-p0-1")
            ;; (pop-to-buffer "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-1" "xxx-p1-0"))
            ;; 3
            (message "3...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p1-0")
            (purpose-set-window-purpose-dedicated-p nil t)
            (select-window (split-window))
            (set-window-buffer nil "xxx-p0-0")
            ;; (purpose-pop-buffer "xxx-p0-1")
            (pop-to-buffer "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-1" "xxx-p1-0"))
            (purpose-mode -1)))
      (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p0-1" "xxx-p1-0"))))

(ert-deftest purpose-test-pop-buffer-same-window ()
  "Test variations of `purpose-pop-buffer-same-window'.
- 1 windows, switch to other purpose
- 2 windows (p0 and p1), from p0 window, switch to buried p0 buffer
- 2 windows (p0 and p1), from p1 window, switch to buried p0 buffer
- 2 windows (p0 and p1), p0 b-dedicated, from p0 window, switch to
  buried p0 buffer.
- 2 windows (p0 and p1), both b-dedicated, from p0 window, switch to
  buried p0 buffer."
  (save-window-excursion
    (unwind-protect
        (let ((purpose-message-on-p t))
          (purpose-with-temp-config
              nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1))
            (purpose-create-buffers-for-test :p0 2 :p1 1)
            (purpose-mode 1)
            ;; 1
            (message "1...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            ;; (purpose-pop-buffer-same-window "xxx-p1-0")
            (pop-to-buffer-same-window "xxx-p1-0")
            (purpose-check-displayed-buffers '("xxx-p1-0"))
            ;; 2
            (message "2...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p1-0")
            (select-window (split-window))
            (set-window-buffer nil "xxx-p0-0")
            (purpose-pop-buffer-same-window "xxx-p0-1")
            ;; (pop-to-buffer-same-window "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-1" "xxx-p1-0"))
            ;; 3
            (message "3...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (select-window (split-window))
            (set-window-buffer nil "xxx-p1-0")
            ;; (purpose-pop-buffer-same-window "xxx-p0-1")
            (pop-to-buffer-same-window "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p0-1"))
            ;; 4
            (message "4...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p1-0")
            (select-window (split-window))
            (set-window-buffer nil "xxx-p0-0")
            (set-window-dedicated-p nil t)
            ;; (purpose-pop-buffer-same-window "xxx-p0-1")
            (pop-to-buffer-same-window "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p0-1"))
            ;; 5
            (message "5...")
            (delete-other-windows)
            (set-window-buffer nil "xxx-p1-0")
            (set-window-dedicated-p nil t)
            (select-window (split-window))
            (set-window-buffer nil "xxx-p0-0")
            (set-window-dedicated-p nil t)
            ;; (purpose-pop-buffer-same-window "xxx-p0-1")
            (pop-to-buffer-same-window "xxx-p0-1")
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p0-1" "xxx-p1-0"))
            (purpose-mode -1)))
      (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p0-1" "xxx-p1-0"))))

;; can't raise frames in automatic tests (because "emacs -batch"), so
;; this test can't pass...
;; (ert-deftest purpose-test-switch-buffer-other-frame ()
;;   "Test `purpose-switch-buffer-other-frame'."
;;   (let ((frame-conf (current-frame-configuration)))
;;     (unwind-protect
;; 	(unwind-protect
;; 	    (purpose-with-temp-config
;; 	     nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1))
;; 	     (purpose-create-buffers-for-test :p0 2 :p1 1)
;; 	     (purpose-mode 1)
;; 	     (delete-other-frames)
;; 	     (delete-other-windows)
;; 	     (set-window-buffer nil "xxx-p0-0")
;; 	     ;; (purpose-switch-buffer-other-frame "xxx-p0-1")
;;           (switch-to-buffer-other-frame "xxx-p0-1")
;; 	     (should (equal (length (frame-list)) 2))
;; 	     (purpose-check-displayed-buffers "xxx-p0-1")
;; 	     (other-frame 1)
;; 	     (purpose-check-displayed-buffers "xxx-p0-0")
;; 	     (purpose-mode -1))
;; 	  (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p0-1" "xxx-p1-0"))
;;       (set-frame-configuration frame-conf))))

(ert-deftest purpose-test-window-buffer-reusable ()
  "Test `purpose-window-buffer-reusable-p'."
  (should (purpose-window-buffer-reusable-p (selected-window) (window-buffer (selected-window)))))

(ert-deftest purpose-test-display-no-buffer ()
  "Test `display-buffer-no-window' works with `purpose-mode'.
Window layout should be unchanged."
  ;; `display-buffer-no-window' isn't defined in Emacs 24.3 and older
  (when (fboundp 'display-buffer-no-window)
    (save-window-excursion
      (unwind-protect
          (let ((purpose-message-on-p t))
            (purpose-create-buffers-for-test :p0 2)
            (purpose-mode 1)
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (split-window)
            (message "testing buffer not displayed ...")
            (should-not (display-buffer "xxx-p0-1" '(display-buffer-no-window (allow-no-window . t))))
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p0-0"))
            (message "testing buffer not displayed (2) ...")
            (should-not (display-buffer "xxx-p0-1" '((display-buffer-no-window
                                                      purpose-display-maybe-other-window)
                                                     (allow-no-window . t))))
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p0-0")))
        (purpose-mode -1)
        (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p0-1")))))

(ert-deftest purpose-test-display-fallback-pop-window ()
  "Test value `pop-up-window' for `purpose-display-fallback'.
From single buffer-dedicated window, switch with `force-same-window: a
new window should be created."
  (save-window-excursion
    (unwind-protect
        (let ((purpose-message-on-p t))
          (purpose-with-temp-config
              nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1))
            (purpose-create-buffers-for-test :p0 1 :p1 1)
            (purpose-mode 1)
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (set-window-dedicated-p nil t)
            (let ((purpose-display-fallback 'pop-up-window))
              (switch-to-buffer "xxx-p1-0" nil t)
              (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p1-0")))))
      (purpose-mode -1)
      (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p1-0"))))

;; can't raise frames in automatic tests (because "emacs -batch"), so
;; this test can't pass...
;; (ert-deftest purpose-test-display-fallback-pop-frame ()
;;   "Test value `pop-up-frame' for `purpose-display-fallback'.
;; From single buffer-dedicated window, switch with `force-same-window: a
;; new frame should be created."
;;   (unwind-protect
;;       (let ((purpose-message-on-p t))
;; 	(purpose-with-temp-config
;; 	 nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1))
;; 	 (purpose-create-buffers-for-test :p0 1 :p1 1)
;; 	 (purpose-mode 1)
;; 	 (delete-other-frames)
;; 	 (delete-other-windows)
;; 	 (set-window-buffer nil "xxx-p0-0")
;; 	 (set-window-dedicated-p nil t)
;; 	 (let ((purpose-display-fallback 'pop-up-frame))
;; 	   (switch-to-buffer "xxx-p1-0" nil t)
;; 	   (should (equal (length (frame-list)) 2)))))
;;     (purpose-mode -1)
;;     (delete-other-frames)
;;     (delete-other-windows)
;;     (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p1-0")))

(ert-deftest purpose-test-display-fallback-error ()
  "Test value `error' for `purpose-display-fallback'.
From single buffer-dedicated window, switch with `force-same-window: an
error should be signaled."
  (save-window-excursion
    (unwind-protect
        (let ((purpose-message-on-p t))
          (purpose-with-temp-config
              nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1))
            (purpose-create-buffers-for-test :p0 1 :p1 1)
            (purpose-mode 1)
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (set-window-dedicated-p nil t)
            (let ((purpose-display-fallback 'error))
              (should-error (switch-to-buffer "xxx-p1-0" nil t)))))
      (purpose-mode -1)
      (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p1-0"))))

(ert-deftest purpose-test-display-fallback-nil ()
  "Test value `nil' for `purpose-display-fallback'.
From single buffer-dedicated window, switch with `force-same-window': an
error should be signaled.
With two purpose-dedicated windows, switch to a third purpose window:
new buffer should be displayed in one of the two existing windows."
  (save-window-excursion
    (unwind-protect
        (let ((purpose-message-on-p t))
          (purpose-with-temp-config
              nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1) ("^xxx-p2-" . p2))
            (purpose-create-buffers-for-test :p0 1 :p1 1 :p2 1)
            (purpose-mode 1)
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (set-window-dedicated-p nil t)
            (let ((purpose-display-fallback nil))
              (message "testing error ...")
              (should-error (switch-to-buffer "xxx-p1-0" nil t)))

            (set-window-dedicated-p nil nil)
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (purpose-set-window-purpose-dedicated-p nil t)
            (let ((other-window (split-window)))
              (set-window-buffer other-window "xxx-p1-0")
              (purpose-set-window-purpose-dedicated-p other-window t))
            (let ((purpose-display-fallback nil))
              (message "testing successful display ...")
              (switch-to-buffer "xxx-p2-0")
              (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p2-0")))))
      (purpose-mode -1)
      (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p1-0"))))

(ert-deftest purpose-test-normalize-sizes ()
  "Test sanity for `purpose--normalize-width' and `purpose--normalize-height'."
  (message "testing purpose--normalize-width ...")
  (should (equal (purpose--normalize-width 5) 5))
  (should (equal (purpose--normalize-width 0.5) (/ (frame-width) 2)))
  (should (equal (purpose--normalize-width nil) nil))
  (should-error (purpose--normalize-width -5))

  (message "testing purpose--normalize-height ...")
  (should (equal (purpose--normalize-height 5) 5))
  (should (equal (purpose--normalize-height 0.5) (/ (frame-height) 2)))
  (should (equal (purpose--normalize-height nil) nil))
  (should-error (purpose--normalize-height -5)))

(ert-deftest purpose-test-display-at ()
  "Test scenarios of `purpose-display--at'."
  (save-window-excursion
    (unwind-protect
        (purpose-with-temp-config
            nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1) ("^xxx-p2-" . p2))
          (purpose-create-buffers-for-test :p0 1 :p1 2)
          (purpose-mode 1)
          (delete-other-windows)
          (let ((first-window (selected-window)))
            (set-window-buffer first-window "xxx-p0-0")
            (message "testing popup ...")
            (purpose-display-at-bottom (get-buffer "xxx-p1-0") nil)
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p1-0"))

            (message "testing reuse buffer ...")
            (select-window first-window)
            (purpose-display-at-bottom (get-buffer "xxx-p1-0") nil)
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p1-0"))

            (message "testing reuse purpose ...")
            (select-window first-window)
            (purpose-display-at-bottom (get-buffer "xxx-p1-1") nil)
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p1-1"))))
      (purpose-mode -1)
      (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p1-0" "xxx-p1-1"))))

(ert-deftest purpose-test-special-action-sequences ()
  "Test `purpose-special-action-sequences' properly affects display behavior.
- (purpose . (display-functions)) causes <display-functions> to be
  called for buffers with <purpose>.
- (predicate . (display-functions)) causes <display-functions> to be
  called for buffers that match <predicate>."
  (save-window-excursion
    (unwind-protect
        (purpose-with-temp-config
            nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1) ("^xxx-p2-" . p2))
          (purpose-create-buffers-for-test :p0 1 :p1 1 :p2 1)
          (purpose-mode 1)
          (setq test-happend 0)
          (let ((purpose-special-action-sequences
                 '((p1
                    (lambda (buffer alist) (setq test-happened 1) (display-buffer-at-bottom buffer alist)))
                   ((lambda (purpose buffer alist) (eql (purpose-buffer-purpose buffer) 'p2))
                    (lambda (buffer alist) (setq test-happened 2) (display-buffer-at-bottom buffer alist))))))
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (switch-to-buffer "xxx-p1-0")
            (message "Windows: %S" (window-list))
            (should (equal test-happened 1))
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (switch-to-buffer "xxx-p2-0")
            (should (equal test-happened 2))))
      (purpose-mode -1)
      (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p1-0" "xxx-p2-0"))))

(ert-deftest purpose-cover-select-buffer-without-action-order ()
  "Test `purpose-select-buffer' does use `purpose-default-action-order'."
  (save-window-excursion
    (unwind-protect
        (let ((purpose-default-action-order 'prefer-other-window))
          (purpose-mode 1)
          (delete-other-windows)
          (purpose-select-buffer (get-buffer-create "xxx-test"))
          (should (equal (length (window-list)) 2)))
      (purpose-mode -1)
      (purpose-kill-buffers-safely "xxx-test"))))

(ert-deftest purpose-test-interactive-switch-buffer ()
  "Test `purpose-switch-buffer' when called interactively."
  (save-window-excursion
    (unwind-protect
        (let ((purpose-message-on-p t))
          (purpose-with-temp-config
              nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1))
            (purpose-create-buffers-for-test :p0 1 :p1 1)
            (purpose-mode 1)
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (purpose-set-window-purpose-dedicated-p nil t)
            (purpose-insert-user-input "xxx-p1-0")
            (call-interactively 'purpose-switch-buffer)
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p1-0"))))
      (purpose-mode -1)
      (delete-other-windows)
      (purpose-set-window-purpose-dedicated-p nil nil)
      (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p1-0"))))

(ert-deftest purpose-test-interactive-switch-buffer-with-some-purpose ()
  "Test `purpose-switch-buffer-with-some-purpose' when called interactively."
  (save-window-excursion
    (unwind-protect
        (let ((purpose-message-on-p t))
          (purpose-with-temp-config
              nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1))
            (purpose-create-buffers-for-test :p0 1 :p1 1)
            (purpose-mode 1)
            (delete-other-windows)
            (set-window-buffer nil "xxx-p0-0")
            (purpose-set-window-purpose-dedicated-p nil t)
            (purpose-insert-user-input "p1")
            (purpose-insert-user-input "xxx-p1-0")
            (call-interactively 'purpose-switch-buffer-with-some-purpose)
            (purpose-check-displayed-buffers '("xxx-p0-0" "xxx-p1-0"))))
      (purpose-mode -1)
      (delete-other-windows)
      (purpose-set-window-purpose-dedicated-p nil nil)
      (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p1-0"))))

(ert-deftest purpose-test-temp-actions-1 ()
  "Test macros for changing `purpose-special-action-sequences' temporarily.
This one tests `purpose-with-temp-display-actions' and
`purpose-with-temp-display-action'."
  (let ((original-actions purpose-special-action-sequences)
        (new-actions '((py purpose-display-reuse-window-buffer)
                       (c purpose-display-reuse-window-purpose))))
    (purpose-with-temp-display-actions new-actions
      (should (equal purpose-special-action-sequences new-actions)))
    (should (equal purpose-special-action-sequences original-actions))
    (purpose-with-temp-display-action (car new-actions)
      (should (equal purpose-special-action-sequences (list (car new-actions)))))
    (should (equal purpose-special-action-sequences original-actions))))

(ert-deftest purpose-test-temp-actions-1 ()
  "Test macros for changing `purpose-special-action-sequences' temporarily.
This one tests `purpose-with-additional-display-actions' and
`purpose-with-additional-display-action'."
  (let ((original-actions purpose-special-action-sequences)
        (new-actions '((py purpose-display-reuse-window-buffer)
                       (c purpose-display-reuse-window-purpose))))
    (purpose-with-additional-display-actions new-actions
      (should (equal purpose-special-action-sequences
                     (append new-actions original-actions))))
    (should (equal purpose-special-action-sequences original-actions))
    (purpose-with-additional-display-action (car new-actions)
      (should (equal purpose-special-action-sequences
                     (append (list (car new-actions)) original-actions))))
    (should (equal purpose-special-action-sequences original-actions))))

(provide 'switch-test)

;;; switch-test.el ends here
