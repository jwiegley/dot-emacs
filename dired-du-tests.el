;;; dired-du-tests.el --- Tests for dired-du.el  -*- lexical-binding: t; -*-

;; Copyright (C) 2017 Free Software Foundation, Inc.

;; Author: Tino Calancha <tino.calancha@gmail.com>,
;; Keywords:

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;

;;; code:

(require 'ert)
(require 'dired-du)

(ert-deftest dired-du-test1 ()
  (let* ((dir (make-temp-file "dired-du" 'dir))
         (dir2 (expand-file-name "foo" dir))
         (dired-du-used-space-program nil)
         (buffers '())
         mode-on)
    (unwind-protect
        (progn
          (make-directory dir2)
          (push (dired dir2) buffers)
          (setq mode-on dired-du-mode)
          (dotimes (i 9)
            (write-region "1234" nil (format "baz%d" i)))
          (push (dired dir) buffers)
          (dired-goto-file dir2)
          (should (= 36 (dired-du-get-recursive-dir-size))))
      (if mode-on
          (dired-du-mode 1)
        (dired-du-mode 0))
      (mapc #'kill-buffer buffers)
      (delete-directory dir 'recursive))))

(ert-deftest dired-du-test2 ()
  (let* ((dir (make-temp-file "dired-du" 'dir))
         (dir2 (expand-file-name "foo" dir))
         (buffers '()) mode-on)
    (unwind-protect
        (progn
          (make-directory dir2)
          (add-to-list 'buffers (dired dir2))
          (setq mode-on dired-du-mode)
          (dotimes (i 9)
            (write-region "1234" nil (format "baz%d" i)))
          (add-to-list 'buffers (dired dir))
          (dired-goto-file dir2)
          (let ((size-orig (floor (dired-du--read-size-from-buffer)))
                (size-du (dired-du-get-recursive-dir-size)))
            (dolist (dired-du-size-format (list nil 'comma t))
              (unwind-protect
                  (progn
                    (should (/= size-orig size-du))
                    (dired-du-mode 1)
                    (unless (eq dired-du-size-format t)
                      (should (= (floor (dired-du--read-size-from-buffer))
                                 size-du)))
                    ;; Disable user write permissions on this dir: The size shown
                    ;; must be equal to `size-orig'.
                    (set-file-modes dir2 #o000)
                    (dired-du-mode 0)
                    (dired-du--reset)
                    (revert-buffer)
                    (dired-du-mode 1)
                    (unless dired-du-used-space-program
                      (should (= size-orig
                                 (floor (dired-du--read-size-from-buffer))))))
                ;; Clean up
                (set-file-modes dir2 #o755)
                (dired-du-mode 0)
                (dired-du--reset)))))
      (if mode-on
          (dired-du-mode 1)
        (dired-du-mode 0))
      (mapc #'kill-buffer buffers)
      (delete-directory dir 'recursive))))

(ert-deftest dired-du-test3 ()
  (let* ((dir (make-temp-file "dired-du" 'dir))
         (dir2 (expand-file-name "foo" dir))
         (dir3 (expand-file-name "bar" dir))
         (file (expand-file-name "qux" dir))
         (dired-du-used-space-program nil)
         (buffers '()) mode-on info)
    (unwind-protect
        (let ((name2 (file-name-nondirectory dir2))
              (name3 (file-name-nondirectory dir3)))
          (make-directory dir2)
          (make-directory dir3)
          (write-region "" nil file)
          (add-to-list 'buffers (dired dir))
          (setq mode-on dired-du-mode)
          (dired-du-mode 1)
          ;; (should (dired-du--get-position name2))
          (should (dired-du--file-in-dir-info-p name2))
          (should (dired-du--get-value name2 'size))
          ;; (should (dired-du--get-position name3))
          (should (dired-du--file-in-dir-info-p name3))
          (should (dired-du--get-value name3 'size))
          (setq info (assoc name3
                            (cdr (nth 0 dired-du-dir-info))))
          (dired-du--delete-entry name3)
          (should-not (dired-du--file-in-dir-info-p name3))
          ;; Reinsert it.
          (dired-du--global-update-dir-info
           (progn
             (dired-goto-file dir3)
             (list (dired-du-get-file-info)))
           0)
          (should (dired-du--file-in-dir-info-p name3))
          (delete-directory dir3 t)
          (should (dired-du--file-in-dir-info-p name3))
          (dired-mark 1)
          (dired-do-kill-lines nil)
          (dired-du--drop-unexistent-files)
          (should-not (dired-du--file-in-dir-info-p name3))
          ;; `dired-du-dir-info' just stored directories.
          (should-not (dired-du--get-position (file-name-nondirectory file))))
      (if mode-on
          (dired-du-mode 1)
        (dired-du-mode 0))
      (mapc #'kill-buffer buffers)
      (delete-directory dir 'recursive))))

(ert-deftest dired-du-test4 ()
  (let* ((dir (make-temp-file "dired-du" 'dir))
         (dir2 (expand-file-name "foo" dir))
         (dir3 (expand-file-name "bar" dir))
         (file (expand-file-name "qux" dir))
         (buffers '()))
    (unwind-protect
        (let ((name2 (file-name-nondirectory dir2))
              (name3 (file-name-nondirectory dir3))
              (marks '()))
          (make-directory dir2)
          (make-directory dir3)
          (write-region "" nil file)
          (add-to-list 'buffers (dired dir))
          (dired-mark-directories nil)
          (dired-change-marks ?* ?1)
          (dired-toggle-marks)
          (setq marks
                (sort (dired-du-get-all-marks) #'<))
          (should (equal (sort (list ?* ?1) #'<) marks)))
      (mapc #'kill-buffer buffers)
      (delete-directory dir 'recursive))))

(ert-deftest dired-du-test5 ()
  (let* ((dir (make-temp-file "dired-du" 'dir))
         (dir2 (expand-file-name "foo" dir))
         (dir3 (expand-file-name "bar" dir))
         (file1 (expand-file-name "qux" dir))
         (file2 (expand-file-name "qux" dir2))
         (file3 (expand-file-name "qux" dir3))
         (buffers '()) mode-on)
    (unwind-protect
        (let ((name2 (file-name-nondirectory dir2))
              (name3 (file-name-nondirectory dir3))
              (marks '()))
          (make-directory dir2)
          (make-directory dir3)
          (dolist (file (list file1 file2 file3))
            (write-region "" nil file))
          (add-to-list 'buffers (dired dir))
          (setq mode-on dired-du-mode)
          (dired-du-mode 1)
          (dired-insert-subdir dir2)
          (dired-insert-subdir dir3)
          (should (= 3 (length dired-du-dir-info)))
          (dired-goto-file file2)
          (dired-kill-subdir)
          (dired-du--drop-unexistent-files)
          (should (= 2 (length dired-du-dir-info))))
      (if mode-on
          (dired-du-mode 1)
        (dired-du-mode 0))
      (mapc #'kill-buffer buffers)
      (delete-directory dir 'recursive))))

(ert-deftest dired-du-count-sizes-test ()
  (let* ((dir (make-temp-file "dired-du" 'dir))
         (dir2 (expand-file-name "foo" dir))
         (dir3 (expand-file-name "bar" dir))
         (file1 (expand-file-name "file1" dir))
         (file2 (expand-file-name "file2" dir))
         (file3 (expand-file-name "file3" dir))
         (buffers '()) mode-on)
    (unwind-protect
        (let ((name2 (file-name-nondirectory dir2))
              (name3 (file-name-nondirectory dir3))
              (marks '()))
          (make-directory dir2)
          (make-directory dir3)
          (dolist (file (list file1 file2 file3))
            (write-region "" nil file))
          (add-to-list 'buffers (dired dir))
          (setq mode-on dired-du-mode)
          (dired-du-mode 1)
          (should (string-match "No marked files with mark"
                                (dired-du-count-sizes ?*)))
          ;; Mark dirs.
          (dired-mark-directories nil)
          (should (dired-du-count-sizes ?*))
          (dired-change-marks ?* ?1)
          (should (dired-du-count-sizes ?1))
          (dired-mark-files-regexp "\\`file[1-3]\\'")
          (should (string-match "Marked with [^ ]+ 3 files"
                                (dired-du-count-sizes ?*)))
          (should (windowp (dired-du-count-sizes ?* 'all-marks))))
      (if mode-on
          (dired-du-mode 1)
        (dired-du-mode 0))
      (mapc #'kill-buffer buffers)
      (delete-directory dir 'recursive))))

(provide 'dired-du-tests)
;;; dired-du-tests.el ends here
