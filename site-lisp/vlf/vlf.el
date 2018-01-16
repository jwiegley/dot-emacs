;;; vlf.el --- View Large Files  -*- lexical-binding: t -*-

;; Copyright (C) 2006, 2012-2015 Free Software Foundation, Inc.

;; Version: 1.7
;; Keywords: large files, utilities
;; Maintainer: Andrey Kotlarski <m00naticus@gmail.com>
;; Authors: 2006 Mathias Dahl <mathias.dahl@gmail.com>
;;          2012 Sam Steingold <sds@gnu.org>
;;          2013-2015 Andrey Kotlarski <m00naticus@gmail.com>
;; URL: https://github.com/m00natic/vlfi

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
;; This package provides the M-x vlf command, which visits part of
;; large file without loading it entirely.  The buffer uses VLF mode,
;; which provides several commands for moving around, searching,
;; comparing and editing selected part of file.
;; To have it offered when opening large files:
;; (require 'vlf-setup)

;; This package was inspired by a snippet posted by Kevin Rodgers,
;; showing how to use `insert-file-contents' to extract part of a
;; file.

;;; Code:

(require 'vlf-base)

(defcustom vlf-before-batch-functions nil
  "Hook that runs before multiple batch operations.
One argument is supplied that specifies current action.  Possible
values are: `write', `ediff', `occur', `search', `goto-line'."
  :group 'vlf :type 'hook)

(defcustom vlf-after-batch-functions nil
  "Hook that runs after multiple batch operations.
One argument is supplied that specifies current action.  Possible
values are: `write', `ediff', `occur', `search', `goto-line'."
  :group 'vlf :type 'hook)

(defcustom vlf-batch-size-remote 1024
  "Defines size (in bytes) of a batch of file data when accessed remotely."
  :group 'vlf :type 'integer)

(defvar hexl-bits)

(autoload 'vlf-write "vlf-write" "Write current chunk to file." t)
(autoload 'vlf-re-search-forward "vlf-search"
  "Search forward for REGEXP prefix COUNT number of times." t)
(autoload 'vlf-re-search-backward "vlf-search"
  "Search backward for REGEXP prefix COUNT number of times." t)
(autoload 'vlf-goto-line "vlf-search" "Go to line." t)
(autoload 'vlf-query-replace "vlf-search"
  "Query replace regexp over whole file." t)
(autoload 'vlf-occur "vlf-occur"
  "Make whole file occur style index for REGEXP." t)
(autoload 'vlf-toggle-follow "vlf-follow"
  "Toggle continuous chunk recenter around current point." t)
(autoload 'vlf-stop-follow "vlf-follow" "Stop continuous recenter." t)
(autoload 'vlf-ediff-buffers "vlf-ediff"
  "Run batch by batch ediff over VLF buffers." t)

(defvar vlf-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "n" 'vlf-next-batch)
    (define-key map "p" 'vlf-prev-batch)
    (define-key map " " 'vlf-next-batch-from-point)
    (define-key map "+" 'vlf-change-batch-size)
    (define-key map "-"
      (lambda () "Decrease vlf batch size by factor of 2."
        (interactive)
        (vlf-change-batch-size t)))
    (define-key map "s" 'vlf-re-search-forward)
    (define-key map "r" 'vlf-re-search-backward)
    (define-key map "%" 'vlf-query-replace)
    (define-key map "o" 'vlf-occur)
    (define-key map "[" 'vlf-beginning-of-file)
    (define-key map "]" 'vlf-end-of-file)
    (define-key map "j" 'vlf-jump-to-chunk)
    (define-key map "l" 'vlf-goto-line)
    (define-key map "e" 'vlf-ediff-buffers)
    (define-key map "f" 'vlf-toggle-follow)
    (define-key map "g" 'vlf-revert)
    map)
  "Keymap for `vlf-mode'.")

(defvar vlf-prefix-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-c\C-v" vlf-mode-map)
    map)
  "Prefixed keymap for `vlf-mode'.")

(define-minor-mode vlf-mode
  "Mode to browse large files in."
  :group 'vlf :keymap vlf-prefix-map
  :lighter (:eval (format " VLF[%d/%d](%s)"
                          (ceiling vlf-end-pos vlf-batch-size)
                          (ceiling vlf-file-size vlf-batch-size)
                          (file-size-human-readable vlf-file-size)))
  (cond (vlf-mode
         (set (make-local-variable 'require-final-newline) nil)
         (add-hook 'write-file-functions 'vlf-write nil t)
         (set (make-local-variable 'revert-buffer-function)
              'vlf-revert)
         (make-local-variable 'vlf-batch-size)
         (setq vlf-file-size (vlf-get-file-size buffer-file-truename)
               vlf-start-pos 0
               vlf-end-pos 0)
         (let* ((pos (position-bytes (point)))
                (start (* (/ pos vlf-batch-size) vlf-batch-size)))
           (goto-char (byte-to-position (- pos start)))
           (vlf-move-to-batch start))
         (add-hook 'after-change-major-mode-hook 'vlf-keep-alive t t)
         (vlf-keep-alive))
        ((or (not large-file-warning-threshold)
             (< vlf-file-size large-file-warning-threshold)
             (y-or-n-p (format "Load whole file (%s)? "
                               (file-size-human-readable
                                vlf-file-size))))
         (kill-local-variable 'revert-buffer-function)
         (vlf-stop-follow)
         (kill-local-variable 'require-final-newline)
         (remove-hook 'write-file-functions 'vlf-write t)
         (remove-hook 'after-change-major-mode-hook
                      'vlf-keep-alive t)
         (if (derived-mode-p 'hexl-mode)
             (let ((line (/ (1+ vlf-start-pos) hexl-bits))
                   (pos (point)))
               (if (consp buffer-undo-list)
                   (setq buffer-undo-list nil))
               (vlf-with-undo-disabled
                (let ((inhibit-read-only t))
                  (insert-file-contents-literally buffer-file-name
                                                  t nil nil t)
                  (hexlify-buffer)))
               (set-buffer-modified-p nil)
               (goto-char (point-min))
               (forward-line line)
               (forward-char pos))
           (let ((pos (+ vlf-start-pos (position-bytes (point))))
                 (inhibit-read-only t))
             (vlf-with-undo-disabled
              (insert-file-contents buffer-file-name t nil nil t))
             (goto-char (byte-to-position pos)))))
        (t (setq vlf-mode t))))

(defun vlf-keep-alive ()
  "Keep `vlf-mode' on major mode change."
  (if (derived-mode-p 'hexl-mode)
      (set (make-local-variable 'revert-buffer-function) 'vlf-revert))
  (setq vlf-mode t))

;;;###autoload
(defun vlf (file &optional minimal)
  "View Large FILE in batches.  When MINIMAL load just a few bytes.
You can customize number of bytes displayed by customizing
`vlf-batch-size'.
Return newly created buffer."
  (interactive (list (read-file-name "File to open: ") nil))
  (let ((vlf-buffer (generate-new-buffer "*vlf*")))
    (set-buffer vlf-buffer)
    (set-visited-file-name file)
    (set-buffer-modified-p nil)
    (cond (minimal
           (set (make-local-variable 'vlf-batch-size) 1024))
          ((file-remote-p file)
           (set (make-local-variable 'vlf-batch-size) vlf-batch-size-remote)))
    (vlf-mode 1)
    (when minimal                 ;restore batch size to default value
      (kill-local-variable 'vlf-batch-size)
      (make-local-variable 'vlf-batch-size))
    (switch-to-buffer vlf-buffer)
    vlf-buffer))

(defun vlf-next-batch (append)
  "Display the next batch of file data.
When prefix argument is supplied and positive
 jump over APPEND number of batches.
When prefix argument is negative
 append next APPEND number of batches to the existing buffer."
  (interactive "p")
  (vlf-verify-size)
  (vlf-tune-load (if (derived-mode-p 'hexl-mode)
                     '(:hexl :raw)
                   '(:insert :encode)))
  (let* ((end (min (+ vlf-end-pos (* vlf-batch-size (abs append)))
                   vlf-file-size))
         (start (if (< append 0)
                    vlf-start-pos
                  (- end vlf-batch-size))))
    (vlf-move-to-chunk start end)))

(defun vlf-prev-batch (prepend)
  "Display the previous batch of file data.
When prefix argument is supplied and positive
 jump over PREPEND number of batches.
When prefix argument is negative
 append previous PREPEND number of batches to the existing buffer."
  (interactive "p")
  (if (zerop vlf-start-pos)
      (error "Already at BOF"))
  (vlf-tune-load (if (derived-mode-p 'hexl-mode)
                     '(:hexl :raw)
                   '(:insert :encode)))
  (let* ((start (max 0 (- vlf-start-pos (* vlf-batch-size (abs prepend)))))
         (end (if (< prepend 0)
                  vlf-end-pos
                (+ start vlf-batch-size))))
    (vlf-move-to-chunk start end)))

;; scroll auto batching
(defadvice scroll-up (around vlf-scroll-up
                             activate compile)
  "Slide to next batch if at end of buffer in `vlf-mode'."
  (if (and vlf-mode (pos-visible-in-window-p (point-max)))
      (progn (vlf-next-batch 1)
             (goto-char (point-min)))
    ad-do-it))

(defadvice scroll-down (around vlf-scroll-down
                               activate compile)
  "Slide to previous batch if at beginning of buffer in `vlf-mode'."
  (if (and vlf-mode (pos-visible-in-window-p (point-min)))
      (progn (vlf-prev-batch 1)
             (goto-char (point-max)))
    ad-do-it))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; hexl mode integration

(eval-after-load "hexl"
  '(progn
     (defadvice hexl-save-buffer (around vlf-hexl-save
                                         activate compile)
       "Prevent hexl save if `vlf-mode' is active."
       (if vlf-mode
           (vlf-write)
         ad-do-it))

     (defadvice hexl-scroll-up (around vlf-hexl-scroll-up
                                       activate compile)
       "Slide to next batch if at end of buffer in `vlf-mode'."
       (if (and vlf-mode (pos-visible-in-window-p (point-max))
                (or (not (numberp arg)) (< 0 arg)))
           (progn (vlf-next-batch 1)
                  (goto-char (point-min)))
         ad-do-it))

     (defadvice hexl-scroll-down (around vlf-hexl-scroll-down
                                         activate compile)
       "Slide to previous batch if at beginning of buffer in `vlf-mode'."
       (if (and vlf-mode (pos-visible-in-window-p (point-min)))
           (progn (vlf-prev-batch 1)
                  (goto-char (point-max)))
         ad-do-it))

     (defadvice hexl-mode-exit (around vlf-hexl-mode-exit
                                       activate compile)
       "Exit `hexl-mode' gracefully in case `vlf-mode' is active."
       (if (and vlf-mode (not (buffer-modified-p)))
           (vlf-with-undo-disabled
            (erase-buffer)
            ad-do-it
            (vlf-move-to-chunk-2 vlf-start-pos vlf-end-pos))
         ad-do-it))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; utilities

(defun vlf-change-batch-size (decrease)
  "Change the buffer-local value of `vlf-batch-size'.
Normally, the value is doubled;
with the prefix argument DECREASE it is halved."
  (interactive "P")
  (vlf-set-batch-size (if decrease (/ vlf-batch-size 2)
                        (* vlf-batch-size 2))))

(defun vlf-set-batch-size (size)
  "Set batch to SIZE bytes and update chunk."
  (interactive
   (list (read-number "Size in bytes: "
                      (vlf-tune-optimal-load
                       (if (derived-mode-p 'hexl-mode)
                           '(:hexl :raw)
                         '(:insert :encode))))))
  (setq vlf-batch-size size)
  (vlf-move-to-batch vlf-start-pos))

(defun vlf-beginning-of-file ()
  "Jump to beginning of file content."
  (interactive)
  (vlf-tune-load (if (derived-mode-p 'hexl-mode)
                     '(:hexl :raw)
                   '(:insert :encode)))
  (vlf-move-to-batch 0))

(defun vlf-end-of-file ()
  "Jump to end of file content."
  (interactive)
  (vlf-verify-size)
  (vlf-tune-load (if (derived-mode-p 'hexl-mode)
                     '(:hexl :raw)
                   '(:insert :encode)))
  (vlf-move-to-batch vlf-file-size))

(defun vlf-revert (&optional _auto noconfirm)
  "Revert current chunk.  Ignore _AUTO.
Ask for confirmation if NOCONFIRM is nil."
  (interactive)
  (when (or noconfirm
            (yes-or-no-p (format "Revert buffer from file %s? "
                                 buffer-file-name)))
    (set-buffer-modified-p nil)
    (vlf-move-to-chunk-2 vlf-start-pos vlf-end-pos)))

(defun vlf-jump-to-chunk (n)
  "Go to to chunk N."
  (interactive "nGoto to chunk: ")
  (vlf-tune-load (if (derived-mode-p 'hexl-mode)
                     '(:hexl :raw)
                   '(:insert :encode)))
  (vlf-move-to-batch (* (1- n) vlf-batch-size)))

(defun vlf-no-modifications ()
  "Ensure there are no buffer modifications."
  (if (buffer-modified-p)
      (error "Save or discard your changes first")
    t))

(defun vlf-move-to-batch (start)
  "Move to batch determined by START.
Adjust according to file start/end and show `vlf-batch-size' bytes."
  (vlf-verify-size)
  (let* ((start (max 0 start))
         (end (min (+ start vlf-batch-size) vlf-file-size)))
    (if (= vlf-file-size end)          ; re-adjust start
        (setq start (max 0 (- end vlf-batch-size))))
    (vlf-move-to-chunk start end)))

(defun vlf-next-batch-from-point ()
  "Display batch of file data starting from current point."
  (interactive)
  (let ((start (+ vlf-start-pos (position-bytes (point)) -1)))
    (vlf-move-to-chunk start (+ start vlf-batch-size)))
  (goto-char (point-min)))

(provide 'vlf)

;;; vlf.el ends here
