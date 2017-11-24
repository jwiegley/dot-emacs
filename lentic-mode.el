;;; lentic-mode.el --- minor mode for lentic buffers -*- lexical-binding: t -*-

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>
;; The contents of this file are subject to the GPL License, Version 3.0.

;; Copyright (C) 2014, 2015, 2016, Phillip Lord, Newcastle University

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

;; A minor mode for creating and manipulated lentic buffers.

;;; Code:

;; ** Preliminaries

;; #+begin_src emacs-lisp
(require 'lentic)
(require 'lentic-doc)
;; #+end_src

;; ** Utility

;; #+begin_src emacs-lisp
(defun lentic-mode-lentic-list (buffer)
  "Return a list of all lentics for BUFFER.
Lentics are listed in an undefined order."
  (lentic-mode--lentic-list-1 buffer nil))

(defun lentic-mode--lentic-list-1 (buffer seen-buffer)
  (let ((buffers))
    (lentic-each
     buffer
     (lambda (b)
       (setq buffers (cons b buffers))))
    buffers))

(defun lentic-mode-buffer-list (buffer &optional frame)
  "Returns a list of all lentics for BUFFER.
Lentics are listed in the same order as in fundamental
`buffer-list'. or the frame local if FRAME is specified."
  (let ((lentic-list
         (lentic-mode-lentic-list buffer)))
    (-filter
     (lambda (b)
       (-contains? lentic-list b))
     (buffer-list frame))))

(defun lentic-mode-find-next-lentic-buffer (buffer &optional frame)
  (car
   (--drop-while
    (eq buffer it)
    (lentic-mode-buffer-list
     buffer (or frame (selected-frame))))))

(defun lentic-mode-find-next-visible-lentic-buffer (buffer &optional frame)
  (car
   (--drop-while
    (or (eq buffer it)
        (not (get-buffer-window it frame)))
    (lentic-mode-buffer-list
     buffer (or frame (selected-frame))))))

(defun lentic-mode-find-next-non-visible-lentic-buffer (buffer &optional frame)
  (car
   (--drop-while
    (or (eq buffer it)
        (get-buffer-window it frame))
    (lentic-mode-buffer-list
     buffer (or frame (selected-frame))))))
;; #+end_src



;; ** Window and Buffer Functions

;; #+begin_src emacs-lisp
(defun lentic-mode-show-buffer-in-window (before-buffer new-buffer)
  (let* ((buffer-window (get-buffer-window before-buffer))
         (before-window-start
          (window-start buffer-window))
         (before-window-point
          (m-buffer-at-point before-buffer)))
    (set-window-buffer
     buffer-window
     new-buffer)
    (set-window-start
     buffer-window
     before-window-start)
    (goto-char before-window-point)
    (bury-buffer before-buffer)))

;;;###autoload
(defun lentic-mode-create-from-init (&optional force)
  (interactive "P")
  (lentic-garbage-collect-config)
  (if (and lentic-config (not force))
      (message "Already initialized. C-u to force.")
    (let ((before (length lentic-config))
          (all (lentic-init-all-create)))
      (message "Created %s buffers"
               (- (length all)
                  before)))))


;;;###autoload
(defun lentic-mode-next-lentic-buffer ()
  "Move the lentic buffer into the current window, creating if necessary."
  (interactive)
  (lentic-mode-show-buffer-in-window
   (current-buffer)
   (lentic-mode-find-next-lentic-buffer (current-buffer))))

;;;###autoload
(defun lentic-mode-split-window-below ()
  "Move lentic buffer to the window below, creating if needed."
  (interactive)
  (-when-let
      (next
       (lentic-mode-find-next-non-visible-lentic-buffer
        (current-buffer)))
    (set-window-buffer
     (split-window-below)
     next)
    next))

;;;###autoload
(defun lentic-mode-split-window-right ()
  "Move lentic buffer to the window right, creating if needed."
  (interactive)
  (-when-let
      (next
       (lentic-mode-find-next-non-visible-lentic-buffer
        (current-buffer)))
    (set-window-buffer
     (split-window-right)
     next)
    next))

;;;###autoload
(defun lentic-mode-show-all-lentic ()
  (interactive)
  (delete-other-windows)
  (while
      (lentic-mode-split-window-below))
  (balance-windows))

(defun lentic-mode-swap-buffer-windows (a b)
  "Swaps the window that two buffers are displayed in.
A and B are the buffers."
  (let ((window-a (get-buffer-window a))
        (window-b (get-buffer-window b)))
    (when window-a
      (set-window-buffer
       window-a b))
    (when window-b
      (set-window-buffer
       window-b a))))

;;;###autoload
(defun lentic-mode-move-lentic-window ()
  "Move the next lentic buffer into the current window.
If the lentic is currently being displayed in another window,
then the current-buffer will be moved into that window. See also
`lentic-mode-swap-buffer-windows' and `lentic-mode-next-buffer'."
  (interactive)
  (let ((before-window-start
         (window-start (get-buffer-window)))
        (before-window-point
         (point)))
    (lentic-mode-swap-buffer-windows
     (current-buffer)
     (or
      (lentic-mode-find-next-visible-lentic-buffer
       (current-buffer))
      (lentic-mode-find-next-lentic-buffer
       (current-buffer))))
    (set-window-start
     (selected-window)
     before-window-start)
    (goto-char before-window-point)))

;;;###autoload
(defun lentic-mode-swap-lentic-window ()
  "Swap the window of the buffer and lentic.
If both are current displayed, swap the windows they
are displayed in, which keeping current buffer.
See also `lentic-mode-move-lentic-window'."
  (interactive)
  (lentic-mode-swap-buffer-windows
   (current-buffer)
   (lentic-mode-find-next-visible-lentic-buffer
    (current-buffer)))
  (when (window-live-p
         (get-buffer-window
          (current-buffer)))
    (select-window
     (get-buffer-window
      (current-buffer)))))

(defun lentic-mode-create-new-view ()
  (let* ((conf (lentic-default-init))
         (_ (oset conf
                  :sync-point nil))
         (that (lentic-create conf)))
    (setq lentic-config
          (cons conf lentic-config))
    that))

;;;###autoload
(defun lentic-mode-create-new-view-in-selected-window ()
  (interactive)
  (set-window-buffer
   (selected-window)
   (lentic-mode-create-new-view)))

(defun lentic-mode-force-clone-1 ()
  (lentic-when-lentic
   (let ((inhibit-modification-hooks t))
     (lentic-after-change-function
      (point-min) (point-max)
      (- (point-max) (point-min))))))

(defun lentic-mode-force-clone ()
  (interactive)
  (when (yes-or-no-p "Force Clone of the current buffer? ")
    (lentic-mode-force-clone-1)))
;; #+end_src

;; ** Minor Mode

;; #+begin_src emacs-lisp

;;;###autoload
(defun lentic-mode-toggle-auto-sync-point ()
  (interactive)
  (lentic-when-lentic
   (oset lentic-config :sync-point
         (not (oref lentic-config :sync-point)))))

(defvar lentic-mode-map (make-sparse-keymap)
  "Keymap for lentic-minor-mode")

(define-key lentic-mode-map
  (kbd "C-c ,c") 'lentic-mode-create-from-init)

(define-key lentic-mode-map
  (kbd "C-c ,v") 'lentic-mode-create-new-view-in-selected-window)

(define-key lentic-mode-map
  (kbd "C-c ,n") 'lentic-mode-next-lentic-buffer)

(define-key lentic-mode-map
  (kbd "C-c ,s") 'lentic-mode-swap-lentic-window)

(define-key lentic-mode-map
  (kbd "C-c ,h") 'lentic-mode-move-lentic-window)

(define-key lentic-mode-map
  (kbd "C-c ,b") 'lentic-mode-split-window-below)

(define-key lentic-mode-map
  (kbd "C-c ,t") 'lentic-mode-split-window-right)

(define-key lentic-mode-map
  (kbd "C-c ,f") 'lentic-mode-insert-file-local)

(define-key lentic-mode-map
  (kbd "C-c ,a") 'lentic-mode-show-all-lentic)


(defcustom lentic-mode-line-lighter "Lentic"
  "Default mode lighter for lentic"
  :group 'lentic
  :type 'string)

(defvar-local lentic-mode-line (format " %s[]" lentic-mode-line-lighter))

(defun lentic-mode-update-mode-line ()
  (setq lentic-mode-line
        (format " %s[%s]"
                lentic-mode-line-lighter
                (if lentic-config
                    (s-join ","
                     (-map
                      (lambda (conf)
                        (lentic-mode-line-string conf))
                      lentic-config))
                  ""))))

(defun lentic-mode-update-all-display ()
  (if lentic-emergency
      (setq lentic-mode-line
            (format " %s[Emergency]" lentic-mode-line-lighter))
    (-map
     (lambda (b)
       (lentic-when-with-current-buffer
           b
         (lentic-mode-update-mode-line)))
     (buffer-list))
    (force-mode-line-update t)))

;; ** lentic self-doc

;; #+begin_src: emacs-lisp
;;;###autoload
(defun lentic-mode-doc-eww-view ()
  (interactive)
  (lentic-doc-eww-view 'lentic))

;;;###autoload
(defun lentic-mode-doc-external-view ()
  (interactive)
  (lentic-doc-external-view 'lentic))

;;;###autoload
(define-minor-mode lentic-mode
  "Documentation"
  :lighter lentic-mode-line
  :keymap lentic-mode-map)

;;;###autoload
(easy-menu-change
 '("Edit")
 "Lentic"
 '(["Create All" lentic-mode-create-from-init
    :active (not lentic-config)]
   ["Create View" lentic-mode-create-new-view-in-selected-window]
   ["Next" lentic-mode-next-lentic-buffer
    :active lentic-config]
   ["Split Below" lentic-mode-split-window-below
    :active lentic-config]
   ["Split Right" lentic-mode-split-window-right
    :active lentic-config]
   ["Show All" lentic-mode-show-all-lentic
    :active lentic-config]
   ["Swap" lentic-mode-swap-lentic-window
    :active lentic-config]
   ["Force Clone" lentic-mode-force-clone
    :active lentic-config]
   ["Insert File Local" lentic-mode-insert-file-local]
   ["Read Doc (eww)" lentic-mode-doc-eww-view]
   ["Read Doc (external)" lentic-mode-doc-external-view]
   ))

;;;###autoload
(defun lentic-mode-insert-file-local (init-function)
  (interactive
   (list (completing-read
          "Lentic init function: "
          (mapcar
           'symbol-name
           lentic-init-functions)
          'identity 'confirm)))
  (add-file-local-variable 'lentic-init (intern init-function)))

;;;###autoload
(define-globalized-minor-mode global-lentic-mode
  lentic-mode
  lentic-mode-on)

(defun lentic-mode-on ()
  (lentic-mode 1))

;; #+end_src

(provide 'lentic-mode)

;;; lentic-mode.el ends here
