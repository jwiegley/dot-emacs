;;; lentic-dev.el --- Tools for developers -*- lexical-binding: t -*-

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

;; Developing support for new forms of lentic buffers is not trivial. This
;; file provides some support functions for doing so.

;;; Code:

;; #+begin_src emacs-lisp
(require 'lentic)

;; #+end_src

;; ** Manual Updates

;; Usually, lentic uses Emacs hooks to percolate changes in one buffer to
;; another. Unfortunately, all the hooks that do this not only silently discard
;; errors, but they delete the offending function from the hook. So, post-mortem
;; debugging is hard. Step-through is also hard since it happens in the command
;; loop.

;; Lentic has a function for disabling its functionality (due to breakage
;; rather than just normal switching it off), called `linked-buffer-emergency'
;; (and the inverse `linked-buffer-unemergency'). In this emergency state, we
;; can still run the hooks manually, which is by far the best way to debug them.

;; For the `lentic-test-after-change-function' to work `lentic-emergency-debug'
;; must be set. It is also critical that only a single change has happened before
;; this function is called -- otherwise the result of the previous change are
;; deleted, and the lentic buffers will update in an inconsistent and haphazard
;; way.


;; #+begin_src emacs-lisp
;;;###autoload
(defun lentic-dev-after-change-function ()
  "Run the change functions out of the command loop.
Using this function is the easiest way to test an new
`lentic-clone' method, as doing so in the command loop is
painful for debugging. Set variable `lentic-emergency' to
true to disable command loop functionality."
  (interactive)
  (message "Running after change with args: %s"
           lentic-emergency-last-change)
  (apply 'lentic-after-change-function-1
         lentic-emergency-last-change))

;;;###autoload
(defun lentic-dev-post-command-hook ()
  "Run the post-command functions out of the command loop.
Using this function is the easiest way to test an new
`lentic-convert' method, as doing so in the command loop is
painful for debugging. Set variable `lentic-emergency' to
true to disable command loop functionality."
  (interactive)
  (lentic-post-command-hook-1 (current-buffer) '()))

;;;###autoload
(defun lentic-dev-after-save-hook ()
  (interactive)
  (let ((lentic-emergency nil))
    (lentic-mode-after-save-hook)))

;;;###autoload
(defun lentic-dev-mode-buffer-list-update-hook ()
  (interactive)
  (let ((lentic-emergency nil))
    (lentic-mode-buffer-list-update-hook)))

;;;###autoload
(defun lentic-dev-kill-buffer-hook ()
  (interactive)
  (let ((lentic-emergency nil))
    (lentic-kill-buffer-hook)))

;;;###autoload
(defun lentic-dev-kill-emacs-hook ()
  (interactive)
  (let ((lentic-emergency nil))
    (lentic-kill-emacs-hook)))

;;;###autoload
(defun lentic-dev-reinit ()
  "Recall the init function regardless of current status.
This can help if you have change the config object and need
to make sure there is a new one."
  (interactive)
  (setq lentic-config nil)
  (lentic-ensure-init))

;; #+end_src

;; ** Font-Lock changes

;; These commands enable or disable fontification of changes that lentic has
;; percolated. This is very useful for incremental changes; it's the only
;; practical way of seeing what has been copied.

;; The exact behaviour of this depends on the mode of the buffer displaying the
;; lentic buffer. Sometimes, the natural buffer fontification functions just
;; change the font back to whatever the syntax suggests. In this case, try
;; switching off `font-lock-mode'.

;; #+begin_src emacs-lisp

(defvar lentic-dev-insert-face
  "Start face to use for inserted text."
  'font-lock-keyword-face)

;;;###autoload
(defun lentic-dev-random-face ()
  "Change the insertion face to a random one."
  (interactive)
  (setq lentic-dev-insert-face
        (nth (random (length (face-list)))
             (face-list)))
  (message "Insert face is now %s"
           (propertize
            "this"
            'face
            lentic-dev-insert-face)))

(defadvice lentic-insertion-string-transform
  (after face-transform
         (string)
         disable)
  (setq ad-return-value
        (propertize
         string
         'font-lock-face
         lentic-dev-insert-face
         'face
         lentic-dev-insert-face)))

(defvar lentic-dev-enable-insertion-marking nil)

;;;###autoload
(defun lentic-dev-enable-insertion-marking ()
  "Enable font locking properties for inserted text."
  (interactive)
  (if lentic-dev-enable-insertion-marking
      (progn
        (ad-deactivate 'lentic-insertion-string-transform)
        (setq lentic-enable-insertion-marking nil)
        (message "Insertion marking off"))
    (ad-enable-advice 'lentic-insertion-string-transform
                      'after 'face-transform)
    (ad-activate 'lentic-insertion-string-transform)
    (setq lentic-enable-insertion-marking t)
    (message "Insertion marking on")))


(defadvice lentic-after-change-transform
    (after pulse-transform (buffer start stop length-before) disable)
  (with-current-buffer
      buffer
    (pulse-momentary-highlight-region
     (or start (point-min))
     (or stop (point-max)))))

(defvar lentic-dev-enable-insertion-pulse nil)

;;;###autoload
(defun lentic-dev-enable-insertion-pulse ()
  (interactive)
  (if lentic-dev-enable-insertion-pulse
      (progn
        (ad-deactivate 'lentic-after-change-transform)
        (setq lentic-dev-enable-insertion-pulse nil)
        (message "insertion pulse off"))
    (ad-enable-advice 'lentic-after-change-transform
                      'after 'pulse-transform)
    (ad-activate 'lentic-after-change-transform)
    (setq lentic-dev-enable-insertion-pulse t)
    (message "insertion pulse on")))


(defun lentic-dev-edebug-trace-mode ()
  (setq edebug-initial-mode 'continue)
  (setq edebug-trace t))


(defun lentic-dev-highlight-markers ()
  (interactive)
  (m-buffer-overlay-font-lock-face-match
   (lentic-blk-marker-boundaries
    (car lentic-config)
    (current-buffer))
   'highlight))

(provide 'lentic-dev)
;;; lentic-dev.el ends here

;; #+end_src
