;;; wrap-region.el --- Wrap text with punctation or tag

;; Copyright (C) 2008-2010 Johan Andersson

;; Author: Johan Andersson <johan.rejeep@gmail.com>
;; Maintainer: Johan Andersson <johan.rejeep@gmail.com>
;; Version: 0.4.0
;; Keywords: speed, convenience
;; URL: http://github.com/rejeep/wrap-region

;; This file is NOT part of GNU Emacs.


;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.


;;; Commentary:

;; wrap-region is a minor mode that wraps a region with
;; punctuations. For tagged markup modes, such as HTML and XML, it
;; wraps with tags.
;;
;; To use wrap-region, make sure that this file is in Emacs load-path:
;;   (add-to-list 'load-path "/path/to/directory/or/file")
;;
;; Then require wrap-region:
;;   (require 'wrap-region)

;; To start wrap-region:
;;   (wrap-region-mode t) or M-x wrap-region-mode
;;
;; If you only want wrap-region active in some mode, use hooks:
;;   (add-hook 'ruby-mode-hook 'wrap-region-mode)
;;
;; Or if you want to activate it in all buffers, use the global mode:
;;   (wrap-region-global-mode t)

;; To wrap a region, select that region and hit one of the punctuation
;; keys. In "tag-modes"" (see `wrap-region-tag-active-modes'), "<" is
;; replaced and wraps the region with a tag. To activate this behavior
;; in a mode that is not default:
;;   (add-to-list 'wrap-region-tag-active-modes 'some-tag-mode)
;;
;; `wrap-region-table' contains the default punctuations
;; that wraps. You can add and remove new wrappers by using the
;; functions `wrap-region-add-wrapper' and
;; `wrap-region-remove-wrapper' respectively.
;;   (wrap-region-add-wrapper "`" "'")                  ; hit ` then region -> `region'
;;   (wrap-region-add-wrapper "/*" "*/" "/")            ; hit / then region -> /*region*/
;;   (wrap-region-add-wrapper "$" "$" nil 'latex-mode)  ; hit $ then region -> $region$ in latex-mode
;;   (wrap-region-remove-wrapper "(")
;;   (wrap-region-remove-wrapper "$" 'latex-mode)
;;
;; Some modes may have conflicting key bindings with wrap-region. To
;; avoid conflicts, the list `wrap-region-except-modes' contains names
;; of modes where wrap-region should not be activated (note, only in
;; the global mode). You can add new modes like this:
;;   (add-to-list 'wrap-region-except-modes 'conflicting-mode)


;;; Code:

(eval-when-compile
  (require 'cl))


(defstruct wrap-region-wrapper key left right modes)

(defvar wrap-region-mode-map (make-sparse-keymap)
  "Keymap for `wrap-region-mode'.")

(defvar wrap-region-table (make-hash-table :test 'equal)
  "Table with wrapper pairs.")

(defvar wrap-region-tag-active-modes '(html-mode sgml-mode rhtml-mode)
  "List of modes that uses tags.")

(defvar wrap-region-except-modes '(calc-mode dired-mode)
  "A list of modes in which `wrap-region-mode' should not be activated.")

(defvar wrap-region-hook nil
  "Called when `wrap-region-mode' is turned on.")

(defvar wrap-region-before-wrap-hook nil
  "Called before wrapping.")

(defvar wrap-region-after-wrap-hook nil
  "Called after wrapping.")


(defun wrap-region-trigger ()
  "Called when trigger key is pressed."
  (interactive)
  (let* ((key (char-to-string last-input-event))
         (wrapper (wrap-region-find key)))
    (if (and (region-active-p) wrapper)
        (if (wrap-region-insert-tag-p key)
            (wrap-region-with-tag)
          (wrap-region-with-punctuations
           (wrap-region-wrapper-left wrapper)
           (wrap-region-wrapper-right wrapper)))
      (wrap-region-fallback key))))

(defun wrap-region-find (key)
  "Finds first wrapper with trigger KEY that should be active in MAJOR-MODE."
  (let ((wrappers (gethash key wrap-region-table)))
    (or
     (find-if
      (lambda (wrapper)
        (member major-mode (wrap-region-wrapper-modes wrapper)))
      wrappers)
     (find-if
      (lambda (wrapper)
        (not (wrap-region-wrapper-modes wrapper)))
      wrappers))))

(defun wrap-region-insert-tag-p (key)
  "Checks if tag should be inserted or not."
  (and
   (equal key "<")
   (member major-mode wrap-region-tag-active-modes)))

(defun wrap-region-with-tag ()
  "Wraps region with tag."
  (let* ((tag (read-string "Enter Tag (with optional attributes): "))
         (split (split-string tag " "))
         (tag-name (car split))
         (left (concat "<" tag ">"))
         (right (concat "</" tag-name ">")))
    (wrap-region-with left right)))

(defun wrap-region-with-punctuations (left right)
  "Wraps region with LEFT and RIGHT punctuations."
  (wrap-region-with left right))

(defun wrap-region-with (left right)
  "Wraps region with LEFT and RIGHT."
  (run-hooks 'wrap-region-before-wrap-hook)
  (let ((beg (region-beginning)) (end (region-end)))
    (save-excursion
      (goto-char beg)
      (insert left)
      (goto-char (+ end (length left)))
      (insert right)))
  (run-hooks 'wrap-region-after-wrap-hook))

(defun wrap-region-fallback (key)
  "Executes function that KEY was bound to before `wrap-region-mode'."
  (let ((wrap-region-mode nil))
    (call-interactively
     (key-binding
      (read-kbd-macro key)))))

(defun wrap-region-add-wrappers (wrappers)
  "Add WRAPPERS by calling `wrap-region-add-wrapper' for each one."
  (mapc
   (lambda (wrapper)
     (apply 'wrap-region-add-wrapper wrapper))
   wrappers))

(defun wrap-region-add-wrapper (left right &optional key mode-or-modes)
  "Add new LEFT and RIGHT wrapper.

Optional KEY is the trigger key and MODE-OR-MODES is a single
mode or multiple modes that the wrapper should trigger in."
  (or key (setq key left))
  (let ((wrappers (gethash key wrap-region-table))
        (modes
         (if mode-or-modes
             (if (listp mode-or-modes)
                 mode-or-modes
               (list mode-or-modes)))))
    (if wrappers
        (let ((wrapper-exactly-same
               (find-if
                (lambda (wrapper)
                  (and
                   (equal (wrap-region-wrapper-key wrapper) key)
                   (equal (wrap-region-wrapper-left wrapper) left)
                   (equal (wrap-region-wrapper-right wrapper) right)))
                wrappers)))
          (if wrapper-exactly-same
              (when (wrap-region-wrapper-modes wrapper-exactly-same)
                (if modes
                    (setf
                     (wrap-region-wrapper-modes wrapper-exactly-same)
                     (union modes (wrap-region-wrapper-modes wrapper-exactly-same)))
                  (let ((new-wrapper (make-wrap-region-wrapper :key key :left left :right right)))
                    (puthash key (cons new-wrapper wrappers) wrap-region-table))))
            (let* ((new-wrapper (make-wrap-region-wrapper :key key :left left :right right :modes modes))
                   (wrapper-same-trigger
                    (find-if
                     (lambda (wrapper)
                       (equal (wrap-region-wrapper-key wrapper) key))
                     wrappers))
                   (wrapper-same-trigger-modes
                    (wrap-region-wrapper-modes wrapper-same-trigger)))
              (when (and wrapper-same-trigger wrapper-same-trigger-modes)
                (let ((new-modes (nset-difference (wrap-region-wrapper-modes wrapper-same-trigger) modes)))
                  (if new-modes
                      (setf (wrap-region-wrapper-modes wrapper-same-trigger) new-modes)
                    (setq wrappers (delete wrapper-same-trigger wrappers)))))
              (puthash key (cons new-wrapper wrappers) wrap-region-table))))
      (let ((new-wrapper (make-wrap-region-wrapper :key key :left left :right right :modes modes)))
        (puthash key (list new-wrapper) wrap-region-table))))
  (wrap-region-define-trigger key))

(defun wrap-region-remove-wrapper (key &optional mode-or-modes)
  "Remove wrapper with trigger KEY or exclude from MODE-OR-MODES.

If MODE-OR-MODES is not present, all wrappers for KEY are removed."
  (if mode-or-modes
      (let ((wrappers (gethash key wrap-region-table))
            (modes
             (if mode-or-modes
                 (if (listp mode-or-modes)
                     mode-or-modes
                   (list mode-or-modes)))))
        (mapc
         (lambda (mode)
           (let ((wrapper-including-mode
                  (find-if
                   (lambda (wrapper)
                     (member mode (wrap-region-wrapper-modes wrapper)))
                   wrappers)))
             (when wrapper-including-mode
               (let ((new-modes (delete mode (wrap-region-wrapper-modes wrapper-including-mode))))
                 (if new-modes
                     (setf (wrap-region-wrapper-modes wrapper-including-mode) new-modes)
                   (puthash key (delete wrapper-including-mode wrappers) wrap-region-table))))))
         modes))
    (wrap-region-destroy-wrapper key)))

(defun wrap-region-destroy-wrapper (key)
  "Removes the wrapper bound to KEY, no questions asked."
  (remhash key wrap-region-table)
  (wrap-region-unset-key key))

(defun wrap-region-define-wrappers ()
  "Defines defaults wrappers."
  (mapc
   (lambda (pair)
     (apply 'wrap-region-add-wrapper pair))
   '(("\"" "\"")
     ("'"  "'")
     ("("  ")")
     ("{"  "}")
     ("["  "]")
     ("<"  ">"))))

(defun wrap-region-define-trigger (key)
  "Defines KEY as wrapper."
  (wrap-region-define-key key 'wrap-region-trigger))

(defun wrap-region-unset-key (key)
  "Remove KEY from `wrap-region-mode-map'."
  (wrap-region-define-key key))

(defun wrap-region-define-key (key &optional fn)
  "Binds KEY to FN in `wrap-region-mode-map'."
  (define-key wrap-region-mode-map (read-kbd-macro key) fn))


;;;###autoload
(define-minor-mode wrap-region-mode
  "Wrap region with stuff."
  :init-value nil
  :lighter " wr"
  :keymap wrap-region-mode-map
  (when wrap-region-mode
    (wrap-region-define-wrappers)
    (run-hooks 'wrap-region-hook)))

;;;###autoload
(defun turn-on-wrap-region-mode ()
  "Turn on `wrap-region-mode'"
  (interactive)
  (unless (member major-mode wrap-region-except-modes)
    (wrap-region-mode +1)))

;;;###autoload
(defun turn-off-wrap-region-mode ()
  "Turn off `wrap-region-mode'"
  (interactive)
  (wrap-region-mode -1))

;;;###autoload
(define-globalized-minor-mode wrap-region-global-mode
  wrap-region-mode
  turn-on-wrap-region-mode)

(provide 'wrap-region)

;;; wrap-region.el ends here
