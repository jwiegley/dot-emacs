;;; phi-search-mc.el --- multiple-cursors extension for phi-search
;;
;; Copyright (c) 2013-2015 Akinori MUSHA
;;
;; All rights reserved.
;;
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;; 1. Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;; 2. Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in the
;;    documentation and/or other materials provided with the distribution.
;;
;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
;; ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
;; FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
;; OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
;; HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
;; LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
;; OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
;; SUCH DAMAGE.

;; Author: Akinori MUSHA <knu@iDaemons.org>
;; URL: https://github.com/knu/phi-search-mc.el
;; Created: 25 Aug 2013
;; Version: 2.2.1
;; Package-Requires: ((phi-search "2.0.0") (multiple-cursors "1.2.1"))
;; Keywords: search, cursors

;;; Commentary:
;;
;; phi-search-mc.el provides the following interactive commands:
;;
;; * phi-search-mc/mark-here
;; * phi-search-mc/mark-next
;; * phi-search-mc/mark-previous
;; * phi-search-mc/mark-all
;;
;;   These functions serve as great way to add fake cursors at your
;;   desired points using phi-search.
;;
;; * phi-search-from-isearch
;; * phi-search-from-isearch-mc/mark-next
;; * phi-search-from-isearch-mc/mark-previous
;; * phi-search-from-isearch-mc/mark-all
;;
;; Run the following line to rebind `mc/mark-next-like-this',
;; `mc/mark-previous-like-this' and `mc/mark-all-like-this' in
;; phi-search buffer to `phi-search-mc/mark-next',
;; `phi-search-mc/mark-previous' and `phi-search-mc/mark-all',
;; respectively.
;
;;   (phi-search-mc/setup-keys)
;;
;; Run the following line to bind `phi-search',
;; `mc/mark-next-like-this', `mc/mark-previous-like-this' and
;; `mc/mark-all-like-this' in isearch mode to
;; `phi-search-from-isearch', `phi-search-from-isearch-mc/mark-next',
;; `phi-search-from-isearch-mc/mark-previous' and
;; `phi-search-from-isearch-mc/mark-all', respectively.
;;
;;   (add-hook 'isearch-mode-hook 'phi-search-from-isearch-mc/setup-keys)
;;
;; If you have bound multi-stroke keys to `mc/mark-next-like-this'
;; etc., this may not be enough.  For example, I bound
;; [C->]/[C-<]/[C-. !] to mc/mark-* functions, and since they are
;; complex multi-stroke keys on my terminal emulator where [C->] is
;; mapped to [C-x @ c >] etc., I had to add the following lines for
;; the features to work properly.
;;
;;   (defvar phi-search-from-isearch-mc/ctl-map
;;     (let ((map (make-sparse-keymap)))
;;       (define-key map (kbd ">")   'phi-search-from-isearch-mc/mark-next)
;;       (define-key map (kbd "<")   'phi-search-from-isearch-mc/mark-previous)
;;       (define-key map (kbd ". !") 'phi-search-from-isearch-mc/mark-all)
;;       map))
;;
;;   (defadvice phi-search-from-isearch-mc/setup-keys
;;     (after for-terminal activate)
;;     (define-key isearch-mode-map (kbd "C-x @ c") phi-search-from-isearch-mc/ctl-map))

;;; Code:

(require 'phi-search)
(require 'multiple-cursors)

(eval-when-compile
  (require 'cl))

(defvar phi-search--mc/fake-cursors nil
  "Keeps a list of fake cursors that are activated after exiting phi-search.")
(make-variable-buffer-local 'phi-search--mc/fake-cursors)

(defun phi-search--mc/fake-cursor-p (ov)
  (eq (overlay-get ov 'type) 'phi-search--fake-cursor))

(defun phi-search--mc/fake-cursor-at-pos-p (pos)
  (loop for ov in (overlays-at pos)
        thereis (phi-search--mc/fake-cursor-p ov)))

(defun phi-search--mc/add-fake-cursor (pos)
  (or
   (phi-search--mc/fake-cursor-at-pos-p pos)
   (let ((ov (make-overlay pos (1+ pos) nil nil nil)))
     (overlay-put ov 'type 'phi-search--fake-cursor)
     (overlay-put ov 'face 'mc/cursor-face)
     (add-to-list 'phi-search--mc/fake-cursors ov))))

(defmacro phi-search--mc/mark-do (&rest body)
  `(progn
     (phi-search--with-target-buffer
      (when (> (mc/num-cursors) 1)
        ;; Save existing fake cursors and remove them, or they
        ;; will move when phi-search exits.
        (mc/for-each-fake-cursor
         (phi-search--mc/add-fake-cursor (overlay-start cursor)))
        (mc/remove-fake-cursors))
      ,@body)
     (if (minibufferp)
         (add-hook 'minibuffer-exit-hook
                   'phi-search--mc/minibuffer-exit-hook)
       (add-hook (make-local-variable 'kill-buffer-hook)
                 'phi-search--mc/activate-fake-cursors))))

(defun phi-search--mc/activate-fake-cursors ()
  (and phi-search--target
       (phi-search--with-target-buffer
        (loop for ov in phi-search--mc/fake-cursors do
              (let ((pos (overlay-start ov)))
                (delete-overlay ov)
                (and (/= pos (point))
                     (loop for o in (overlays-at pos)
                           never (mc/fake-cursor-p o))
                     (mc/save-excursion
                      (goto-char pos)
                      (mc/create-fake-cursor-at-point)))))
        (setq phi-search--mc/fake-cursors nil)
        (mc/maybe-multiple-cursors-mode)
        ;; Prevent the fake cursors from moving via mc's post-command-hook
        (setq this-original-command nil))))

(defun phi-search--mc/minibuffer-exit-hook ()
  (phi-search--mc/activate-fake-cursors)
  (remove-hook 'minibuffer-exit-hook 'phi-search--mc/minibuffer-exit-hook))

;;;###autoload
(defun phi-search-mc/mark-here (&optional arg)
  "Mark the current match as fake cursor.

With an optional argument, mark the beginning of the match instead of the end."
  (interactive "P")
  (phi-search--mc/mark-do
   (phi-search--mc/add-fake-cursor
    (let ((ov (nth phi-search--selection phi-search--overlays)))
      (if arg (overlay-start ov)
          (overlay-end ov))))))

;;;###autoload
(defun phi-search-mc/mark-next (n)
  "Mark the current match as fake cursor and search next item.

With an optional number argument, marking repeats as many times
as the absolute value of the number.  If a negative argument is
given, the beginning of the match is marked instead of the end."
  (interactive "p")
  (let* ((neg (< n 0)) (n (if neg (- n) n)))
    (dotimes (_ n)
      (phi-search-mc/mark-here neg)
      (phi-search-again-or-next))))

;;;###autoload
(defun phi-search-mc/mark-previous (n)
  "Mark the current match as fake cursor and search previous item.

With an optional number argument, marking repeats as many times
as the absolute value of the number.  If a negative argument is
given, the beginning of the match is marked instead of the end."
  (interactive "p")
  (let* ((neg (< n 0)) (n (if neg (- n) n)))
    (dotimes (_ n)
      (phi-search-mc/mark-here neg)
      (phi-search-again-or-previous))))

;;;###autoload
(defun phi-search-mc/mark-all ()
  "Mark all matches as fake cursors."
  (interactive)
  (phi-search--mc/mark-do
   (dolist (ov phi-search--overlays)
     (phi-search--mc/add-fake-cursor
      (overlay-end ov)))))

;;;###autoload
(defun phi-search-mc/setup-keys ()
  (let ((map phi-search-default-map))
    (define-key map [remap mc/mark-next-like-this]     'phi-search-mc/mark-next)
    (define-key map [remap mc/mark-previous-like-this] 'phi-search-mc/mark-previous)
    (define-key map [remap mc/mark-all-like-this]      'phi-search-mc/mark-all)))

;;;###autoload
(defun phi-search-from-isearch (&optional init-func)
  "Switch to phi-search inheriting the current isearch query.
Currently whitespace characters are taken literally, ignoring
`isearch-lax-whitespace' or `isearch-regexp-lax-whitespace'."
  (interactive)
  (let ((forward isearch-forward)
        (query (cond ((eq isearch-word 'isearch-symbol-regexp)
                      (isearch-symbol-regexp isearch-string))
                     (isearch-word
                      (word-search-regexp isearch-string))
                     (isearch-regexp
                      isearch-string)
                     (t
                      (regexp-quote isearch-string)))))
    (goto-char isearch-other-end)
    (isearch-exit)
    (let ((phi-search-init-hook phi-search-init-hook))
      (add-hook 'phi-search-init-hook
                (lambda ()
                  (insert query)
                  (and isearch-word
                       (string-match "\\(\\\\_?>\\)\\'" query)
                       (backward-char (length (match-string 1 query))))))
      (if init-func
          (add-hook 'phi-search-init-hook init-func t))
      (if forward (phi-search)
        (phi-search-backward)))))

(defmacro phi-search-from-isearch-do (&rest body)
  `(phi-search-from-isearch #'(lambda () ,@body)))

;;;###autoload
(defun phi-search-from-isearch-mc/mark-next (arg)
  "Switch to phi-search, mark the current isearch match and search next match."
  (interactive "p")
  (phi-search-from-isearch-do
   (phi-search-mc/mark-next arg)))

;;;###autoload
(defun phi-search-from-isearch-mc/mark-previous (arg)
  "Switch to phi-search, mark the current isearch match and search previous match."
  (interactive "p")
  (phi-search-from-isearch-do
   (phi-search-mc/mark-previous arg)))

;;;###autoload
(defun phi-search-from-isearch-mc/mark-all ()
  "Switch to phi-search and mark all isearch matches."
  (interactive)
  (phi-search-from-isearch-do
   (phi-search-mc/mark-all)))

;;;###autoload
(defun phi-search-from-isearch-mc/setup-keys ()
  (let ((map isearch-mode-map))
    (define-key map [remap phi-search]                 'phi-search-from-isearch)
    (define-key map [remap mc/mark-next-like-this]     'phi-search-from-isearch-mc/mark-next)
    (define-key map [remap mc/mark-previous-like-this] 'phi-search-from-isearch-mc/mark-previous)
    (define-key map [remap mc/mark-all-like-this]      'phi-search-from-isearch-mc/mark-all)))

(provide 'phi-search-mc)

;;; phi-search-mc.el ends here
