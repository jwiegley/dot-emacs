;;; selectkey --- Select buffers by type with a single key

;; Copyright (C) 2008-2012 Martin Cracauer
;; Copyright (C) 2008-2012 Edward O'Connor
;; Copyright (C) 2012      John Wiegley

;; Author: Martin Cracauer
;;         Edward O'Connor
;;         John Wiegley <johnw@newartisans.com>
;; Created: 5 Sep 2008 (or earlier)
;; Version: 1.0
;; Keywords: select buffers
;; X-URL: http://www.emacswiki.org/emacs/SelectKey

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Martin Cracauer wrote some code which emulates the SELECT key from a
;; Symbolics Lisp machine. EdwardOConnor adapted that some, and here’s my
;; adaptation of that along with some keybindings that I commonly use.

(defgroup selectkey nil
  "Select buffers by type with a single key"
  :group 'emacs)

;; selectkey-f8-prefix-map is a sparse keymap defined earlier in my .emacs
;;(defvar selectkey-select-prefix-map selectkey-f8-prefix-map)

;; updated 7/30/07 now works with 22.1
(defvar selectkey-select-prefix-map)
(define-prefix-command 'selectkey-select-prefix-map)
;; (global-set-key [f8] selectkey-select-prefix-map)

(global-set-key [menu] selectkey-select-prefix-map)
(global-set-key [apps] selectkey-select-prefix-map)

(defun selectkey-get-repeat-prefix ()
  (let (keys)
    (and (setq keys (this-single-command-keys))
         (> (length keys) 1)
         keys)))

(defun selectkey-repeat-on-last-key (keys)
  (setq keys (vconcat keys))
  (let ((n (1- (length keys)))
        cmd done repeat)
    (while (and (not done)
                (aset keys n (read-event))
                (setq cmd (key-binding keys t)))
      (clear-this-command-keys t)
      (funcall cmd nil)
      (setq last-input-event nil)))
  (when last-input-event
    (clear-this-command-keys t)
    (setq unread-command-events (list last-input-event))))

(defun selectkey-display-select-bindings ()
  (interactive)
  (describe-bindings [f8]))

(define-key selectkey-select-prefix-map "?" 'selectkey-display-select-bindings)

(defmacro selectkey-define-select-key
  (fname-base key &optional buf-form else-form)
  "Define a select-key function FNAME-BASE bound on KEY.

If provided, BUF-FORM should be a form which will attempt to return
a buffer to switch to.  If it returns nil, ELSE-FORM is evaluated."
  (let ((fname (intern (concat "selectkey-select-" (symbol-name fname-base)))))
    `(progn
       (defun ,fname (arg)
         (interactive "P")
         (let ((keys (selectkey-get-repeat-prefix)))
           (let ((buf
                  (catch 'found
                    (ignore
                     (mapc #'(lambda (buf)
                               (and (string-match ,buf-form (buffer-name
                                                             buf))
                                    (throw 'found buf)))
                           (cdr (buffer-list)))))))
             (if buf
                 (switch-to-buffer buf)
               ,else-form))
           (if keys
               (selectkey-repeat-on-last-key keys))))
       (define-key selectkey-select-prefix-map ,key ',fname))))

(put 'selectkey-define-select-key 'lisp-indent-function 2)

(defmacro selectkey-define-select-key-class
  (fname-base key regexp &optional default-dir)
  `(selectkey-define-select-key
       ,(intern (concat (symbol-name fname-base) "-file")) ,key
     ,regexp
     ;; Allow ido or other overrides to take effect
     (let ((default-directory (or ,default-dir
                                  default-directory)))
       (call-interactively #'find-file))))

;; These are the file types I use at least semi-regularly.

(selectkey-define-select-key-class C          "c" "\\.c\\'")
(selectkey-define-select-key-class Emacs-Lisp "e" "\\.el\\'"
                                   user-emacs-directory)
(selectkey-define-select-key-class HTML       "h" "\\.s?html\\'")
(selectkey-define-select-key-class Lisp       "l" "\\.\\(lisp\\|lsp\\)\\'")
(selectkey-define-select-key-class LaTeX      "t" "\\.tex\\'")
(selectkey-define-select-key-class Makefile   "M" "\\(GNU\\)?[Mm]akefile")
(selectkey-define-select-key-class m4         "4" "\\.m4\\'")

;; For easy access to a few commonly accessed files/buffers.

(defvar selectkey-dotemacs-file "~/.emacs.d/emacs.el")

(selectkey-define-select-key dotemacs-file "."
  selectkey-dotemacs-file
  (find-file selectkey-dotemacs-file))

(selectkey-define-select-key home-directory "~"
  "\\`~\\'"
  (dired "~"))

;; That ~ key is impossible to type...
(define-key selectkey-select-prefix-map "`"
  'selectkey-select-home-directory)

(selectkey-define-select-key info "i"
  "\\`\\*info\\*\\'"
  (info))

(selectkey-define-select-key shell "!"
  "\\`\\*eshell\\*\\'"
  (eshell))

(selectkey-define-select-key gnus "g"
  "\\`\\*Group\\*\\'"
  (gnus))

(provide 'selectkey)

;;; selectkey.el ends here
