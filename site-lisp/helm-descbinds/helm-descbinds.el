;;; helm-descbinds.el --- A convenient `describe-bindings' with `helm'   -*- lexical-binding: t -*-

;; Copyright (C) 2008, 2009, 2010  Taiki SUGAWARA <buzz.taiki@gmail.com>
;; Copyright (C) 2012, 2013  Michael Markert <markert.michael@googlemail.com>
;; Copyright (C) 2013 Daniel Hackney <dan@haxney.org>
;; Copyright (C) 2015, 2016 Michael Heerdegen <michael_heerdegen@web.de>

;; Author: Taiki SUGAWARA <buzz.taiki@gmail.com>
;; URL: https://github.com/emacs-helm/helm-descbinds
;; Keywords: helm, help
;; Version: 1.12
;; Package-Requires: ((helm "1.5"))

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.


;;; Commentary:
;; This package is a replacement of `describe-bindings' for Helm.

;; Usage:
;;
;; You can use this package independently from Helm - in particular,
;; you don't need to turn on `helm-mode' to be able to use this.  Helm
;; just needs to be installed.
;;
;; Add followings on your .emacs.
;;
;;   (require 'helm-descbinds)
;;   (helm-descbinds-mode)
;;
;; or use customize to set `helm-descbinds-mode' to t.
;;
;; Now, `describe-bindings' is replaced with `helm-descbinds'. As
;; usual, type `C-h b', or any incomplete key sequence plus C-h , to
;; run `helm-descbinds'.  The bindings are presented in a similar way
;; as `describe-bindings ' does, but you can use completion to find
;; the command you searched for and execute it, or view it's
;; documentation.
;;
;; In the Helm completions buffer, you match key bindings with the
;; Helm interface:
;;
;;  - When you type RET, the selected candidate command is executed.
;;
;;  - When you hit RET on a prefix key, the candidates are narrowed to
;;    this prefix
;;
;;  - When you type TAB, you can select "Execute", "Describe" or "Find
;;    Function" by the menu (i.e. these are the available "actions"
;;    and are of course also available via their usual shortcuts).
;;
;;  - When you type C-z (aka "persistent action"), the selected
;;    command is described without quitting Helm.



;;; Code:

(eval-when-compile (require 'cl-lib)) ;cl-loop
(require 'helm)

(defgroup helm-descbinds nil
  "A convenient `describe-bindings' with `helm'."
  :prefix "helm-descbinds-"
  :group 'helm)

(defcustom helm-descbinds-actions
  '(("Execute" . helm-descbinds-action:execute)
    ("Describe" . helm-descbinds-action:describe)
    ("Find Function" . helm-descbinds-action:find-func))
  "Actions of selected candidate."
  :type '(repeat
	  (cons
	   :tag "Action"
	   (string :tag "Name")
	   (function :tag "Function"))))

(defcustom helm-descbinds-candidate-formatter
  #'helm-descbinds-default-candidate-formatter
  "Candidate formatter function.
This function will be called with two arguments KEY and BINDING."
  :type 'function)

(defcustom helm-descbinds-window-style 'one-window
  "Window splitting style."
  :type '(choice
	  (const :tag "One Window" one-window)
	  (const :tag "Same Window" same-window)
	  (const :tag "Split Window" split-window)))

(defcustom helm-descbinds-section-order
  '("Major Mode Bindings" "Minor Mode Bindings" "Global Bindings")
  "A list of section order by name regexp."
  :type '(repeat (regexp :tag "Regexp")))

(defvar helm-descbinds-Orig-describe-bindings (symbol-function 'describe-bindings))
(defvar helm-descbind--initial-full-frame helm-full-frame)

;;;###autoload
(define-minor-mode helm-descbinds-mode
  "Use `helm' for `describe-bindings'."
  :group 'helm-descbinds
  :global t
  (if helm-descbinds-mode
      (advice-add 'describe-bindings :override #'helm-descbinds)
      (advice-remove 'describe-bindings #'helm-descbinds)))

;;;###autoload
(defun helm-descbinds-install ()
  "Use `helm-descbinds' as a replacement of `describe-bindings'."
  (interactive)
  (helm-descbinds-mode 1))
(make-obsolete 'helm-descbinds-install 'helm-descbinds-mode "1.08")

;;;###autoload
(defun helm-descbinds-uninstall ()
  "Restore original `describe-bindings'."
  (interactive)
  (helm-descbinds-mode -1))
(make-obsolete 'helm-descbinds-uninstall 'helm-descbinds-mode "1.08")

(defun helm-descbinds-all-sections (buffer &optional prefix menus)
  (with-temp-buffer
    (let ((indent-tabs-mode t))
      (describe-buffer-bindings buffer prefix menus))
    (goto-char (point-min))
    (let ((header-p (not (= (char-after) ?\f)))
	  sections header section)
      (while (not (eobp))
	(cond
	 (header-p
	  (setq header (buffer-substring-no-properties
			(point)
			(line-end-position)))
	  (setq header-p nil)
	  (forward-line 3))
	 ((= (char-after) ?\f)
	  (push (cons header (nreverse section)) sections)
	  (setq section nil)
	  (setq header-p t))
	 ((looking-at "^[ \t]*$")
	  ;; ignore
	  )
	 (t
	  (let ((binding-start (save-excursion
				 (and (re-search-forward "\t+" nil t)
				      (match-end 0))))
		key binding)
	    (when binding-start
	      (setq key (buffer-substring-no-properties (point) binding-start)
		    key (replace-regexp-in-string"^[ \t\n]+" "" key)
		    key (replace-regexp-in-string"[ \t\n]+$" "" key))
	      (goto-char binding-start)
	      (setq binding (buffer-substring-no-properties
			     binding-start
			     (line-end-position)))
	      (unless (member binding '("self-insert-command"))
		(push (cons key binding) section))))))
	(forward-line))
      (push (cons header (nreverse section)) sections)
      (nreverse sections))))

(defun helm-descbinds-action:execute (candidate)
  "An action that execute selected CANDIDATE command."
  (let ((x (cdr candidate))
        (helm-full-frame helm-descbind--initial-full-frame))
    (cond
     ((equal x "Keyboard Macro")
      (command-execute (kbd (car candidate))))
     ((stringp x)
      (insert x))
     ((commandp x)
      (run-at-time 0.01 nil (lambda (command) (call-interactively command)) x)))))

(defun helm-descbinds-action:describe (candidate)
  "An action that describe selected CANDIDATE function."
  (let ((name (cdr candidate)))
    (if (equal name "Keyboard Macro")
        (describe-key (kbd (car candidate)))
      (describe-function name))))

(defun helm-descbinds-action:find-func (candidate)
  "An action that find selected CANDIDATE function."
  (find-function (cdr candidate)))

(defun helm-descbinds-default-candidate-formatter (key binding)
  "Default candidate formatter."
  (format "%-10s\t%s" key binding))

(defun helm-descbinds-order-section (section)
  (cl-loop for n = 0 then (1+ n)
           for regexp in helm-descbinds-section-order
           if (and (car section) (string-match regexp (car section)))
           return n
           finally
           return n))

(defun helm-descbinds-transform-candidates (candidates)
  (cl-loop for (key . command) in candidates
           for sym = (intern-soft command)
           collect
           (cons (funcall helm-descbinds-candidate-formatter key command)
                 (cons key (if (commandp sym) sym command)))))

(defun helm-descbinds-action-transformer (actions cand)
  "Default action transformer for `helm-descbinds'.
Provide a useful behavior for prefix commands."
  (if (stringp (cdr cand))
      (helm-make-actions
       "helm-descbinds this prefix"
       (lambda (cand)
         (describe-bindings (kbd (car cand)))))
      actions))

(defun helm-descbinds-sources (buffer &optional prefix menus)
  (mapcar
   (lambda (section)
     (helm-descbinds-source (car section) (cdr section)))
   (sort
    (helm-descbinds-all-sections buffer prefix menus)
    (lambda (a b)
      (< (helm-descbinds-order-section a)
         (helm-descbinds-order-section b))))))

(defclass helm-descbinds-source-class (helm-source-sync) ())

(defun helm-descbinds-source (name candidates)
  (when (and name candidates)
    (helm-make-source name 'helm-descbinds-source-class
      :candidates candidates
      :candidate-transformer #'helm-descbinds-transform-candidates
      :filtered-candidate-transformer #'helm-fuzzy-highlight-matches
      :persistent-action #'helm-descbinds-action:describe
      :action-transformer #'helm-descbinds-action-transformer
      :action 'helm-descbinds-actions)))

;;;###autoload
(defun helm-descbinds (&optional prefix buffer)
  "A convenient helm version of `describe-bindings'.

Turning on `helm-descbinds-mode' is the recommended way to
install this command to replace `describe-bindings'.

You complete against a list of keys + command pairs presented in
a similar way as `describe-bindings' does, split into sections
defined by the types of the key bindings (minor and major modes,
global bindings, etc).

The default action executes a command as if the binding had been
entered, or narrows the commands according to a prefix key,
respectively.

The persistent action pops up a help buffer for the selected
command without quitting.

For key translation maps, the default actions are not very
useful, yet they are listed for completeness."
  (interactive)
  (let ((old-helm-full-frame helm-full-frame)
        (helm-full-frame (and (not (minibufferp))
                              (memq helm-descbinds-window-style
                                    '(same-window one-window))))
        (helm-before-initialize-hook (if (and (not (minibufferp))
                                              (eq helm-descbinds-window-style
                                                  'one-window))
                                         (cons 'delete-other-windows
                                               helm-before-initialize-hook)
                                       helm-before-initialize-hook))
        (enable-recursive-minibuffers t))
    (setq helm-descbind--initial-full-frame old-helm-full-frame)
    (helm :sources (helm-descbinds-sources
                    (or buffer (current-buffer)) prefix)
          :buffer "*helm-descbinds*"
          :resume 'noresume
          :allow-nest t)))

(provide 'helm-descbinds)

;;; helm-descbinds.el ends here
