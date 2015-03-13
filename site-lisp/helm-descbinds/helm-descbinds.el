;;; helm-descbinds.el --- Yet Another `describe-bindings' with `helm'.

;; Copyright (C) 2008, 2009, 2010  Taiki SUGAWARA <buzz.taiki@gmail.com>
;; Copyright (C) 2012, 2013  Michael Markert <markert.michael@googlemail.com>
;; Copyright (C) 2013 Daniel Hackney <dan@haxney.org>

;; Author: Taiki SUGAWARA <buzz.taiki@gmail.com>
;; Keywords: helm, help
;; Version: 1.08
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
;; This package is a replacement of `describe-bindings'.

;;; Usage:
;; Add followings on your .emacs.
;;
;;   (require 'helm-descbinds)
;;   (helm-descbinds-mode)
;;
;; or use customize to set `helm-descbinds-mode' to t.
;;
;; Now, `describe-bindings' is replaced to `helm-descbinds'. Type
;; `C-h b', `C-x C-h' these run `helm-descbinds'.
;;
;; In the Helm buffer, you can select key-binds with helm interface.
;;
;;  - When type RET, selected candidate command is executed.
;;
;;  - When type TAB, You can "Execute", "Describe Function" or "Find
;;    Function" by the menu.
;;
;;  - When type C-z, selected command is described without quiting.

;;; History:
;; 2013-02-23 Michael Markert <markert.michael@googlemail.com>
;;   * helm-descbinds.el: Version 1.08
;;   Merge Daniel Hackney's helm-descbinds minor mode.
;;   Several bugfixes.
;;
;; 2012-03-18 Michael Markert <markert.michael@googlemail.com>
;;   * helm-descbinds.el: Version 1.07
;;   make strings bound to keys insertable
;;
;; 2012-03-18 Michael Markert <markert.michael@googlemail.com>
;;   * helm-descbinds.el: Version 1.06
;;   port to helm
;;
;; 2010-02-05   Taiki SUGAWARA  <sugawara_t@ariel-networks.com>
;;
;;   * descbinds-anything.el: Version 1.05
;;   bug fix.
;;
;; 2010-02-02 UTC  Taiki SUGAWARA  <buzz.taiki@gmail.com>
;;
;;   * descbinds-anything.el: Version 1.04
;;   add sorting feature.
;;   separete sorce creation function.
;;   add persistent action.
;;
;; 2009-03-29 UTC  Taiki SUGAWARA  <buzz.taiki@gmail.com>
;;
;;   * descbinds-anything.el: Version 1.03
;;   fix typo.
;;
;; 2008-11-16 UTC  Taiki SUGAWARA  <buzz.taiki@gmail.com>
;;
;;   * descbinds-anything.el: Version 1.02
;;   bound `indent-tabs-mode` to t for nil environment.
;;
;; 2008-11-16 UTC  Taiki SUGAWARA  <buzz.taiki@gmail.com>
;;
;;   * descbinds-anything.el: fix infinitive-loop when binding-line
;;   has not tab.

;;; Code:

(require 'cl-lib)
(require 'helm)

(defgroup helm-descbinds nil
  "Yet Another `describe-bindings' with `helm'."
  :prefix "helm-descbinds-"
  :group 'helm)

(defcustom helm-descbinds-actions
  '(("Execute" . helm-descbinds-action:execute)
    ("Describe Function" . helm-descbinds-action:describe)
    ("Find Function" . helm-descbinds-action:find-func))
  "Actions of selected candidate."
  :type '(repeat
	  (cons
	   :tag "Action"
	   (string :tag "Name")
	   (function :tag "Function")))
  :group 'helm-descbinds)

(defcustom helm-descbinds-strings-to-ignore
  '("Keyboard Macro" "Prefix Command")
  "Strings to ignore as a possible string candidate."
  :type '(repeat string))

(defcustom helm-descbinds-candidate-formatter
  'helm-descbinds-default-candidate-formatter
  "Candidate formatter function.
This function called two argument KEY and BINDING."
  :type 'function
  :group 'helm-descbinds)

(defcustom helm-descbinds-window-style 'one-window
  "Window splitting style."
  :type '(choice
	  (const :tag "One Window" one-window)
	  (const :tag "Same Window" same-window)
	  (const :tag "Split Window" split-window))
  :group 'helm-descbinds)

(defcustom helm-descbinds-section-order
  '("Major Mode Bindings" "Minor Mode Bindings" "Global Bindings")
  "A list of section order by name regexp."
  :type '(repeat (regexp :tag "Regexp"))
  :group 'helm-descbinds)

(defcustom helm-descbinds-source-template
  `((candidate-transformer . helm-descbinds-transform-candidates)
    (persistent-action . helm-descbinds-action:describe)
    (action . ,helm-descbinds-actions))
  "A template of `helm-descbinds' source."
  :type 'sexp
  :group 'helm-descbinds)

(defvar helm-descbinds-Orig-describe-bindings (symbol-function 'describe-bindings))
(defvar helm-descbind--initial-full-frame helm-full-frame)

;;;###autoload
(define-minor-mode helm-descbinds-mode
  "Use `helm' for `describe-bindings'"
  :group 'helm-descbinds
  :global t
  (if helm-descbinds-mode
      (fset 'describe-bindings #'helm-descbinds)
    (fset 'describe-bindings helm-descbinds-Orig-describe-bindings)))

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
     ((stringp x)
      (insert x))
     ((commandp x)
      (call-interactively x)))))

(defun helm-descbinds-action:describe (candidate)
  "An action that describe selected CANDIDATE function."
  (describe-function (cdr candidate)))

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
  (mapcar
   (lambda (pair)
     (let ((key (car pair))
           (command (cdr pair)))
       (cons (funcall helm-descbinds-candidate-formatter key command)
             (cons key (or (intern-soft command)
                           (unless (member command helm-descbinds-strings-to-ignore)
                             command))))))
   candidates))

(defun helm-descbinds-sources (buffer &optional prefix menus)
  (mapcar
   (lambda (section)
     (helm-descbinds-source (car section) (cdr section)))
   (sort
    (helm-descbinds-all-sections buffer prefix menus)
    (lambda (a b)
      (< (helm-descbinds-order-section a)
         (helm-descbinds-order-section b))))))

(defun helm-descbinds-source (name candidates)
  `((name . ,name)
    (candidates . ,candidates)
    ,@helm-descbinds-source-template))

;;;###autoload
(defun helm-descbinds (&optional prefix buffer)
  "Yet Another `describe-bindings' with `helm'."
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
                                         helm-before-initialize-hook)))
    (setq helm-descbind--initial-full-frame old-helm-full-frame)
    (helm :sources (helm-descbinds-sources
                    (or buffer (current-buffer)) prefix))))

(provide 'helm-descbinds)

;;; helm-descbinds.el ends here
