;;; python-mode-write-menu.el --- write menu

;; Copyright (C) 2015  Andreas Röhler

;; Author: Andreas Röhler <andreas.roehler@easy-emacs.de>

;; Keywords: lisp

;; This program is free software; you can redistribute it and/or modify
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

;;

;;; Code:

(defun py--kurzmenu-insert-intern (ele)
  (save-excursion (py--emen ele))
  (let ((orig (point)))
    (forward-list 1)
    (indent-region orig (point))
    (newline)))

(defun py--kurzmenu-insert (liste &optional prefix suffix exclude)
  (dolist (ele liste)
    (unless (stringp ele) (setq ele (prin1-to-string ele)))
    ;; Can't shift left top-level
    (unless (string= exclude ele)
      (when (string= "top-level" ele)
	(message "%s" exclude))
      (when prefix (setq ele (concat prefix ele)))
      (when suffix (setq ele (concat ele suffix)))
      (insert (concat "\n" (make-string 10 ? )))
      (py--kurzmenu-insert-intern ele))))

(defun kurzmenu ()
  (interactive)
  (with-current-buffer (get-buffer-create "py-menu-init.el")
    (erase-buffer)
    (insert "(and (ignore-errors (require 'easymenu) t)
     ;; (easy-menu-define py-menu map \"Python Tools\"
     ;;           `(\"PyTools\"
     (easy-menu-define
       py-menu python-mode-map \"Python Mode menu\"
       `(\"Python\"
	 (\"Interpreter\"")
    (emacs-lisp-mode)
    (switch-to-buffer (current-buffer))
    ;; (py--kurzmenu-insert py-checks-symbols)

    ;; (py--kurzmenu-insert (list 'import-or-reload) "py-execute-")
    (py--kurzmenu-insert py-shells)
    (insert (concat (make-string 10 ? )")\n"))
    (insert (concat (make-string 9 ? )"(\"Edit\"\n"))

    (insert (concat (make-string 10 ? )"(\"Mark\""))
    (py--kurzmenu-insert py-positions-forms "py-mark-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Copy\""))
    (py--kurzmenu-insert py-positions-forms "py-copy-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Kill\""))
    (py--kurzmenu-insert py-positions-forms "py-kill-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Delete\""))
    (py--kurzmenu-insert py-positions-forms "py-delete-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Comment\""))
    (py--kurzmenu-insert py-comment-forms "py-comment-")

    ;; Edit end
    (insert (concat (make-string 11 ? ) "))\n"))

    (insert (concat (make-string 9 ? )"(\"Move\"\n"))

    (insert (concat (make-string 10 ? )"(\"Shift\"\n"))

    (insert (concat (make-string 11 ? )"(\"Shift right\""))
    (py--kurzmenu-insert py-shift-forms "py-shift-" "-right")
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 11 ? )"(\"Shift left\""))
    (py--kurzmenu-insert py-shift-forms "py-shift-" "-left" "top-level")
    (insert (concat (make-string 12 ? )"))\n"))

    (insert (concat (make-string 11 ? )"(\"Backward\""))
    (py--kurzmenu-insert py-move-forms "py-backward-")
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 11 ? )"(\"Forward\""))
    (py--kurzmenu-insert py-navigate-forms "py-forward-")
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"BOL-forms\"\n"))

    (insert (concat (make-string 11 ? )"(\"Backward\""))
    (py--kurzmenu-insert py-navigate-forms "py-backward-" "-bol" "top-level")
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 11 ? )"(\"Forward\""))
    (py--kurzmenu-insert py-navigate-forms "py-forward-" "-bol")
    ;; BOL forms end
    (insert (concat (make-string 12 ? )"))\n"))

    (insert (concat (make-string 10 ? )"(\"Up/Down\""))
    (py--kurzmenu-insert (list 'up) "py-")
    (py--kurzmenu-insert (list 'down) "py-")

    ;; Move ends
    (insert (concat (make-string 11 ? )"))\n"))

    (insert (concat (make-string 9 ? )"(\"Send\""))
    (py--kurzmenu-insert py-execute-forms "py-execute-")

    (insert (concat (make-string 11 ? )"(\"Other\"\n"))
    (dolist (ele py-shells)
      (setq ele (prin1-to-string ele))
      ;; Shell forms
      (insert (concat (make-string 12 ? ))"(\"")
      (cond ((string-match "ipython" ele)
	     (insert (concat "IP" (substring ele 2))))
	    (t (insert (capitalize ele))))
      (insert "\"")
      (setq ele (concat "-" ele))
      (py--kurzmenu-insert py-execute-forms "py-execute-" ele)
      (insert (concat (make-string 13 ? )")\n")))
    (insert (make-string 12 ? ))
    (insert "(\"Ignoring defaults \"\n")
    (insert (concat (make-string 13 ? )":help \"`M-x py-execute-statement- TAB' for example list commands ignoring defaults\n\n of `py-switch-buffers-on-execute-p' and `py-split-window-on-execute'\"\n"))
    (insert (concat (make-string 13 ? ) ")))\n"))

    (insert (concat (make-string 9 ? )"(\"Hide-Show\"\n"))

    (insert (concat (make-string 10 ? )"(\"Hide\""))
    (py--kurzmenu-insert py-hide-names "py-hide-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Show\""))
    (py--kurzmenu-insert py-hide-names "py-show-")

    ;; Hide-show ends
    (insert (concat (make-string 11 ? )"))\n"))

    (insert (concat (make-string 9 ? )"(\"Fast process\""))
    (py--kurzmenu-insert py-fast-core "py-execute-")
    (insert (concat (make-string 10 ? )")\n"))

    (insert (concat (make-string 9 ? )"(\"Virtualenv\""))
    (py--kurzmenu-insert py-virtualenv-symbols "virtualenv-")
    (insert (concat (make-string 10 ? )")\n"))

    (py--kurzmenu-insert (list 'import-or-reload) "py-execute-")
    (insert (concat (make-string 9 ? )"(\"Help\""))
    (py--kurzmenu-insert py-help-symbols)
    (insert (concat (make-string 10 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Debugger\""))
    (py--kurzmenu-insert py-debugger-symbols)
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Checks\""))
    (py--kurzmenu-insert py-checks-symbols)

    (insert (concat (make-string 10 ? )"(\"Pylint\""))
    (py--kurzmenu-insert py-pylint-symbols)
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Pep8\""))
    (py--kurzmenu-insert py-pep8-symbols)
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Pyflakes\""))
    (py--kurzmenu-insert py-pyflakes-symbols)
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Flake8\""))
    (py--kurzmenu-insert py-flake8-symbols)

    (insert (concat (make-string 10 ? )"(\"Pyflakes-pep8\""))
    (py--kurzmenu-insert py-pyflakes-pep8-symbols)

    ;; close Pyflakes
    ;; close Checks
    (insert (concat (make-string 12 ? ) ")))\n"))
    (insert py-menu-custom-forms)
    (newline)
    (insert (concat (make-string 9 ? )"(\"Other\""))
    (py--kurzmenu-insert py-other-symbols "py-")

    (insert (concat (make-string 10 ? )"(\"Electric\""))
    (py--kurzmenu-insert py-electric-symbols "py-")
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Filling\""))
    (py--kurzmenu-insert py-filling-symbols "py-")
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Abbrevs\""))
    (insert py-menu-abbrev-form)
    (insert (concat (make-string 12 ? )")\n"))
    (py--kurzmenu-insert (list 'py-add-abbrev))

    (insert (concat (make-string 10 ? )"(\"Completion\""))
    (py--kurzmenu-insert py-completion-symbols "py-")
    (insert (concat (make-string 12 ? )")\n"))

    (py--kurzmenu-insert (list 'py-find-function))

    ;; nicht vorhanden
    ;; (insert (concat (make-string 10 ? )"(\"Skeletons\""))
    ;; (py--kurzmenu-insert py-skeletons)
    ;; (insert (concat (make-string 12 ? )")\n"))

    ;; Close Other
    (insert (concat (make-string 12 ? )")\n"))

    ;; final
    (insert (concat (make-string 12 ? ) ")))"))
    (write-file (expand-file-name "~/arbeit/emacs/python-modes/components-python-mode/devel/eame.el"))))

(defun write-menu-entry (&optional erg)
  "Menu Eintrag einfuegen. "
  (interactive "*")
  (let* ((orig (point))
         (erg (or erg (car kill-ring)))
         (name (intern-soft erg))
         (doku (documentation name))
         last)
      (insert (concat "\[\"" (replace-regexp-in-string "-" " " (replace-regexp-in-string "py-" "" erg)) "\" " erg "
 :help \" `" erg "'
"))
      (when doku (insert (regexp-quote doku)))

      (insert (concat
               ". \"]\n\n"))
      (setq last (point))
      (goto-char orig)
    (skip-chars-forward "[[:punct:]]")
    (capitalize-word 1)
    (goto-char last)))

(defun py-write-bol-menu ()
  (interactive)
  (set-buffer (get-buffer-create "bol-menu.el"))
  (erase-buffer)
  (dolist (ele py-down-forms)
    (insert (concat "(\" " (capitalize ele) " bol ... \"
             [\"Beginning of " ele " bol\" py-backward-" ele "-bol
              :help \"`py-backward-" ele "-bol'
Go to beginning of line at beginning of " ele ".

Returns position reached, if successful, nil otherwise. \"]\n"))

    (insert (concat "
             [\"End of " ele " bol\" py-forward-" ele "-bol
              :help \"`py-forward-" ele "-bol'
Go to beginning of line following end of " ele ".

Returns position reached, if successful, nil otherwise. \"]

             [\"Up " ele " bol\" py-up-" ele "-bol
              :help \"`py-up-" ele "-bol'
Go to next " ele " upwards in buffer if any. Go to beginning of line.

Returns position reached, if successful, nil otherwise. \"]

             [\"Down " ele " bol\" py-down-" ele "-bol
              :help \"`py-down-" ele "-bol'
Go to next " ele " downwards in buffer if any. Go to beginning of line.

Returns position reached, if successful, nil otherwise. \"]

             [\"Mark " ele " bol\" py-mark-" ele "-bol
              :help \"`py-mark-" ele "-bol'
Mark " ele " at point. \"]

             [\"Copy " ele " bol\" py-copy-" ele "-bol
              :help \"`py-copy-" ele "-bol'
Copy " ele " at point. \"]

             [\"Kill " ele " bol\" py-kill-" ele "-bol
              :help \"`py-kill-" ele "-bol'
Kill " ele " at point. \"]

             [\"Delete " ele " bol\" py-delete-" ele "-bol
              :help \"`py-delete-" ele "-bol'
Delete " ele " at point. \"]\n)\n"))))


(defun py-write-copy-bol-menu ()
  (interactive "*")
  (dolist (ele py-bol-copy-forms)
    (emen (prin1-to-string ele))
    (skip-chars-forward "^]")
    (forward-char 1)
    (newline)))

(defun py-write-bol-menu ()
  (interactive "*")
  (dolist (ele py-bol-menu-forms)
    (emen (prin1-to-string ele))
    (skip-chars-forward "^]")
    (forward-char 1)
    (newline)))

(defun py-write-bol-end-menu ()
  (interactive "*")
  (dolist (ele py-bol-end-forms)
    (emen (prin1-to-string ele))
    (skip-chars-forward "^]")
    (forward-char 1)
    (newline)))

(defun py-write-fast-menu ()
  (interactive "*")
  (dolist (ele py-fast-forms)
    (push-mark)
    (emen (prin1-to-string ele))
    (skip-chars-forward "^]")
    (forward-char 1)
    (newline)
    (indent-region (mark) (point))))


(defun py-write-hide-menu ()
  (interactive)
  (set-buffer (get-buffer-create "python-components-hide-Menu.el"))
  (erase-buffer)
  (switch-to-buffer (current-buffer))
  (emacs-lisp-mode)
  (insert "(\"Hide-Show\"")

  (dolist (ele py-hide-names)
    (emen (concat "py-hide-" ele))
    (goto-char (point-max))
    )
  (insert "(\"Show\"\n")

  (dolist (ele py-hide-names)
    (emen (concat "py-show-" ele))
    (goto-char (point-max))

    )

  (insert "))\n")

  (richten nil (point-min) (point-max))

  (switch-to-buffer (current-buffer))
  (emacs-lisp-mode))

(provide 'python-mode-write-menu)
;;; python-mode-write-menu.el ends here
