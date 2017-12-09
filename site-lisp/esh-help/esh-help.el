;;; esh-help.el --- Add some help functions and support for Eshell

;; Copyright (C) 2013, 2014 by Tomoya Tanjo

;; Author: Tomoya Tanjo <ttanjo@gmail.com>
;; URL: https://github.com/tom-tan/esh-help/
;; Package-Requires: ((dash "1.4.0"))
;; Keywords: eshell, extensions

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

;; This library adds the following help functions and support for Eshell:
;; - run-help function inspired by Zsh
;; - eldoc support
;;
;; To use this package, add these lines to your .emacs file:
;;     (require 'esh-help)
;;     (setup-esh-help-eldoc)  ;; To use eldoc in Eshell
;; And by using M-x eldoc-mode in Eshell, you can see help strings
;; for the pointed command in minibuffer.
;; And by using M-x esh-help-run-help, you can see full help string
;; for the command.

;;; Code:

(require 'esh-cmd)
(require 'esh-mode)
(require 'em-unix)
(require 'esh-ext)
(require 'eldoc)
(require 'env)
(require 'dash)
(require 'man)

;;;###autoload
(defun setup-esh-help-eldoc ()
  "Setup eldoc function for Eshell."
  (interactive)
  (add-hook 'eshell-mode-hook
            (lambda ()
              (make-local-variable 'eldoc-documentation-function)
              (setq eldoc-documentation-function
                    'esh-help-eldoc-command))))

;;;###autoload
(defun esh-help-run-help (cmd)
  "Show help for the pointed command or functions CMD.
It comes from Zsh."
  (interactive
   (list (esh-help-pointed-symbol)))
  (cond
    ((eshell-find-alias-function cmd)
     (describe-function (eshell-find-alias-function cmd)))
    ((string-match-p "^\\*." cmd)
     (man (substring cmd 1)))
    ((eshell-search-path cmd) (man cmd))
    ((functionp (intern cmd)) (describe-function (intern cmd)))))

(defun esh-help-pointed-symbol ()
  "Return the symbol to show the help string."
  (let ((bol (save-excursion
               (eshell-bol)
               (point)))
        (eol (save-excursion
               (move-end-of-line nil)
               (point))))
    (when (<= bol (point))
      (save-excursion
        (--if-let (re-search-backward "|" bol t)
          (forward-char)
          (eshell-bol))
        (--when-let (re-search-forward "[^\s]+" eol t)
          (goto-char it)
          (current-word))))))

(defalias 'esh-help--get-fnsym-args-string
    (if (fboundp 'eldoc-get-fnsym-args-string)
        #'eldoc-get-fnsym-args-string
      #'elisp-get-fnsym-args-string)
  "eldoc-get-fnsym-args-string is no longer defined in Emacs 25")

(defun esh-help-eldoc-help-string (cmd)
  "Return minibuffer help string for CMD."
  (cond
    ((string-match-p "^[/.]" cmd) nil)
    ((eshell-find-alias-function cmd)
     (esh-help--get-fnsym-args-string (eshell-find-alias-function cmd)))
    ((string-match-p "^\\*." cmd)
     (esh-help-eldoc-man-minibuffer-string (substring cmd 1)))
    ((eshell-search-path cmd) (esh-help-eldoc-man-minibuffer-string cmd))
    ((functionp (intern cmd)) (esh-help--get-fnsym-args-string (intern cmd)))))

(defun esh-help-man-string (cmd)
  "Return help string for the shell command CMD."
  (let ((lang (getenv "LANG")))
    (setenv "LANG" "C")
    (let ((str (shell-command-to-string (format "%s %s | col -b"
                                                manual-program cmd))))
      (setenv "LANG" lang)
      str)))

(defun esh-help-eldoc-man-minibuffer-string (cmd)
  "Return minibuffer help string for the shell command CMD."
  (let ((str (split-string (esh-help-man-string cmd) "\n")))
    (unless (equal (concat "No manual entry for " cmd)
                   (car str))
      (->> str
        (--drop-while (not (string-match-p "^SYNOPSIS$" it)))
        (nth 1)
        (funcall (lambda (s)
                   (let ((idx (string-match "[^\s\t]" s)))
                     (substring s idx))))))))

(defun esh-help-eldoc-command ()
  "Return eldoc string for the pointed symbol."
  (--when-let (esh-help-pointed-symbol)
    (esh-help-eldoc-help-string it)))

(provide 'esh-help)
;;; esh-help.el ends here
