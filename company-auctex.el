;;; company-auctex.el --- Company-mode auto-completion for AUCTeX

;; Copyright (C) 2012 Christopher Monsanto, 2014 Alexey Romanov

;; Author: Christopher Monsanto <chris@monsan.to>, Alexey Romanov <alexey.v.romanov@gmail.com>
;; Version: 0.1
;; URL: https://github.com/alexeyr/company-auctex/
;; Package-Requires: ((yasnippet "0.8.0") (company "0.8.0") (auctex "11.87"))

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

;; To use:
;; (require 'company-auctex)
;; (company-auctex-init)
;; Feel free to contribute better documentation!

;;; Code:

(require 'tex)
(require 'latex)
(require 'company)
(require 'yasnippet)
(eval-when-compile (require 'cl-lib))

(defvar company-auctex-arg-lookup-table
  '((TeX-arg-define-macro . ("\\MacroName"))
    (TeX-arg-counter . ("Counter"))
    (TeX-arg-define-counter . ("\\CounterName"))
    (TeX-arg-file . ("Filename"))
    (TeX-arg-bibliography . ("Filename"))
    (TeX-arg-bibstyle . ("Style"))
    (TeX-arg-environment . ("Environment"))
    (TeX-arg-define-environment . ("EnvironmentName"))
    (TeX-arg-size . ("(w, h)"))
    (TeX-arg-ref . ("Name"))
    (TeX-arg-index . ("Index"))
    (TeX-arg-define-label . ("Label"))
    (LaTeX-arg-section . ("Title"))
    (LaTeX-arg-usepackage . (["opt1,..."] "Package"))
    (LaTeX-env-label . nil)
    (LaTeX-amsmath-env-aligned . (["htbp!"]))
    (LaTeX-amsmath-env-alignat . (["# Columns"]))
    (LaTeX-env-array . (["bct"] "lcrpmb|"))
    (LaTeX-env-item . nil)
    (LaTeX-env-document . nil)
    (LaTeX-env-figure . (["htbp!"]))
    (LaTeX-env-contents . ("Filename"))
    (LaTeX-env-minipage . (["htbp!"] "Width"))
    (LaTeX-env-list . ("Label" "\\itemsep,\\labelsep,..."))
    (LaTeX-env-picture . ("(w, h)" "(x, y)"))
    (LaTeX-env-tabular* . ("Width" ["htbp!"] "lcrpmb|><"))
    (LaTeX-env-bib . ("WidestLabel"))
    (TeX-arg-conditional . ([""]))
    (2 . ("" ""))
    (3 . ("" "" ""))
    (4 . ("" "" "" ""))
    (5 . ("" "" "" "" ""))
    (6 . ("" "" "" "" "" ""))
    (7 . ("" "" "" "" "" "" ""))
    (8 . ("" "" "" "" "" "" "" ""))
    (9 . ("" "" "" "" "" "" "" "" "")))
  "Anything not in this table defaults to '(\"\").")

(defgroup company-auctex nil
  "Completion backend for AUCTeX."
  :prefix "company-auctex-"
  :tag "Company AUCTeX"
  :group 'company)

(defun car-or (item)
  "Return car of ITEM if it's a cons, ITEM otherwise."
  (or (car-safe item) item))

(defun company-auctex-lookup-arg (item)
  (let ((arg (assoc (car-or item) company-auctex-arg-lookup-table)))
    (if arg (cdr arg) '(""))))

(defun company-auctex-expand-arg-info (arg-info)
  (cl-loop for item in arg-info
           append (cond
                   ((or (stringp item) (and (vectorp item) (stringp (elt item 0))))
                    (list item))
                   ((vectorp item)
                    (cl-loop for item-2 in (company-auctex-lookup-arg (elt item 0))
                             collect [item-2]))
                   (t
                    (company-auctex-lookup-arg item)))))

(defun company-auctex-snippet-arg (arg)
  (let* ((opt (vectorp arg))
         (item (if opt (elt arg 0) arg))
         (var (format "${%s}" item)))
    (if opt
        (concat "${[" var "]}")
      (concat "{" var "}"))))

(defun company-auctex-prefix (regexp)
  "Returns the prefix for matching given REGEXP."
  (let ((prefix (and (derived-mode-p 'latex-mode)
                     (when (looking-back regexp)
                       (match-string-no-properties 1)))))
    (if prefix (cons prefix t) nil)))


;; Macros
;;

(defun company-auctex--disable-yas ()
  (yas-minor-mode -1)
  (remove-hook 'yas-after-exit-snippet-hook #'company-auctex--disable-yas))

(defmacro company-auctex-with-yas (&rest body)
  `(progn
     (unless yas-minor-mode
       (yas-minor-mode +1)
       (add-hook 'yas-after-exit-snippet-hook #'company-auctex--disable-yas))
     ,@body))

(defun company-auctex-get-LaTeX-font-list (&optional mathp)
  (delq nil (mapcar
             (lambda (x)
               (and (stringp x)
                    (not (string= x ""))
                    (not (string= x "}"))
                    (list (substring x 1 -1) t)))
             (delete-dups
              (mapcar (if mathp
                          (lambda (x) (nth 3 x))
                        #'cadr)
                      LaTeX-font-list)))))

(defun company-auctex-macro-snippet (arg-info)
  (let ((count 1))
    (apply 'concat
           (cl-loop for item in (company-auctex-expand-arg-info arg-info)
                    collect (company-auctex-snippet-arg item)))))

(defun company-auctex-expand-args (str env)
  (company-auctex-with-yas
    (yas-expand-snippet (company-auctex-macro-snippet (assoc-default str env)))))

(defun company-auctex-macro-candidates (prefix)
  (let ((comlist (mapcar (lambda (item) (car-or (car item)))
                         (append (TeX-symbol-list)
                                 (LaTeX-length-list)
                                 LaTeX-section-list
                                 (company-auctex-get-LaTeX-font-list)))))
    (all-completions prefix comlist)))

(defun company-auctex-macro-post-completion (candidate)
  (company-auctex-expand-args candidate
                              (append (TeX-symbol-list)
                                      (mapcar (lambda (item)
                                                (list (car item) 'LaTeX-arg-section))
                                              LaTeX-section-list)
                                      (company-auctex-get-LaTeX-font-list))))

;;;###autoload
(defun company-auctex-macros (command &optional arg &rest ignored)
  "company-auctex-macros backend"
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-auctex-macros))
    (prefix (company-auctex-prefix "\\\\\\([a-zA-Z]*\\)\\="))
    (candidates (company-auctex-macro-candidates arg))
    (post-completion (company-auctex-macro-post-completion arg))))


;; Symbols
;;

(defun company-auctex-math-all ()
  (append LaTeX-math-list LaTeX-math-default))

(defun company-auctex-symbol-candidates (prefix)
  (all-completions prefix (append (mapcar 'cadr (company-auctex-math-all))
                                  (mapcar 'car (company-auctex-get-LaTeX-font-list t)))))

(defun company-auctex-symbol-post-completion (candidate)
  (search-backward candidate)
  (delete-region (1- (match-beginning 0)) (match-end 0))
  (if (texmathp)
      (insert "\\" candidate)
    (insert "$\\" candidate "$")
    (backward-char))
  (company-auctex-expand-args
   candidate
   (append (TeX-symbol-list) (company-auctex-get-LaTeX-font-list t))))

(defun company-auctex-symbol-annotation (candidate)
  (let ((char (nth 2 (assoc candidate (mapcar 'cdr (company-auctex-math-all))))))
    (and char (concat " " (char-to-string (decode-char 'ucs char))))))

;;;###autoload
(defun company-auctex-symbols (command &optional arg &rest ignored)
  "company-auctex-symbols backend"
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-auctex-symbols))
    (prefix (company-auctex-prefix "\\\\\\([a-zA-Z]*\\)\\="))
    (candidates (company-auctex-symbol-candidates arg))
    (post-completion (company-auctex-symbol-post-completion arg))
    (annotation (company-auctex-symbol-annotation arg))))


;; Environments
;;

(defcustom company-auctex-environment-prefix "beg"
  "Prefix for auto-completing environments.")

(defun company-auctex-environment-candidates (prefix)
  (let
      ((envlist
        (mapcar (lambda (item)
                  (concat company-auctex-environment-prefix (car item)))
                (LaTeX-environment-list))))
    (all-completions prefix envlist)))

(defun company-auctex-environment-post-completion (candidate)
  (search-backward candidate)
  (delete-region (1- (match-beginning 0)) (match-end 0))
  (let ((candidate
         (substring candidate (length company-auctex-environment-prefix))))
    (company-auctex-with-yas
      (yas-expand-snippet
       (format "\\begin{%s}%s\n$0\n\\end{%s}"
               candidate
               (company-auctex-macro-snippet
                (assoc-default candidate (LaTeX-environment-list)))
               candidate)))))

;;;###autoload
(defun company-auctex-environments (command &optional arg &rest ignored)
  "company-auctex-environments backend"
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-auctex-environments))
    (prefix (company-auctex-prefix "\\\\\\([a-zA-Z]*\\)\\="))
    (candidates (company-auctex-environment-candidates arg))
    (post-completion (company-auctex-environment-post-completion arg))))


;; Refs
;;

(defun company-auctex-label-candidates (prefix)
  (all-completions prefix (mapcar 'car (LaTeX-label-list))))

;;;###autoload
(defun company-auctex-labels (command &optional arg &rest ignored)
  "company-auctex-labels backend"
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-auctex-labels))
    (prefix (company-auctex-prefix "\\\\ref{\\([^}]*\\)\\="))
    (candidates (company-auctex-label-candidates arg))))


;; Bibs
;;

(defun company-auctex-bib-candidates (prefix)
  (all-completions prefix (mapcar 'car (LaTeX-bibitem-list))))

;;;###autoload
(defun company-auctex-bibs (command &optional arg &rest ignored)
  "company-auctex-bibs backend"
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-auctex-bibs))
    (prefix (company-auctex-prefix "\\\\cite[^[{]*\\(?:\\[[^]]*\\]\\)?{\\([^},]*\\)\\="))
    (candidates (company-auctex-bib-candidates arg))))


;; Merged backend
;;

;;;###autoload
(defun company-auctex-init ()
  "Add backends provided by company-auctex to company-backends."
  (add-to-list 'company-backends 'company-auctex-labels)
  (add-to-list 'company-backends 'company-auctex-bibs)
  (add-to-list 'company-backends
    '(company-auctex-macros company-auctex-symbols company-auctex-environments)))

(provide 'company-auctex)

;;; company-auctex.el ends here
