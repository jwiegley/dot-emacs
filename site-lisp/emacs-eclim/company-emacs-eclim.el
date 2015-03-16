;; company-emacs-eclim.el --- an interface to the Eclipse IDE.
;;
;; Copyright (C) 2009-2012   Fredrik Appelberg
;; Copyright (C) 2013-2014   Dmitry Gutov
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;
;;; Description
;;
;; company-emacs-eclim.el -- company-mode backend that replaces company-eclim
;;
;; To activate this backend, replace company-eclim and/or company-nxml
;; with company-emacs-eclim in the eclim-backends list, or call the
;; convenience function company-emacs-eclim-setup.
;;
;; Minimum company-mode version required: 0.7.

;;* Eclim Company

(require 'eclim)
(require 'eclim-completion)
(require 'eclim-java)
(require 'company)

(defun company-emacs-eclim-setup ()
  "Convenience function that adds company-emacs-eclim to the list
  of available company backends."
  (setq company-backends
        (cons 'company-emacs-eclim
              (remove-if (lambda (b) (find b '(company-nxml company-eclim)))
                         company-backends))))

(defun company-emacs-eclim--candidates (prefix)
  (mapcar
   (lambda (str)
     (if (string-match "(" str)
         (propertize (substring str 0 (match-beginning 0)) 'eclim-meta str)
       str))
   (eclim--completion-candidates)))

(defun company-emacs-eclim--annotation (candidate)
  (let ((str (get-text-property 0 'eclim-meta candidate)))
    (when (and str (string-match "(" str))
      (substring str (match-beginning 0)))))

(defun company-emacs-eclim (command &optional arg &rest ignored)
  "`company-mode' back-end for Eclim completion"
  (interactive (list 'interactive))
  (case command
    (interactive (company-begin-backend 'company-emacs-eclim))
    (prefix (let ((start (eclim-completion-start)))
              (when start (buffer-substring-no-properties start (point)))))
    (candidates (company-emacs-eclim--candidates arg))
    (annotation (company-emacs-eclim--annotation arg))
    (meta (eclim--completion-documentation
           (concat arg (company-emacs-eclim--annotation arg))))
    (no-cache (equal arg ""))
    (ignore-case t)
    (sorted t)
    (post-completion (let ((ann (company-emacs-eclim--annotation arg)))
                       (when ann (insert ann))
                       (eclim--completion-action)))))

(provide 'company-emacs-eclim)
