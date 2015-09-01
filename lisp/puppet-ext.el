;;; puppet-ext --- Extensions to puppet.el

;; Copyright (C) 2012 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 18 Jul 2012
;; Version: 1.0
;; Keywords: ruby puppet
;; X-URL: https://github.com/jwiegley/dot-emacs

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

;; Extensions to puppet.el.

(require 'align)
(require 'puppet-mode)

(eval-when-compile
  (require 'cl))

(defgroup puppet-ext nil
  "Extensions to puppet.el."
  :group 'puppet)

(add-to-list 'align-rules-list
             '(ruby-arrow
               (regexp   . "\\(\\s-*\\)=>\\(\\s-*\\)")
               (group    . (1 2))
               (modes    . '(ruby-mode puppet-mode))))

(defvar puppet-anchor-point nil)

(defun puppet-set-anchor ()
  (interactive)
  (setq puppet-anchor-point (point-marker))
  (message "puppet-mode anchor set at %s"
           (marker-position puppet-anchor-point)))

(defun puppet-resource-beginning ()
  (save-excursion
    (and (re-search-backward
          "^\\s-*\\(\\S-+\\)\\s-+{\\s-+\\([^:]+\\):" nil t)
         (list (match-beginning 0)
               (match-string 1) (match-string 2)))))

(defun puppet-resource-end ()
  (save-excursion
    (and (re-search-forward "^\\s-*}" nil t)
         (match-end 0))))

(defun puppet-create-require ()
  (interactive)
  (require 'align)
  (if (null puppet-anchor-point)
      (error "Anchor point has not been set")
    (destructuring-bind (anchored-start resource name)
        (save-excursion
          (goto-char puppet-anchor-point)
          (puppet-resource-beginning))
      (save-excursion
        (let ((beginning (car (puppet-resource-beginning)))
              (end (puppet-resource-end)))
          (goto-char end)
          (backward-char)
          (let ((current-requires
                 (when (re-search-backward
                        "^\\s-*require\\s-*=>\\s-*" beginning t)
                   (let ((start (match-beginning 0))
                         (beg (match-end 0)))
                     (if (looking-at "\\[")
                         (forward-sexp))
                     (re-search-forward "\\([,;]\\)?[ \t]*\n")
                     (prog1
                         (buffer-substring-no-properties
                          beg (match-beginning 0))
                       (delete-region start (point)))))))
            (save-excursion
              (skip-chars-backward " \t\n\r")
              (when (looking-back ";")
                (delete-char -1)
                (insert ?,)))
            (insert "  require => ")
            (if current-requires
                (insert "[ " current-requires ", "))
            (insert (capitalize (substring resource 0 1))
                    (substring resource 1) "[" name "]")
            (if current-requires
                (insert " ]"))
            (insert ";\n")
            (mark-paragraph)
            (align-code (region-beginning) (region-end))))))))

(define-key puppet-mode-map [(control ?x) ? ] 'puppet-set-anchor)
(define-key puppet-mode-map [(control ?x) space] 'puppet-set-anchor)

(define-key puppet-mode-map [(control ?c) (control ?r)] 'puppet-create-require)

(provide 'puppet-ext)

;;; puppet-ext.el ends here
