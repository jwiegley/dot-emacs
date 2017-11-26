;;; helm-navi.el --- Helm for navi-mode -*- lexical-binding: t -*-

;; Author: Adam Porter <adam@alphapapa.net>
;; Url: http://github.com/emacs-helm/helm-navi
;; Version: 0.1-pre
;; Package-Requires: ((emacs "24.4") (helm "1.9.4") (navi-mode "2.0") (s "1.10.0"))
;; Keywords: navigation, outlines

;; Copyright (C) 2012 ~ 2017 Thierry Volpiatto <thierry.volpiatto@gmail.com>

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

;; This file provides commands to navigate a buffer using keywords and
;; headings provided by `navi-mode' and `outshine'.

;; navi-mode <https://github.com/tj64/navi> is a package that lets you
;; quickly navigate and "remotely control" buffers.

;; Outshine <https://github.com/tj64/outshine> is a package that lets
;; you organize your non-org-mode buffers with commented Org headings
;; and other Org features, especially useful for any kind of source
;; code, or any file format which supports comments.

;; These packages are practically developed as as single package, and
;; `navi-mode' requires `outshine', so they are supported here in a
;; single `helm-navi' package.

;;; Code:

;;;; Requirements

(require 'cl-lib)
(require 'helm-org)
(require 's)
(require 'navi-mode)

;;;; Customization

(defgroup helm-navi nil
  "Settings for `helm-navi'."
  :group 'helm)

(defcustom helm-navi-fontify t
  "Fontify results according to their appearance in source buffers.
It's unlikely that you would want to disable this, but in case it
is ever a performance issue on slow machines, you can."
  :type 'boolean)

;;;; Functions

;;;;; Commands

;;;###autoload
(defalias 'helm-navi 'helm-navi-headings-and-keywords-current-buffer)

;;;###autoload
(defun helm-navi-headings-and-keywords-current-buffer ()
  "Show matches for all `navi-mode' keywords and `outshine' headings in current buffer."
  (interactive)
  (save-restriction
    (let ((helm-move-to-line-cycle-in-source t))
      (helm :buffer "*helm-navi-headings-and-keywords-current-buffer*"
            :sources (helm-source--navi-keywords-and-outshine-headings-in-buffer (current-buffer))
            :preselect (helm-navi--in-buffer-preselect)))))

;;;###autoload
(defalias 'helm-navi-headings 'helm-navi-headings-current-buffer)

;;;###autoload
(defun helm-navi-headings-current-buffer ()
  "Show matches for Outshine headings in current buffer."
  (interactive)
  (let ((helm-move-to-line-cycle-in-source t))
    (helm :buffer "*helm-navi-headings-current-buffer*"
          :sources (helm-source--outshine-headings-in-buffer (current-buffer))
          :preselect (helm-navi--current-or-previous-outshine-heading))))

;;;;; Helm sources

(defun helm-source--navi-keywords-and-outshine-headings-in-buffer (buffer)
  "Return Helm source for `navi-mode' keywords and `outshine' headings in BUFFER."
  (helm-build-sync-source (concat " " (buffer-name buffer))
    :candidates (helm-navi--get-candidates-in-buffer buffer #'helm-navi--get-regexp)
    :action '(("Go to heading" . helm-navi--goto-marker))
    :follow 1
    ;; FIXME: Calling `show-all' is not ideal,
    ;; because collapsed/hidden nodes will be shown
    ;; afterward, but I can't find a way to save this
    ;; information and restore it.  In Org buffers,
    ;; `org-show-entry' can be used, but I haven't
    ;; been able to find a similar function for
    ;; non-Org buffers.
    :init 'show-all))

(defun helm-source--outshine-headings-in-buffer (buffer)
  "Return helm-sync-source for Outshine headings in BUFFER."
  (helm-build-sync-source (concat " " (buffer-name buffer))
    :candidates (helm-navi--get-candidates-in-buffer buffer)
    :action '(("Go to heading" . helm-navi--goto-marker))
    :follow 1
    :init 'show-all))

;;;;; Support functions

(defun helm-navi--get-candidates-in-buffer (buffer &optional regexp)
  "Return Outshine heading candidates in BUFFER.
Optional argument REGEXP is a regular expression to match, a
function to return a regular expression, or
`outline-promotion-headings' by default."
  ;; Much of this code is copied from helm-org.el
  (with-current-buffer buffer
    ;; Make sure outshine is loaded
    (unless outline-promotion-headings
      (error "Outshine is not activated in buffer \"%s\".  Activate `outline-minor-mode', or consult Outshine's documentation for further instructions if necessary." (buffer-name buffer)))
    (let* ((heading-regexp (pcase regexp
                             ((pred functionp) (funcall regexp))
                             ((pred stringp) regexp)
                             ((pred null) (concat "^\\("
                                                  (mapconcat (lambda (s)
                                                               (s-trim (car s)))
                                                             outline-promotion-headings
                                                             "\\|")
                                                  "\\)"
                                                  "\s+\\(.*\\)$"))))
           (match-fn (if helm-navi-fontify
                         #'match-string
                       #'match-string-no-properties))
           (search-fn (lambda ()
                        (re-search-forward heading-regexp nil t))))
      (save-excursion
        (save-restriction
          (goto-char (point-min))
          (cl-loop while (funcall search-fn)
                   for beg = (point-at-bol)
                   for end = (point-at-eol)
                   when (and helm-navi-fontify
                             (null (text-property-any
                                    beg end 'fontified t)))
                   do (jit-lock-fontify-now beg end)
                   for level = (length (match-string-no-properties 1))
                   for heading = (if regexp
                                     (funcall match-fn 0)
                                   (concat (match-string 1) " " (funcall match-fn 2)))
                   if (or regexp
                          (and (>= level helm-org-headings-min-depth)
                               (<= level helm-org-headings-max-depth)))
                   collect `(,heading . ,(point-marker))))))))

(defun helm-navi--current-or-previous-outshine-heading ()
  "Return string containing current or previous visible heading in current buffer.
Typically for preselecting in Helm buffer."
  (if (outline-on-heading-p)
      (buffer-substring-no-properties (point-at-bol) (point-at-eol))
    (save-excursion
      (outline-previous-visible-heading 1)
      (buffer-substring-no-properties (point-at-bol) (point-at-eol)))))

(defun helm-navi--goto-marker (marker)
  "Switch to MARKER's buffer and go to it."
  (switch-to-buffer (marker-buffer marker))
  (goto-char (marker-position marker)))

(defun helm-navi--in-buffer-preselect ()
  "Return string containing symbol-at-point, or current/previous visible heading for preselecting in Helm buffer."
  (or (symbol-name (symbol-at-point))
      (save-excursion
        (goto-char (line-end-position))
        (when (re-search-backward (helm-navi--get-regexp))
          (match-string 0)))))

(defun helm-navi--get-regexp ()
  "Return regexp for all headings and keywords in current buffer."
  (concat (navi-make-regexp-alternatives
           (navi-get-regexp (car
                             (split-string
                              (symbol-name major-mode)
                              "-mode" 'OMIT-NULLS))
                            :ALL)
           (mapconcat (lambda (s)
                        (s-trim (car s)))
                      outline-promotion-headings
                      "\\|"))
          ".*$"))

;;;; Footer

(provide 'helm-navi)

;;; helm-navi.el ends here
