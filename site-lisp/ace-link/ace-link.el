;;; ace-link.el --- Quickly follow links

;; Copyright (C) 2014-2017 Oleh Krehel

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/ace-link
;; Version: 0.5.0
;; Package-Requires: ((avy "0.4.0"))
;; Keywords: convenience, links, avy

;; This file is not part of GNU Emacs

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; This package offers an alternative to tabbing through links in
;; buffers, for instance, in an Info buffer.  `avy' is used to turn
;; opening a link from an O(N) operation into an O(1).
;;
;; Use `ace-link-setup-default' to set up the default bindings, which currently
;; bind e.g. `ace-link-info' to "o", which was previously unbound and is
;; close to "l" (which by default goes back).
;;
;; Supported modes: `Info-mode', `help-mode', `org-mode', `eww-mode',
;; `gnus-article-mode', `Custom-mode', `woman-mode', `goto-address-mode'.

;;; Code:
(require 'avy)

;;* `ace-link'
(defvar ace-link-fallback-function nil
  "When non-nil, called by `ace-link' when `major-mode' isn't recognized.")

;;;###autoload
(defun ace-link ()
  "Call the ace link function for the current `major-mode'"
  (interactive)
  (cond ((eq major-mode 'Info-mode)
         (ace-link-info))
        ((member major-mode '(help-mode package-menu-mode geiser-doc-mode))
         (ace-link-help))
        ((eq major-mode 'woman-mode)
         (ace-link-woman))
        ((eq major-mode 'eww-mode)
         (ace-link-eww))
        ((or (member major-mode '(compilation-mode grep-mode))
             (bound-and-true-p compilation-shell-minor-mode))
         (ace-link-compilation))
        ((eq major-mode 'gnus-article-mode)
         (ace-link-gnus))
        ((eq major-mode 'org-mode)
         (ace-link-org))
        ((eq major-mode 'org-agenda-mode)
         (ace-link-org-agenda))
        ((eq major-mode 'Custom-mode)
         (ace-link-org))
        ((and ace-link-fallback-function
              (funcall ace-link-fallback-function)))
        (t
         (error
          "%S isn't supported"
          major-mode))))

;;* `ace-link-info'
;;;###autoload
(defun ace-link-info ()
  "Open a visible link in an `Info-mode' buffer."
  (interactive)
  (let ((pt (avy-with ace-link-info
              (avy--process
               (mapcar #'cdr
                       (ace-link--info-collect))
               (avy--style-fn avy-style)))))
    (ace-link--info-action pt)))

(defun ace-link--info-action (pt)
  (when (numberp pt)
    (push-mark)
    (goto-char pt)
    (let ((we (window-end)))
      (while (not (ignore-errors
                    (Info-follow-nearest-node)))
        (forward-char 1)
        (when (> (point) we)
          (error "Could not follow link"))))))

(declare-function Info-follow-nearest-node "info")
(declare-function Info-next-reference "info")
(declare-function Info-try-follow-nearest-node "info")
(declare-function Info-goto-node "info")

(defun ace-link--info-current ()
  "Return the node at point."
  (cons (cl-letf (((symbol-function #'Info-goto-node)
                   (lambda (node _) node))
                  (browse-url-browser-function
                   (lambda (url &rest _) url)))
          (Info-try-follow-nearest-node))
        (point)))

(defun ace-link--info-collect ()
  "Collect the positions of visible links in the current `Info-mode' buffer."
  (let ((end (window-end))
        points)
    (save-excursion
      (goto-char (window-start))
      (when (ignore-errors (Info-next-reference) t)
        (push (ace-link--info-current) points)
        (Info-next-reference)
        (while (and (< (point) end)
                    (> (point) (cdar points)))
          (push (ace-link--info-current) points)
          (Info-next-reference))
        (nreverse points)))))

;;* `ace-link-help'
;;;###autoload
(defun ace-link-help ()
  "Open a visible link in a `help-mode' buffer."
  (interactive)
  (let ((pt (avy-with ace-link-help
              (avy--process
               (mapcar #'cdr (ace-link--help-collect))
               (avy--style-fn avy-style)))))
    (ace-link--help-action pt)))

(defun ace-link--help-action (pt)
  (when (numberp pt)
    (goto-char (1+ pt))
    (push-button)))

(defun ace-link--help-collect ()
  "Collect the positions of visible links in the current `help-mode' buffer."
  (let ((skip (text-property-any
               (window-start) (window-end) 'button nil))
        candidates)
    (save-excursion
      (while (setq skip (text-property-not-all
                         skip (window-end) 'button nil))
        (goto-char skip)
        (push (cons (button-label (button-at skip)) skip) candidates)
        (setq skip (text-property-any (point) (window-end)
                                      'button nil))))
    (nreverse candidates)))

;;* `ace-link-woman'
;;;###autoload
(defun ace-link-woman ()
  "Open a visible link in a `woman-mode' buffer."
  (interactive)
  (let ((pt (avy-with ace-link-woman
              (avy--process
               (mapcar #'cdr (ace-link--woman-collect))
               (avy--style-fn avy-style)))))
    (ace-link--woman-action pt)))

(defun ace-link--woman-action (pt)
  (when (number-or-marker-p pt)
    (goto-char (1+ pt))
    (push-button)))

(defun ace-link--woman-collect ()
  "Collect all links visible in the current `woman-mode' buffer."
  (let ((end (window-end))
        candidates)
    (save-excursion
      (goto-char (window-start))
      (while (and (condition-case nil (forward-button 1)
                    (error nil))
                  (< (point) end))
        (push (cons (button-label (button-at (point))) (point))
              candidates))
      (nreverse candidates))))

;;* `ace-link-eww'
;;;###autoload
(defun ace-link-eww ()
  "Open a visible link in an `eww-mode' buffer."
  (interactive)
  (let ((pt (avy-with ace-link-eww
              (avy--process
               (mapcar #'cdr (ace-link--eww-collect))
               (avy--style-fn avy-style)))))
    (ace-link--eww-action pt)))

(declare-function eww-follow-link "eww")

(defun ace-link--eww-action (pt)
  (when (number-or-marker-p pt)
    (goto-char (1+ pt))
    (eww-follow-link)))

(defun ace-link--eww-collect ()
  "Collect the positions of visible links in the current `eww' buffer."
  (save-excursion
    (save-restriction
      (narrow-to-region
       (window-start)
       (window-end))
      (goto-char (point-min))
      (let (beg end candidates)
        (setq end
              (if (get-text-property (point) 'help-echo)
                  (point)
                (text-property-any
                 (point) (point-max) 'help-echo nil)))
        (while (setq beg (text-property-not-all
                          end (point-max) 'help-echo nil))
          (goto-char beg)
          (setq end (text-property-any
                     (point) (point-max) 'help-echo nil))
          (push (cons (buffer-substring-no-properties beg end) beg)
                candidates))
        (nreverse candidates)))))

;;* `ace-link-compilation'
;;;###autoload
(defun ace-link-compilation ()
  "Open a visible link in a `compilation-mode' buffer."
  (interactive)
  (let ((pt (avy-with ace-link-compilation
              (avy--process
               (mapcar #'cdr (ace-link--eww-collect))
               (avy--style-fn avy-style)))))
    (ace-link--compilation-action pt)))

(defun ace-link--compilation-action (pt)
  (when (number-or-marker-p pt)
    (goto-char (1+ pt))
    (compile-goto-error)))

(declare-function compile-goto-error "compile")

;;* `ace-link-gnus'
;;;###autoload
(defun ace-link-gnus ()
  "Open a visible link in a `gnus-article-mode' buffer."
  (interactive)
  (when (eq major-mode 'gnus-summary-mode)
    (gnus-summary-widget-forward 1))
  (let ((pt (avy-with ace-link-gnus
              (avy--process
               (ace-link--gnus-collect)
               (avy--style-fn avy-style)))))
    (ace-link--gnus-action pt)))

(defun ace-link--gnus-action (pt)
  (when (number-or-marker-p pt)
    (goto-char (1+ pt))
    (widget-button-press (point))))

(declare-function widget-forward "wid-edit")
(declare-function gnus-summary-widget-forward "gnus-sum")
(declare-function widget-button-press "wid-edit")

(defun ace-link--gnus-collect ()
  "Collect the positions of visible links in the current gnus buffer."
  (require 'wid-edit)
  (let (candidates pt)
    (save-excursion
      (save-restriction
        (narrow-to-region
         (window-start)
         (window-end))
        (goto-char (point-min))
        (setq pt (point))
        (while (progn (widget-forward 1)
                      (> (point) pt))
          (setq pt (point))
          (when (or (plist-get (text-properties-at (point)) 'gnus-string)
                    (plist-get (text-properties-at (point)) 'shr-url))
            (push (point) candidates)))
        (nreverse candidates)))))

;;* `ace-link-mu4e'
;;;###autoload
(defun ace-link-mu4e ()
  "Open a visible link in an `mu4e-view-mode' buffer."
  (interactive)
  (let ((pt (avy-with ace-link-mu4e
              (avy--process
               (mapcar #'cdr (ace-link--mu4e-collect))
               (avy--style-fn avy-style)))))
    (ace-link--mu4e-action pt)))

(declare-function shr-browse-url "shr")
(declare-function mu4e~view-browse-url-from-binding "ext:mu4e-view")
(declare-function mu4e~view-open-attach-from-binding "ext:mu4e-view")

(defun ace-link--mu4e-action (pt)
  (when (number-or-marker-p pt)
    (goto-char (1+ pt))
    (cond ((get-text-property (point) 'shr-url)
           (shr-browse-url))
          ((get-text-property (point) 'mu4e-url)
           (mu4e~view-browse-url-from-binding))
          ((get-text-property (point) 'mu4e-attnum)
           (mu4e~view-open-attach-from-binding)))))

(defun ace-link--mu4e-next-link (pos)
  (let* ((shr-link-pos (text-property-not-all pos (point-max) 'shr-url nil))
         (mu4e-link-pos (text-property-not-all pos (point-max) 'mu4e-url nil))
         (mu4e-att-link-pos (text-property-not-all pos (point-max) 'mu4e-attnum nil))
         (links (seq-filter
                 (lambda (link)
                   (elt link 1))
                 (list
                  (list 'shr-url shr-link-pos)
                  (list 'mu4e-url mu4e-link-pos)
                  (list 'mu4e-attnum mu4e-att-link-pos)))))

    (if links
        (car
         (sort links (lambda (x y)
                       (< (elt x 1) (elt y 1)))))
      nil)))

(defun ace-link--mu4e-end-of-link (link)
  (or (text-property-any (elt link 1) (point-max) (elt link 0) nil)
      (point-max)))

(defun ace-link--mu4e-collect ()
  "Collect the positions of visible links in the current mu4e buffer."
  (save-excursion
    (save-restriction
      (narrow-to-region
       (window-start)
       (window-end))
      (goto-char (point-min))
      (let (link pos candidates)
        (setq pos (point))
        (while (setq link (ace-link--mu4e-next-link pos))
          (goto-char (elt link 1))
          (setq pos (ace-link--mu4e-end-of-link link))
          (push (cons (buffer-substring-no-properties (elt link 1) pos) (elt link 1)) candidates))
        (nreverse candidates)))))

;;* `ace-link-org'
;;;###autoload
(defun ace-link-org ()
  "Open a visible link in an `org-mode' buffer."
  (interactive)
  (require 'org)
  (let ((pt (avy-with ace-link-org
               (avy--process
                (mapcar #'cdr (ace-link--org-collect))
                (avy--style-fn avy-style)))))
    (ace-link--org-action pt)))

(declare-function org-open-at-point "org")
(declare-function outline-invisible-p "outline")
(defvar org-any-link-re)

(defun ace-link--org-action (pt)
  (when (numberp pt)
    (goto-char pt)
    (org-open-at-point)))

(defun ace-link--org-collect ()
  (let ((end (window-end))
        res)
    (save-excursion
      (goto-char (window-start))
      (while (re-search-forward org-any-link-re end t)
        ;; Check that the link is visible. Look at the last character
        ;; position in the link ("...X]]") to cover links with and
        ;; without a description.
        (when (not (outline-invisible-p (- (match-end 0) 3)))
          (push
           (cons
            (buffer-substring-no-properties
             (match-beginning 0)
             (match-end 0))
            (match-beginning 0))
           res)))
      (nreverse res))))

;;* `ace-link-org-agenda'
;;;###autoload
(defun ace-link-org-agenda ()
  "Open a visible link in an `org-mode-agenda' buffer."
  (interactive)
  (require 'org-agenda)
  (let ((pt (avy-with ace-link-org-agenda
              (avy--process
               (mapcar #'cdr (ace-link--org-agenda-collect))
               (avy--style-fn avy-style)))))
    (ace-link--org-agenda-action pt)))

(declare-function org-agenda-goto "org-agenda")

(defun ace-link--org-agenda-action (pt)
  (when (numberp pt)
    (goto-char pt)
    (org-agenda-goto)))

(defun ace-link--org-agenda-collect ()
  (let ((skip (text-property-any
               (window-start) (window-end) 'org-marker nil))
        candidates)
    (save-excursion
      (while (setq skip (text-property-not-all
                         skip (window-end) 'org-marker nil))
        (goto-char skip)
        (push (cons (get-char-property (point) 'txt) skip) candidates)
        (setq skip (text-property-any (point) (window-end)
                                      'org-marker nil))))
    (nreverse candidates)))

;;* `ace-link-custom'
;;;###autoload
(defun ace-link-custom ()
  "Open a visible link in an `Custom-mode' buffer."
  (interactive)
  (let ((pt (avy-with ace-link-custom
              (avy--process
               (ace-link--custom-collect)
               (avy--style-fn avy-style)))))
    (ace-link--custom-action pt)))

(declare-function Custom-newline "cus-edit")

(defun ace-link--custom-action (pt)
  (when (number-or-marker-p pt)
    (goto-char pt)
    (Custom-newline (point))))

(defun ace-link--custom-collect ()
  "Collect the positions of visible links in the current `Custom-mode' buffer."
  (let (candidates pt)
    (save-excursion
      (save-restriction
        (narrow-to-region
         (window-start)
         (window-end))
        (goto-char (point-min))
        (setq pt (point))
        (while (progn (widget-forward 1)
                      (> (point) pt))
          (setq pt (point))
          (when (get-char-property (point) 'button)
            (push (point) candidates)))))
    (nreverse candidates)))

;;* `ace-link-addr'
;;;###autoload
(defun ace-link-addr ()
  "Open a visible link in a goto-address buffer."
  (interactive)
  (let ((pt (avy-with ace-link-addr
               (avy--process
                (ace-link--addr-collect)
                (avy--style-fn avy-style)))))
    (ace-link--addr-action pt)))

(defun ace-link--addr-action (pt)
  (when (number-or-marker-p pt)
    (goto-char (1+ pt))
    (goto-address-at-point)))

(defun ace-link--addr-collect ()
  (let (candidates)
    (dolist (overlay (overlays-in (window-start) (window-end)))
      (if (overlay-get overlay 'goto-address)
          (push (overlay-start overlay) candidates)))
    (nreverse candidates)))

;;* Bindings
(defvar eww-link-keymap)
(defvar eww-mode-map)
(defvar custom-mode-map)

;;;###autoload
(defun ace-link-setup-default (&optional key)
  "Bind KEY to appropriate functions in appropriate keymaps."
  (setq key (or key "o"))
  (add-to-list 'avy-styles-alist
               '(ace-link-info . at))
  (add-to-list 'avy-styles-alist
               '(ace-link-help . post))
  (add-to-list 'avy-styles-alist
               '(ace-link-woman . post))
  (add-to-list 'avy-styles-alist
               '(ace-link-eww . post))
  (add-to-list 'avy-styles-alist
               '(ace-link-compilation . post))
  (add-to-list 'avy-styles-alist
               '(ace-link-gnus . post))
  (add-to-list 'avy-styles-alist
               '(ace-link-mu4e . post))
  (add-to-list 'avy-styles-alist
               '(ace-link-org . pre))
  (add-to-list 'avy-styles-alist
               '(ace-link-org-agenda . pre))
  (add-to-list 'avy-styles-alist
               '(ace-link-custom . pre))
  (add-to-list 'avy-styles-alist
               '(ace-link-addr . pre))
  (eval-after-load "info"
    `(define-key Info-mode-map ,key 'ace-link-info))
  (eval-after-load "compile"
    `(define-key compilation-mode-map ,key 'ace-link-compilation))
  (eval-after-load "help-mode"
    `(define-key help-mode-map ,key 'ace-link-help))
  (eval-after-load "woman"
    `(define-key woman-mode-map ,key 'ace-link-woman))
  (eval-after-load "eww"
    `(progn
       (define-key eww-link-keymap ,key 'ace-link-eww)
       (define-key eww-mode-map ,key 'ace-link-eww)))
  (eval-after-load 'cus-edit
    `(progn
       (define-key custom-mode-map ,key 'ace-link-custom)))
  (eval-after-load "helpful"
    `(progn
       (define-key helpful-mode-map ,key 'ace-link-help))))

(provide 'ace-link)

;;; ace-link.el ends here
