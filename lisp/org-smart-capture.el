;;; org-smart-capture --- Capture Gnus messages as tasks, with context

;; Copyright (C) 2011 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 16 Sep 2011
;; Version: 1.0
;; Keywords: gnus message org capture task todo context
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

;; I use: (define-key global-map [(meta ?m)] 'org-smart-capture)

(require 'gnus-sum)
(require 'org-macs)
(require 'org-capture)

(defgroup org-smart-capture nil
  "Capture Gnus messages as tasks, with context"
  :group 'org)

(defcustom org-smart-capture-use-lastname nil
  "If non-nil, include last names in smart captures."
  :type 'boolean
  :group 'org-smart-capture)

(defcustom org-subject-transforms nil
  "Transformations to apply to Subject lines after capture."
  :type '(alist :key-type regexp :value-type regexp)
  :group 'org-smart-capture)

(defcustom org-author-transforms nil
  "Transformations to apply to author names after capture."
  :type '(alist :key-type regexp :value-type regexp)
  :group 'org-smart-capture)

;; (defun convert-dates ()
;;   (interactive)
;;   (while (re-search-forward ":Date:\\s-*\\(.+?\\)$" nil t)
;;     (let ((date-sent (match-string 1)))
;;       (goto-char (match-beginning 1))
;;       (delete-region (match-beginning 1) (match-end 1))
;;       (insert ?\[ (org-encode-time
;;                    (parse-time-string date-sent))
;;               ?\]))))

(defun org-smart-capture-article (&optional article multiple)
  (let* ((body (and (eq major-mode 'gnus-article-mode)
                    (region-active-p)
                    (buffer-substring-no-properties (region-beginning)
                                                    (region-end))))
         (article (or article (cdr gnus-article-current)))
         (data (gnus-data-find-list article))
         (ghead (gnus-data-header (car data)))
         (message-id (mail-header-message-id ghead))
         (raw-subject (mail-header-subject ghead))
         (subject (and raw-subject (rfc2047-decode-string raw-subject)))
         (date-sent (mail-header-date ghead))
         (from (mail-header-from ghead))
         (from (if from (rfc2047-decode-string from) "unknown"))
         (name (car (ignore-errors
                      (mail-extract-address-components from))))
         fname lname)

    (when name
      (let ((new-name name))
        (dolist (transform org-author-transforms)
          (setq new-name
                (replace-regexp-in-string (car transform)
                                          (cdr transform) new-name)))
        (setq name new-name)))

    (when (stringp name)
      ;; Guess first name and last name:
      (cond ((string-match
              "\\`\\(\\w\\|[-.]\\)+ \\(\\w\\|[-.]\\)+\\'" name)
             (setq fname (nth 0 (split-string name "[ \t]+"))
                   lname (nth 1 (split-string name "[ \t]+"))))
            ((string-match
              "\\`\\(\\w\\|[-.]\\)+, \\(\\w\\|[-.]\\)+\\'" name)
             (setq fname (nth 1 (split-string name "[ \t,]+"))
                   lname (nth 0 (split-string name "[ \t,]+"))))
            ((string-match "\\`\\(\\w\\|[-.]\\)+\\'" name)
             (setq fname name
                   lname ""))
            ((string-match "\\`\\(\\w+?\\) " name)
             (setq fname (match-string 1 name)
                   lname ""))))

    (org-capture nil "a")

    (when (stringp fname)
      (insert ?\( fname)
      (if (and org-smart-capture-use-lastname (stringp lname)
               (> (length lname) 0))
          (insert ?  lname))
      (insert ?\) ? ))

    (if subject
        (let ((new-subject subject))
          (dolist (transform org-subject-transforms)
            (setq new-subject
                  (replace-regexp-in-string (car transform)
                                            (cdr transform) new-subject)))
          (save-excursion
            (insert new-subject))))

    (when body
      (cl-flet ((trim-string
                  (str)
                  (replace-regexp-in-string
                   "\\(\\`[[:space:]\n]*\\|[[:space:]\n]*\\'\\)" "" str)))
        (save-excursion
          (goto-char (point-max))
          (unless (bolp)
            (forward-line 1))
          (unless (bolp)
            (insert ?\n))
          (insert body))))

    (org-set-property "Date"
                      (format-time-string
                       (org-time-stamp-format 'long 'inactive)
                       (org-encode-time (parse-time-string date-sent))))
    (org-set-property "Message"
                      (format "[[message://%s][%s]]"
                              (substring message-id 1 -1)
                              (subst-char-in-string
                               ?\[ ?\{ (subst-char-in-string
                                        ?\] ?\} subject))))
    (org-set-property "Author" from)

    (when multiple
      (org-capture-finalize)
      (message "Captured: (%s) %s" fname subject))))

(defun org-smart-capture-create-file-task ()
  "Create Org task with attached file from Dired entry at point."
  (interactive)
  (require 'org-attach)
  (unless (derived-mode-p 'dired-mode)
    (user-error "Not in Dired buffer"))
  (let* ((target-file (dired-get-filename nil t))
         (heading (file-name-nondirectory target-file)))
    (call-interactively #'org-capture)
    (org-attach-attach target-file nil 'mv)))

;;;###autoload
(defun org-smart-capture (&optional arg func)
  (interactive "P")
  (cond ((and (eq major-mode 'dired-mode)
              (y-or-n-p "Create task from file/directory as attachment?"))
         (org-smart-capture-create-file-task))

        ((eq major-mode 'gnus-article-mode)
         (org-smart-capture-article)
         (with-current-buffer gnus-summary-buffer
           (gnus-summary-mark-as-read
            nil (unless (string= (buffer-name) "*Summary INBOX*")
                  gnus-dormant-mark))))

        ((eq major-mode 'gnus-summary-mode)
         (save-excursion
           (let* ((current-article (gnus-summary-article-number))
                  (articles (gnus-summary-work-articles nil))
                  (multiple (> (length articles) 1)))
             (dolist (article articles)
               (gnus-summary-remove-process-mark article)
               (gnus-summary-mark-as-read
                article (unless (string= (buffer-name gnus-summary-buffer)
                                         "*Summary INBOX*")
                          gnus-dormant-mark))
               (save-excursion
                 (org-smart-capture-article article multiple)))))
         (gnus-summary-position-point)
         (gnus-set-mode-line 'summary))

        (t
         (call-interactively (or func #'org-capture)))))

(provide 'org-smart-capture)

;;; org-smart-capture.el ends here
