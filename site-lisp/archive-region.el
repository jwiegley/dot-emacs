;;;; archive-region.el --- Move region to archive file instead of killing
;; Time-stamp: <2010-05-09 10:59:40 rubikitch>

;; Copyright (C) 2010  rubikitch

;; Author: rubikitch <rubikitch@ruby-lang.org>
;; Keywords: languages
;; URL: http://www.emacswiki.org/cgi-bin/wiki/download/archive-region.el

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
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
;;
;; Extend C-w to have archive feature.
;; C-u C-w moves region to the archive file.
;; C-u C-u C-w opens the archive file.
;; The archive files have suffix "_archive" after original filename.

;;; Commands:
;;
;; Below are complete command list:
;;
;;  `archive-region'
;;    Move the region to archive file.
;;  `archive-region-open-archive-file-other-window'
;;    Open archive file.
;;  `kill-region-or-archive-region'
;;    Extend `kill-region' (C-w) to have archive feature.
;;
;;; Customizable Options:
;;
;; Below are customizable option list:
;;

;;; Installation:
;;
;; Put archive-region.el to your load-path.
;; The load-path is usually ~/elisp/.
;; It's set in your ~/.emacs like this:
;; (add-to-list 'load-path (expand-file-name "~/elisp"))
;;
;; And the following to your ~/.emacs startup file.
;;
;; (require 'archive-region)
;;
;; No need more.

;;; Customize:
;;
;;
;; All of the above can customize by:
;;      M-x customize-group RET archive-region RET
;;


;;; History:

;; See http://www.rubyist.net/~rubikitch/gitlog/archive-region.txt

;;; Code:

(eval-when-compile (require 'cl))
(require 'newcomment)
(defgroup archive-region nil
  "archive-region"
  :group 'emacs)

(defvar archive-region-filename-suffix "_archive")
(defvar archive-region-date-format "[%Y/%m/%d]")

(defun archive-region (s e)
  "Move the region to archive file."
  (interactive "r")
  (or buffer-file-name (error "Need filename"))
  (save-restriction
    (narrow-to-region s e)
    ;; (uncomment-region (point-min) (point-max))
    (archive-region-add-header)
    (goto-char (point-max))
    (insert "\n")
    (append-to-file (point-min) (point-max) (archive-region-current-archive-file))
    (delete-region (point-min) (point-max))))

(defun archive-region-add-header ()
  (goto-char (point-min))
  (insert (format-time-string archive-region-date-format) "\n"
          (format "%S\n" (archive-region-link-to-original)))
  (let ((comment-start (or comment-start "#")))
    (comment-region (point-min) (point))))

(defun archive-region-link-to-original ()
  (list 'archive-region-pos
        (save-excursion
          (save-restriction
            (widen)
            (if (= (line-number-at-pos) 1)
                nil
              ;; find previous nonempty line
              (while (progn (forward-line -1)
                            (eq (point-at-bol) (point-at-eol))))
              (buffer-substring-no-properties (point-at-bol) (point-at-eol)))))))

(defun archive-region-pos (line)
  (find-file-other-window (archive-region-current-original-file))
  (save-restriction
    (widen)
    (goto-char (point-min))
    (and line
         (search-forward (concat "\n" line "\n") nil t)
         (forward-line -1))))

;;;; unit test
;; (install-elisp "http://www.emacswiki.org/cgi-bin/wiki/download/el-expectations.el")
;; (install-elisp "http://www.emacswiki.org/cgi-bin/wiki/download/el-mock.el")
(dont-compile
  (when (fboundp 'expectations)
    (expectations
      (desc "archive-region-link-to-original")
      (expect '(archive-region-pos "previous-line")
        (with-temp-buffer
          (insert "previous-line\ncurrent-line")
          (archive-region-link-to-original)))
      (expect '(archive-region-pos "previous-nonempty-line")
        (with-temp-buffer
          (insert "previous-nonempty-line\n\ncurrent-line")
          (archive-region-link-to-original)))
      (expect '(archive-region-pos "previous-nonempty-line")
        (with-temp-buffer
          (insert "previous-nonempty-line\n\n\ncurrent-line")
          (archive-region-link-to-original)))
      (expect '(archive-region-pos nil)
        (with-temp-buffer
          (insert "first-line")
          (archive-region-link-to-original)))
      (expect '(archive-region-pos "out-of-narrowing")
        (with-temp-buffer
          (insert "out-of-narrowing\ncurrent-line")
          (narrow-to-region (point-at-bol) (point-at-eol))
          (archive-region-link-to-original)))
      )))



(defun archive-region-current-archive-file ()
  (or buffer-file-name (error "Need filename"))
  (expand-file-name (concat (subst-char-in-string ?/ ?! buffer-file-name)
                            archive-region-filename-suffix)
                    (expand-file-name "backups" user-emacs-directory)))
(defun archive-region-current-original-file ()
  (or buffer-file-name (error "Need filename"))
  (replace-regexp-in-string
   (concat (regexp-quote archive-region-filename-suffix) "$")
   "" buffer-file-name))

(defun archive-region-open-archive-file-other-window ()
  "Open archive file."
  (interactive)
  (unless (file-exists-p (archive-region-current-archive-file))
    (error "Archive file does not exist."))
  (find-file-other-window (archive-region-current-archive-file)))

(defun kill-region-or-archive-region (arg s e)
  "Extend `kill-region' (C-w) to have archive feature.
C-w: `kill-region' (normal C-w)
C-u C-w: `archive-region' (move text to archive file) / also in kill-ring
C-u C-u C-w: `archive-region-open-archive-file-other-window' (open archive file)"
  (interactive "p\nr")
  (case arg
    (1  (kill-region s e))
    (4  (condition-case nil
            (progn
              (kill-new (buffer-substring s e))
              (archive-region s e))
          (error
           (kill-region s e))))
    (16 (archive-region-open-archive-file-other-window))))
(substitute-key-definition 'kill-region 'kill-region-or-archive-region global-map)

(provide 'archive-region)

;; How to save (DO NOT REMOVE!!)
;; (progn (git-log-upload) (emacswiki-post "archive-region.el"))
;;; archive-region.el ends here
