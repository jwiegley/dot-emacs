;;; org-bookmark-heading.el --- Emacs bookmark support for org-mode

;; Author: Adam Porter <adam@alphapapa.net>
;; Version: 1.0.0
;; Url: http://github.com/alphapapa/org-bookmark-heading
;; Package-Requires: ((emacs "24.4"))
;; Keywords: hypermedia, outlines

;;; Commentary:

;; This package provides Emacs bookmark support for org-mode.  You can
;; bookmark headings in org-mode files and jump to them using standard
;; Emacs bookmark commands.

;; It seems like this file should be named org-bookmark.el, but a
;; package by that name already exists in org-mode/contrib which lets
;; org-mode links point to Emacs bookmarks, sort-of the reverse of
;; this package.

;; It also seems like this should be built-in to org-mode...  ;)

;;; Installation

;; Require the package in your init file:

;; (require 'org-bookmark-heading)

;; Then you can customize `org-bookmark-jump-indirect' if you like.

;;; Usage

;; Use the standard Emacs bookmark commands, "C-x r m", etc.

;; If you use Helm, you can jump to org-mode bookmarks in an indirect
;; buffer by pressing "<C-return>" in the Helm buffer, or by choosing
;; the action from the list.

;; You can also customize the variable `org-bookmark-jump-indirect' to
;; make org-mode bookmarks always open in indirect buffers.

;;; Credits:

;;  Thanks to Steve Purcell for his advice on several improvements.

;;; License:

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

;;; Code:

(require 'mode-local)
(require 'org)
(require 'bookmark)

(defcustom org-bookmark-jump-indirect nil
  "Jump to `org-mode' bookmarks in indirect buffers with `org-tree-to-indirect-buffer'."
  :group 'org :type 'boolean)

(setq-mode-local org-mode bookmark-make-record-function 'org-bookmark-make-record)

(defun org-replace-links-in-string-with-desc (string)
  "Replace `org-mode' links in STRING with their descriptions."
  (if (string-match org-bracket-link-regexp string)
      (replace-regexp-in-string org-bracket-link-regexp
                                (lambda (text) (match-string-no-properties 3 text))
                                string)
    ;; No links found; return original string
    string))

(defun org-bookmark-make-record ()
  "Return alist for `bookmark-set' for current `org-mode'
heading.  Set org-id for heading if necessary."
  (if (org-before-first-heading-p)
      (bookmark-make-record-default)
    (let* ((filename (buffer-file-name (org-base-buffer (current-buffer))))
	   (org-filename (file-name-nondirectory filename))
	   (heading (org-replace-links-in-string-with-desc (nth 4 (org-heading-components))))
	   (name (concat org-filename ":" heading) )
	   front-context-string handler)
      (unless (and (boundp 'bookmark-name)
		   (or (string= bookmark-name (plist-get org-bookmark-names-plist :last-capture-marker))
		       (string= bookmark-name (plist-get org-bookmark-names-plist :last-capture))
		       (string= bookmark-name (plist-get org-bookmark-names-plist :last-refile))))
	;; When `org-capture-mode' is active, and/or when a heading is
	;; being refiled, do not create an org-id for the current
	;; heading, and do not set the bookmark handler.  This is
	;; because org-capture sets a bookmark for the last capture when
	;; `org-capture-bookmark' is non-nil, and `org-refile' sets a
	;; bookmark when a heading is refiled, and we don't want every
	;; heading captured or refiled to get an org-id set by this
	;; function, because not everyone wants to have property drawers
	;; "polluting" every heading in their org files. `bookmark-name'
	;; is set in `org-capture-bookmark-last-stored-position' and in
	;; `org-refile', and it seems to be the way to detect whether
	;; this is being called from a capture or a refile.

	;; MAYBE: An option to always use org-ids.  Some people might
	;; prefer to have all headings given org-ids, because that way
	;; the bookmarks will be more accurate.  The file/line-number
	;; bookmarks aren't guaranteed to be accurate with org files.
	(setq front-context-string (org-id-get (point) t))
	(setq handler 'org-bookmark-jump))
      (rassq-delete-all nil `(,name
			      (filename . ,filename)
			      (handler . ,handler)
			      (front-context-string . ,front-context-string))))))

(defun org-bookmark-jump (bookmark)
  "Jump to BOOKMARK, where BOOKMARK is one whose
`front-context-string' is an org-id."
  (let ((filename (cdr (assoc 'filename bookmark)))
        (id (cdr (assoc 'front-context-string bookmark)))
        (original-buffer (current-buffer))
        marker new-buffer)
    (or
     ;; Look in open and agenda files first. This way, if the node has
     ;; moved to another file, this might find it.
     (setq marker (org-id-find id t))

     (when (and filename
                (not (org-find-base-buffer-visiting filename))
                (file-exists-p filename))
       ;; Bookmark's file exists but is not open, nor in the
       ;; agenda. Find the file and look for the ID again.
       (setq new-buffer (find-file-noselect filename))
       (setq marker (org-id-find id t))))

    (if marker
        (progn
          ;; Bookmark found
          (org-goto-marker-or-bmk marker)

          (when org-bookmark-jump-indirect
            (org-tree-to-indirect-buffer)
            (unless (equal original-buffer (car (window-prev-buffers)))
              ;; The selected bookmark was in a different buffer.  Put the
              ;; non-indirect buffer at the bottom of the prev-buffers list
              ;; so it won't be selected when the indirect buffer is killed.
              (set-window-prev-buffers nil (append (cdr (window-prev-buffers))
                                                   (car (window-prev-buffers))))))

          (unless (equal (buffer-file-name (marker-buffer marker)) filename)
            ;; TODO: Automatically update the bookmark?

            ;; Warn that the node has moved to another file
            (message "Heading has moved to another file; consider updating the bookmark.")))
      (progn
        ;; Bookmark not found
        (if new-buffer
            (progn
              ;; File found but not bookmark
              (kill-buffer new-buffer)  ; Don't leave buffer open
              (message "Bookmark for org-id %s not found in open org files, agenda files, or in %s." id filename))

          ;; File not found
          (message "Bookmark for org-id %s not found in open org files or agenda files, and file not found: %s" id filename))))))

;;;; Helm support

(with-eval-after-load 'helm-bookmark

  (defun helm-org-bookmark-jump-indirect-action (bookmark)
    "Call `bookmark-jump' with `org-bookmark-jump-indirect' set to t.

This function is necessary because `helm-exit-and-execute-action'
somehow loses the dynamic binding of `org-bookmark-jump-indirect'.
This calls `bookmark-jump' with it set properly.  Maybe there's a
better way to do this, but Helm can be confusing, and this works."
    (let ((org-bookmark-jump-indirect t))
      (bookmark-jump bookmark)))

  (defun helm-org-bookmark-jump-indirect ()
    "Jump to `org-mode' bookmark in an indirect buffer."
    (interactive)
    (with-helm-alive-p
      (let ((bookmark (helm-get-selection)))
        (if (equal (bookmark-get-handler bookmark) 'org-bookmark-jump)
            ;; Selected candidate is an org-mode bookmark
            (helm-exit-and-execute-action 'helm-org-bookmark-jump-indirect-action)
          (error "Not an org-mode bookmark")))))

  (unless (lookup-key helm-bookmark-map (kbd "<C-return>"))
    (define-key helm-bookmark-map (kbd "<C-return>") 'helm-org-bookmark-jump-indirect))
  (add-to-list 'helm-type-bookmark-actions
               '("Jump to org-mode bookmark in indirect buffer" . helm-org-bookmark-jump-indirect-action)
               t))

(provide 'org-bookmark-heading)

;;; org-bookmark-heading.el ends here
