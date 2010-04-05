;;; browse-kill-ring+.el --- Extensions to browse-kill-ring.el
;;
;; Filename: browse-kill-ring+.el
;; Description: Extensions to browse-kill-ring.el
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 2006-2009, Drew Adams, all rights reserved.
;; Created: Tue May 25 16:35:05 2004
;; Version: 21.0
;; Last-Updated: Fri Jan  2 00:07:16 2009 (-0800)
;;           By: dradams
;;     Update #: 60
;; URL: http://www.emacswiki.org/cgi-bin/wiki/browse-kill-ring+.el
;; Keywords: convenience
;; Compatibility: GNU Emacs 20.x, GNU Emacs 21.x, GNU Emacs 22.x
;;
;; Features that might be required by this library:
;;
;;   `browse-kill-ring'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;; Extensions to browse-kill-ring.el
;;
;;
;;  Commands defined here:
;;
;;    `browse-kill-ring-delete', `browse-kill-ring-edit',
;;    `browse-kill-ring-edit-finish',
;;    `toggle-browse-kill-ring-display-style'.
;;
;;  Non-interactive functions defined here:
;;
;;    `browse-kill-ring-setup'.
;;
;;  Variables defined here:
;;
;;    `browse-kill-ring-current-ring'.
;;
;;  New key binding defined here: `t' in `browse-kill-ring-mode-map' is
;;                                `toggle-browse-kill-ring-display-style'
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change log:
;;
;; 2008/??/?? dadams
;;     Added: browse-kill-ring-current-ring, browse-kill-ring-delete,
;;            browse-kill-ring-edit(-finish), browse-kill-ring-setup.
;; 2008/??/?? dadams
;;     Created.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(eval-when-compile (require 'cl)) ;; case
(require 'browse-kill-ring)

;;;;;;;;;;;;;;;;;;;;;

(defvar browse-kill-ring-current-ring 'kill-ring
  "Symbol whose value is the current selection ring for `browse-kill-ring'.")

(defadvice kill-new (around browse-kill-ring-no-kill-new-duplicates)
  "Advice for not adding duplicate elements to the current selection ring.
Even after being \"activated\", this advice will only modify the
behavior of `kill-new' if `browse-kill-ring-no-duplicates' is
non-nil."
  (if browse-kill-ring-no-duplicates
      (set browse-kill-ring-current-ring
           (delete (ad-get-arg 0) (symbol-value browse-kill-ring-current-ring))))
  ad-do-it)

(defun browse-kill-ring-delete ()
  "Remove the item at point from the current selection ring."
  (interactive)
  (let ((over (car (overlays-at (point)))))
    (unless (overlayp over)
      (error "No kill ring item here"))
    (unwind-protect
	(progn
	  (setq buffer-read-only nil)
	  (let ((target (overlay-get over 'browse-kill-ring-target)))
	    (delete-region (overlay-start over)
			   (1+ (overlay-end over)))
	    (set browse-kill-ring-current-ring
                 (delete target (symbol-value browse-kill-ring-current-ring))))
	  (when (get-text-property (point) 'browse-kill-ring-extra)
	    (let ((prev (previous-single-property-change (point)
							 'browse-kill-ring-extra))
		  (next (next-single-property-change (point)
						     'browse-kill-ring-extra)))
	      ;; This is some voodoo.
	      (when prev
		(incf prev))
	      (when next
		(incf next))
	      (delete-region (or prev (point-min))
			     (or next (point-max))))))
      (setq buffer-read-only t)))
  (browse-kill-ring-resize-window)
  (browse-kill-ring-forward 0))

(defun browse-kill-ring-edit ()
  "Edit the current selection ring entry at point."
  (interactive)
  (let ((overs (overlays-at (point))))
    (unless overs
      (error "No kill ring entry here"))
    (let* ((target (overlay-get (car overs)
				'browse-kill-ring-target))
	   (target-cell (member target (symbol-value browse-kill-ring-current-ring))))
      (unless target-cell
	(error "Item deleted from the current selection ring"))
      (switch-to-buffer (get-buffer-create "*Kill Ring Edit*"))
      (setq buffer-read-only nil)
      (erase-buffer)
      (insert target)
      (goto-char (point-min))
      (browse-kill-ring-resize-window)
      (browse-kill-ring-edit-mode)
      (message "%s"
	       (substitute-command-keys
		"Use \\[browse-kill-ring-edit-finish] to finish editing."))
      (setq browse-kill-ring-edit-target target-cell))))

(defun browse-kill-ring-edit-finish ()
  "Commit the changes to the current selection ring."
  (interactive)
  (if browse-kill-ring-edit-target
      (setcar browse-kill-ring-edit-target (buffer-string))
    (when (y-or-n-p "The item has been deleted; add to front? ")
      (push (buffer-string) (symbol-value browse-kill-ring-current-ring))))
  (bury-buffer)
  ;; The user might have rearranged the windows
  (when (eq major-mode 'browse-kill-ring-mode)
    (browse-kill-ring-setup (current-buffer)
			    browse-kill-ring-original-window
			    nil
			    browse-kill-ring-original-window-config)
    (browse-kill-ring-resize-window)))

(defun browse-kill-ring-setup (buf window &optional regexp window-config)
  (with-current-buffer buf
    (unwind-protect
         (progn
           (setq browse-kill-ring-current-ring 'kill-ring)
           (browse-kill-ring-mode)
           (setq buffer-read-only nil)
           (when (eq browse-kill-ring-display-style
                     'one-line)
             (setq truncate-lines t))
           (let ((inhibit-read-only t))
             (erase-buffer))
           (setq browse-kill-ring-original-window window
                 browse-kill-ring-original-window-config
                 (or window-config
                     (current-window-configuration)))
           (let ((browse-kill-ring-maximum-display-length
                  (if (and browse-kill-ring-maximum-display-length
                           (<= browse-kill-ring-maximum-display-length 3))
                      4
                    browse-kill-ring-maximum-display-length))
                 (items (mapcar
                         (if browse-kill-ring-depropertize
                             #'browse-kill-ring-depropertize-string
                           #'copy-sequence)
                         (symbol-value browse-kill-ring-current-ring))))
             (when (not browse-kill-ring-display-duplicates)
               ;; I'm not going to rewrite `delete-duplicates'.  If
               ;; someone really wants to rewrite it here, send me a
               ;; patch.
               (require 'cl)
               (setq items (delete-duplicates items :test #'equal)))
             (when (stringp regexp)
               (setq items (delq nil
                                 (mapcar
                                  #'(lambda (item)
                                      (when (string-match regexp item)
                                        item))
                                  items))))
             (funcall (or (cdr (assq browse-kill-ring-display-style
                                     browse-kill-ring-display-styles))
                          (error "Invalid `browse-kill-ring-display-style': %s"
                                 browse-kill-ring-display-style))
                      items)
             ;; Code from Michael Slass <mikesl@wrq.com>
             (message
              (let* ((len (length (symbol-value browse-kill-ring-current-ring)))
                     (entry
                      (if (= 1 len) "entry" "entries")))
                (concat
                 (if (and (not regexp)
                          browse-kill-ring-display-duplicates)
                     (format "%s %s in the ring." len entry)
                   (format "%s (of %s) %s in the ring shown." (length items) len entry))
                 (substitute-command-keys
                  (concat "    Type \\[browse-kill-ring-quit] to quit.  "
                          "\\[describe-mode] for help.")))))
             ;; End code from Michael Slass <mikesl@wrq.com>
             (set-buffer-modified-p nil)
             (goto-char (point-min))
             (browse-kill-ring-forward 0)
             (when regexp
               (setq mode-name (concat "Kill Ring [" regexp "]")))
             (run-hooks 'browse-kill-ring-hook)
             ;; I will be very glad when I can get rid of this gross
             ;; hack, which solely exists for XEmacs users.
             (when (and (featurep 'xemacs)
                        font-lock-mode)
               (browse-kill-ring-fontify-region (point-min) (point-max)))))
      (progn
	(setq buffer-read-only t)))))




(browse-kill-ring-default-keybindings)

(defun toggle-browse-kill-ring-display-style ()
  "Toggle browse-kill-ring-display-style between `separated' and `one-line'."
  (interactive)
  (setq browse-kill-ring-display-style
        (case browse-kill-ring-display-style
          (separated 'one-line)
          (otherwise 'separated)))
  (browse-kill-ring-update)
  (message "browse-kill-ring-display-style is now %s" browse-kill-ring-display-style))

(define-key browse-kill-ring-mode-map (kbd "t") 'toggle-browse-kill-ring-display-style)



;;;;;;;;;;;;;;;;;;;;;

(provide 'browse-kill-ring+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; browse-kill-ring+.el ends here
