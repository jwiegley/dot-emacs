;;; ialign.el --- Interactive align-regexp.

;;
;; Author: Michał Kondraciuk <k.michal@zoho.com>
;; URL: https://github.com/mkcms/interactive-align
;; Package-Requires: ((emacs "24.4"))
;; Version: 0.0.1
;; Keywords: tools, editing, align, interactive

;; Copyright (C) 2017 Michał Kondraciuk

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
;;
;; This package provides command `ialign-interactive-align'
;; which can be used to interactively align a region
;; using a regexp read from minibuffer, like `align-regexp'.
;;
;; See documentation for command `ialign-interactive-align'.

(require 'align)

;;; Code:

(defgroup ialign nil
  "Interactive align-regexp."
  :group 'align)

(defcustom ialign-minibuffer-keymap
  (let ((map (copy-keymap minibuffer-local-map)))
    (define-key map (kbd "C-c C-r") #'ialign-toggle-repeat)
    (define-key map (kbd "C-c C-t") #'ialign-toggle-tabs)
    (define-key map (kbd "C-c +") #'ialign-increment-spacing)
    (define-key map (kbd "C-c -") #'ialign-decrement-spacing)
    (define-key map (kbd "C-c [") #'ialign-decrement-group)
    (define-key map (kbd "C-c ]") #'ialign-increment-group)
    (define-key map (kbd "C-c C-f") #'ialign-set-group)
    (define-key map (kbd "C-c C-s") #'ialign-set-spacing)
    (define-key map (kbd "C-c RET") #'ialign-commit)
    (define-key map (kbd "C-c C-c") #'ialign-update)
    map)
  "Keymap used in minibuffer during `ialign-interactive-align'."
  :group 'ialign)

(defcustom ialign-default-spacing align-default-spacing
  "An integer that represents the default amount of padding to use."
  :group 'ialign
  :type 'integer)

(defcustom ialign-align-with-tabs nil
  "A value that says when the region should be aligned with tabs.
If it's nil, never use tabs.
If it's t, always use tabs.
If it's the symbol 'indent-tabs-mode, use value of variable
`indent-tabs-mode'."
  :group 'ialign
  :type '(choice (const :tag "Never use tabs" nil)
		 (const :tag "Always use tabs" t)
		 (const :tag "Use value of variable `indent-tabs-mode'"
			indent-tabs-mode)))

(defcustom ialign-auto-update t
  "A value that says when to align the region as the characters are typed.
If it is nil, never update (you can manually update with `ialign-update').
If it is t, always update.
If it is an integer, update if the number of lines in the region is less than
or equal to this, otherwise do not update."
  :group 'ialign
  :type
  '(choice (const :tag "Never update" nil)
	   (const :tag "Always update" t)
	   (integer :tag "Update if number of lines is less than or equal")))

(defcustom ialign-initial-regexp "\\(\\s-+\\)"
  "Initial regexp to use when calling `ialign-interactive-align'."
  :group 'ialign
  :type 'regexp)

(defvar ialign--buffer nil)
(defvar ialign--start nil)
(defvar ialign--end nil)
(defvar ialign--region-contents nil)
(defvar ialign--tabs nil)
(defvar ialign--group nil)
(defvar ialign--spacing nil)
(defvar ialign--repeat nil)
(defvar ialign--regexp nil)
(defvar ialign--history nil)
(defvar ialign--error nil)

(defmacro ialign--with-region-narrowed (&rest forms)
  "Evaluate FORMS in `ialign--buffer'.
The buffer is narrowed to region that is to be aligned."
  `(with-current-buffer ialign--buffer
     (save-excursion
       (save-restriction
	 (widen)
	 (narrow-to-region ialign--start ialign--end)
	 (unwind-protect
	     (progn
	       ,@forms)
	   (set-marker ialign--start (point-min))
	   (set-marker ialign--end (point-max)))))))

(defun ialign--active-p ()
  "Return non-nil if currently executing `ialign-interactive-align'."
  ialign--buffer)

(defun ialign-toggle-repeat ()
  "Toggle 'repeat' argument passed to `align-regexp'.
When the repeat argument is non-nil, the alignment is repeated throughout
the line.
Does nothing when currently not aligning with `ialign-interactive-align'."
  (interactive)
  (when (ialign--active-p)
    (setq ialign--repeat (not ialign--repeat))
    (ialign-update)))

(defun ialign-toggle-tabs ()
  "Toggle tab usage during alignment.
After executing this command, the region is always aligned with either tabs
or spaces, regardless of value of the variable `ialign-align-with-tabs'.
Does nothing when currently not aligning with `ialign-interactive-align'."
  (interactive)
  (when (ialign--active-p)
    (setq ialign--tabs (not ialign--tabs))
    (ialign-update)))

(defun ialign-increment-group ()
  "Increment the parenthesis group argument passed to `align-regexp'.
Use `ialign-set-group' to set the group to a specific number.
Does nothing when currently not aligning with `ialign-interactive-align'."
  (interactive)
  (ialign-set-group (1+ ialign--group)))

(defun ialign-decrement-group ()
  "Decrement the parenthesis group argument passed to `align-regexp'.
Use `ialign-set-group' to set the group to a specific number.
Does nothing when currently not aligning with `ialign-interactive-align'."
  (interactive)
  (ialign-set-group (1- ialign--group)))

(defun ialign-set-group (group)
  "Set the parenthesis group argument for the `align-regexp' command to GROUP.
This should be called with a numeric prefix argument that is
the group number to set.
Does nothing when currently not aligning with `ialign-interactive-align'."
  (interactive "p")
  (or group (setq group 1))
  (when (ialign--active-p)
    (setq ialign--group group)
    (ialign-update)))

(defun ialign-increment-spacing ()
  "Increment the amount of spacing passed to `align-regexp' command.
Use `ialign-set-spacing' to set the spacing to specific number.
Does nothing when currently not aligning with `ialign-interactive-align'."
  (interactive)
  (when (ialign--active-p)
    (setq ialign--spacing (1+ ialign--spacing))
    (ialign-update)))

(defun ialign-decrement-spacing ()
  "Decrement the amount of spacing passed to `align-regexp' command.
Use `ialign-set-spacing' to set the spacing to specific number.
Does nothing when currently not aligning with `ialign-interactive-align'."
  (interactive)
  (when (ialign--active-p)
    (setq ialign--spacing (1- ialign--spacing))
    (ialign-update)))

(defun ialign-set-spacing (spacing)
  "Set the spacing parameter passed to `align-regexp' command to SPACING.
This should be called with a numeric prefix argument.
Does nothing when currently not aligning with `ialign-interactive-align'."
  (interactive "p")
  (or spacing (setq spacing 1))
  (when (ialign--active-p)
    (setq ialign--spacing spacing)
    (ialign-update)))

(defun ialign-commit ()
  "Align the region using the current regexp and commit change in the buffer.
The region is aligned using the current regexp only if it's valid.
Next alignments will use the newly aligned region.
Does nothing when currently not aligning with `ialign-interactive-align'."
  (interactive)
  (when (ialign--active-p)
    (ialign--with-region-narrowed
     (ialign-update)
     (setq ialign--region-contents (buffer-substring (point-min) (point-max)))
     (minibuffer-message "Commited regexp %s" ialign--regexp))))

(defun ialign--make-marker (location)
  "Make marker at LOCATION."
  (let ((marker (make-marker)))
    (set-marker marker location)
    (set-marker-insertion-type marker t)
    marker))

(defun ialign--revert ()
  "Revert the aligned region to original `ialign--region-contents'."
  (ialign--with-region-narrowed
   (delete-region ialign--start ialign--end)
   (insert ialign--region-contents)))

(defun ialign--enable-tabs-p ()
  "Return non-nil if tabs should be used for aligning current region."
  (unless (ialign--active-p)
    (error "Called outside `ialign-interactive-align'"))
  (if (eq ialign--tabs 'indent-tabs-mode)
      (with-current-buffer ialign--buffer
	indent-tabs-mode)
    ialign--tabs))

(defun ialign--autoupdate-p ()
  "Return non-nil if the region should be aligned as characters are typed."
  (if (integerp ialign-auto-update)
      (ialign--with-region-narrowed
       (<= (- (line-number-at-pos (point-max))
	      (line-number-at-pos (point-min)))
	  ialign-auto-update))
    ialign-auto-update))

(defun ialign--update-minibuffer-prompt ()
  "Update the minibuffer prompt to show arguments passed to `align-regexp'."
  (let ((inhibit-read-only t)
	(prompt (format "Align regexp %s(group %s%s, spacing %s%s, %s): "
			(if (ialign--autoupdate-p) "" "(manual) ") ialign--group
			(if (< ialign--group 0) " (justify)" "") ialign--spacing
			(if ialign--repeat ", repeat" "")
			(if (ialign--enable-tabs-p) "with tabs" "no tabs"))))
    (put-text-property (point-min) (minibuffer-prompt-end) 'display prompt)))

(defun ialign--minibuffer-setup-hook ()
  "Function called on minibuffer setup.  Aligns the region."
  (and (ialign--active-p) (ialign-update)))
(add-hook 'minibuffer-setup-hook #'ialign--minibuffer-setup-hook)

(defun ialign--align ()
  "Revert the current region, then align it."
  (ialign--revert)
  (ialign--with-region-narrowed
   (align-regexp (point-min) (point-max) ialign--regexp
		 ialign--group ialign--spacing ialign--repeat)))

(defun ialign-update ()
  "Align the region with regexp in the minibuffer for preview.
Does temporary alignment for preview only.
Use `ialign-commit' to actually align the region in the buffer."
  (interactive)
  (when (and (ialign--active-p) (minibufferp))
    (ialign--update-minibuffer-prompt)
    (when (or (called-interactively-p 'interactive) (ialign--autoupdate-p))
      (let ((regexp (minibuffer-contents-no-properties))
	    (indent-tabs-mode (ialign--enable-tabs-p)))
	(setq ialign--regexp regexp)
	(ialign--align)
	(redisplay)))))

(defun ialign--after-change (beg end len)
  "Function called after change.
Updates the minibuffer prompt and maybe realigns the region."
  (when (and (ialign--active-p) (minibufferp))
    (condition-case err
	(progn
	  (ialign-update)
	  (setq ialign--error nil))
      (error
       (progn
	 (unless ialign--error
	   (setq ialign--error err)
	   (run-with-timer
	    0.05 nil
	    (lambda ()
	      (when ialign--error
		(minibuffer-message (error-message-string ialign--error)))))))))))

;;;###autoload
(defun ialign-interactive-align (beg end)
  "Interactively align region BEG END using regexp read from minibuffer.
As characters are typed in the minibuffer, the region is aligned
using `align-regexp' and the result is presented to the user.
\\<ialign-minibuffer-keymap>
If the custom option `ialign-auto-update' is not set to t, manual update is
possible with command `ialign-update' bound to \\[ialign-update].

Additional arguments passed to `align-regexp' are displayed in
the minibuffer prompt and all of them can be interactively
specified.  The parenthesis group argument can be changed using
\\[ialign-decrement-group], \\[ialign-increment-group] and \
\\[ialign-set-group], the spacing can be modified using
\\[ialign-decrement-spacing], \\[ialign-increment-spacing] \
and \\[ialign-set-spacing].

The keymap used in minibuffer is `ialign-minibuffer-keymap':
\\{ialign-minibuffer-keymap}"
  (interactive "r")
  (if (ialign--active-p)
      (error "Already aligning")
    (let* ((ialign--buffer (current-buffer))
	   (ialign--start (ialign--make-marker beg))
	   (ialign--end (ialign--make-marker end))
	   (region-contents (buffer-substring beg end))
	   (ialign--region-contents region-contents)
	   (ialign--repeat nil)
	   (ialign--group 1)
	   (ialign--spacing ialign-default-spacing)
	   (ialign--tabs ialign-align-with-tabs)
	   (ialign--regexp nil)
	   success)
      (unwind-protect
	  (progn
	    (add-hook 'after-change-functions #'ialign--after-change)
	    (let ((buffer-undo-list t))
	      (read-from-minibuffer " " ialign-initial-regexp
                                    ialign-minibuffer-keymap
				    nil 'ialign--history)
	      (setq success t)))
	(if success
	    (progn (push (cons region-contents beg) buffer-undo-list)
		   (push (cons (marker-position ialign--start)
			       (marker-position ialign--end))
			 buffer-undo-list))
	  (ialign--revert))
	(set-marker ialign--start nil)
	(set-marker ialign--end nil)))))

(provide 'ialign)

;;; ialign.el ends here
