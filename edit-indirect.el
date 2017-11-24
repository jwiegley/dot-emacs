;;; edit-indirect.el --- Edit regions in separate buffers -*- lexical-binding: t -*-

;; Author: Fanael Linithien <fanael4@gmail.com>
;; URL: https://github.com/Fanael/edit-indirect
;; Version: 0.1.5
;; Package-Requires: ((emacs "24.3"))

;; This file is NOT part of GNU Emacs.

;; Copyright (c) 2014-2017, Fanael Linithien
;; All rights reserved.
;;
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:
;;
;;   * Redistributions of source code must retain the above copyright
;;     notice, this list of conditions and the following disclaimer.
;;   * Redistributions in binary form must reproduce the above copyright
;;     notice, this list of conditions and the following disclaimer in the
;;     documentation and/or other materials provided with the distribution.
;;
;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
;; IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
;; TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
;; PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
;; OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
;; EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
;; PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
;; PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
;; LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;;; Commentary:

;; Edit regions in separate buffers, like `org-edit-src-code' but for arbitrary
;; regions.
;;
;; See the docstring of `edit-indirect-region' for details.

;;; Code:
(defgroup edit-indirect nil
  "Editing regions in separate buffers."
  :group 'editing)

(defcustom edit-indirect-guess-mode-function #'edit-indirect-default-guess-mode
  "The function used to guess the major mode of an edit-indirect buffer.
It's called with the edit-indirect buffer as the current buffer.
It's called with three arguments, the parent buffer, the beginning
and the end of the parent buffer region being editing.

Note that the buffer-local value from the parent buffer is used."
  :type 'function
  :group 'edit-indirect)

(defcustom edit-indirect-after-creation-hook nil
  "Functions called after the edit-indirect buffer is created.
The functions are called with the edit-indirect buffer as the
current buffer.

Note that the buffer-local value from the parent buffer is used."
  :type 'hook
  :group 'edit-indirect)

(defcustom edit-indirect-before-commit-hook nil
  "Functions called before the edit-indirect buffer is committed.
The functions are called with the edit-indirect buffer as the
current buffer.

Note that the buffer-local value from the edit-indirect buffer is
used."
  :type 'hook
  :group 'edit-indirect)

(defcustom edit-indirect-before-commit-functions nil
  "Functions called before an edit-indirect buffer is committed.
The functions are called with the parent buffer as the current
buffer.
Each function is called with two arguments, the beginning and the
end of the region to be changed."
  :type 'hook
  :group 'edit-indirect)

(defcustom edit-indirect-after-commit-functions nil
  "Functions called after an edit-indirect buffer has been committed.
The functions are called with the parent buffer as the current
buffer.
Each function is called with two arguments, the beginning and the
end of the changed region."
  :type 'hook
  :group 'edit-indirect)

(defgroup edit-indirect-faces nil
  "Faces used in `edit-indirect'."
  :group 'edit-indirect
  :group 'faces
  :prefix "edit-indirect")

(defface edit-indirect-edited-region
  '((t :inherit secondary-selection))
  "Face used to highlight an indirectly edited region."
  :group 'edit-indirect-faces)

;; Emacs <= 24.3 has no `define-error'.
(let* ((user-error-conditions (get 'user-error 'error-conditions))
       (define-user-error (lambda (name message)
                            (put name 'error-conditions
                                 (cons name user-error-conditions))
                            (put name 'error-message message))))
  (funcall define-user-error 'edit-indirect-overlapping
           "Indirectly edited regions cannot overlap")
  (funcall define-user-error 'edit-indirect-read-only
           "Text is read-only, modify the edit-indirect buffer instead")
  (funcall define-user-error 'edit-indirect-not-indirect
           "This is not an edit-indirect buffer"))

(defvar edit-indirect--overlay)
(defvar edit-indirect--should-quit-window nil)

;;;###autoload
(defun edit-indirect-region (beg end &optional display-buffer)
  "Edit the region BEG..END in a separate buffer.
The region is copied, without text properties, to a separate
buffer, called edit-indirect buffer, and
`edit-indirect-guess-mode-function' is called to set the major
mode.
When done, exit with `edit-indirect-commit', which will remove the
original region and replace it with the edited version; or with
`edit-indirect-abort', which will drop the modifications.

This differs from `clone-indirect-buffer' with narrowing in that
the text properties are not shared, so the parent buffer major mode
and the edit-indirect buffer major mode will not be able to tread
on each other's toes by setting up potentially conflicting text
properties, which happens surprisingly often when the font-lock
mode is used.

Edit-indirect buffers use the `edit-indirect-mode-map' keymap.

If there's already an edit-indirect buffer for BEG..END, use that.
If there's already an edit-indirect buffer active overlapping any
portion of BEG..END, an `edit-indirect-overlapping' error is
signaled.

When DISPLAY-BUFFER is non-nil or when called interactively,
display the edit-indirect buffer in some window and select it.

In any case, return the edit-indirect buffer."
  (interactive
   (if (or (use-region-p) (not transient-mark-mode))
       (prog1 (list (region-beginning) (region-end) t)
         (deactivate-mark))
     (user-error "No region")))
  (let ((buffer (edit-indirect--get-edit-indirect-buffer beg end)))
    (when display-buffer
      (with-current-buffer buffer
        (setq-local edit-indirect--should-quit-window t))
      (select-window (display-buffer buffer)))
    buffer))

(defvar edit-indirect-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c '") #'edit-indirect-commit)
    (define-key map (kbd "C-c C-c") #'edit-indirect-commit)
    (define-key map (kbd "C-c C-k") #'edit-indirect-abort)
    map)
  "Keymap for edit-indirect buffers.

\\{edit-indirect-mode-map}")

(defun edit-indirect-commit ()
  "Commit the modifications done in an edit-indirect buffer.
That is, replace the original region in the parent buffer with the
contents of the edit-indirect buffer.
The edit-indirect buffer is then killed.

Can be called only when the current buffer is an edit-indirect
buffer."
  (interactive)
  (edit-indirect--barf-if-not-indirect)
  (edit-indirect--commit)
  (edit-indirect--clean-up))

(defun edit-indirect-abort ()
  "Abort indirect editing in the current buffer and kill the buffer.

Can be called only when the current buffer is an edit-indirect
buffer."
  (interactive)
  (edit-indirect--barf-if-not-indirect)
  (edit-indirect--abort))

(defun edit-indirect-buffer-indirect-p (&optional buffer)
  "Non-nil iff the BUFFER is an edit-indirect buffer.
BUFFER defaults to the current buffer."
  (save-current-buffer
    (when buffer
      (set-buffer buffer))
    ;; (not (null)) so we don't leak the overlay to the outside world.
    (not (null edit-indirect--overlay))))

(defun edit-indirect-default-guess-mode (_parent-buffer _beg _end)
  "Guess the major mode for an edit-indirect buffer.
It's done by calling `normal-mode'."
  (normal-mode))

(defvar edit-indirect--overlay nil
  "The overlay spanning the region of the parent buffer being edited.

It's also used as the variable determining if we're in an
edit-indirect buffer at all.")
(make-variable-buffer-local 'edit-indirect--overlay)
(put 'edit-indirect--overlay 'permanent-local t)

;; Normally this would use `define-minor-mode', but that makes the mode function
;; interactive, which we don't want, because it's just an implementation detail.
(defun edit-indirect--mode (overlay)
  "Turn the `edit-indirect--mode' \"minor mode\" on.
OVERLAY is the value to set `edit-indirect--overlay' to."
  (setq edit-indirect--overlay overlay)
  (add-hook 'kill-buffer-hook #'edit-indirect--abort-on-kill-buffer nil t))
(with-no-warnings
  (add-minor-mode
   'edit-indirect--overlay " indirect" edit-indirect-mode-map nil #'ignore))

(defun edit-indirect--get-edit-indirect-buffer (beg end)
  "Return an edit-indirect buffer for the region BEG..END.
If there's already an edit-indirect buffer active overlapping any
portion of BEG..END, an `edit-indirect-overlapping' error is
signaled."
  (let ((old-overlay (edit-indirect--search-for-edit-indirect beg end)))
    (cond
     ((null old-overlay)
      (let ((overlay (edit-indirect--create-overlay beg end)))
        (edit-indirect--create-indirect-buffer beg end overlay)))
     ((and (= beg (overlay-start old-overlay))
           (= end (overlay-end old-overlay)))
      (overlay-get old-overlay 'edit-indirect-buffer))
     (t
      (signal 'edit-indirect-overlapping '())))))

(defun edit-indirect--search-for-edit-indirect (beg end)
  "Return an existing edit-indirect overlay for some region inside BEG..END.
If there's no indirectly edited region inside BEG..END, return
nil."
  (catch 'done
    (dolist (overlay (overlays-in beg end))
      (when (overlay-get overlay 'edit-indirect-buffer)
        (throw 'done overlay)))
    nil))

(defmacro edit-indirect--buffer-local-value (buffer variable)
  "Get the BUFFER local value of VARIABLE.
VARIABLE shall be a symbol."
  (unless (symbolp variable)
    (signal 'wrong-type-argument (list #'symbolp variable)))
  ;; `with-current-buffer' is used instead of `buffer-local-value' because
  ;; the latter doesn't give warnings about free variables when
  ;; byte-compiled.
  `(with-current-buffer ,buffer ,variable))

(defun edit-indirect--create-indirect-buffer (beg end overlay)
  "Create an edit-indirect buffer and return it.

BEG..END is the parent buffer region to insert.
OVERLAY is the overlay, see `edit-indirect--overlay'."
  (let ((buffer (generate-new-buffer (format "*edit-indirect %s*" (buffer-name))))
        (parent-buffer (current-buffer)))
    (overlay-put overlay 'edit-indirect-buffer buffer)
    (with-current-buffer buffer
      (insert-buffer-substring-no-properties parent-buffer beg end)
      (set-buffer-modified-p nil)
      (edit-indirect--mode overlay)
      ;; Use the buffer-local values from the parent buffer. Don't retrieve the
      ;; values before actual uses in case these variables are changed by some
      ;; of the many possible hooks.
      (funcall (edit-indirect--buffer-local-value
                parent-buffer edit-indirect-guess-mode-function)
               parent-buffer beg end)
      (let ((edit-indirect-after-creation-hook
             (edit-indirect--buffer-local-value
              parent-buffer edit-indirect-after-creation-hook)))
        (run-hooks 'edit-indirect-after-creation-hook)))
    buffer))

(defun edit-indirect--create-overlay (beg end)
  "Create the edit-indirect overlay and return it.

BEG and END specify the region the overlay should encompass."
  (let ((overlay (make-overlay beg end)))
    (overlay-put overlay 'face 'edit-indirect-edited-region)
    (overlay-put overlay 'modification-hooks '(edit-indirect--barf-read-only))
    (overlay-put overlay 'insert-in-front-hooks '(edit-indirect--barf-read-only))
    overlay))

(defvar edit-indirect--inhibit-read-only nil
  "Non-nil means disregard read-only status of indirectly-edited region.")

(defun edit-indirect--barf-read-only (_ov _after _beg _end &optional _len)
  "Signal an error because the text is read-only.
No error is signaled if `inhibit-read-only' or
`edit-indirect--inhibit-read-only' is non-nil."
  (unless (or inhibit-read-only edit-indirect--inhibit-read-only)
    (signal 'edit-indirect-read-only '())))

(defun edit-indirect--commit ()
  "Commit the modifications done in an edit-indirect buffer."
  (run-hooks 'edit-indirect-before-commit-hook)
  (let ((beg (overlay-start edit-indirect--overlay))
        (end (overlay-end edit-indirect--overlay))
        (buffer (current-buffer))
        (edit-indirect--inhibit-read-only t))
    (with-current-buffer (overlay-buffer edit-indirect--overlay)
      (save-excursion
        (let ((beg-marker (copy-marker beg))
              (end-marker (copy-marker end)))
          (edit-indirect--run-hook-with-positions
           'edit-indirect-before-commit-functions beg-marker end-marker)
          (save-match-data
            (set-match-data (list beg-marker end-marker))
            (replace-match (with-current-buffer buffer
                             (buffer-substring-no-properties 1 (1+ (buffer-size))))
                           t t))
          (edit-indirect--run-hook-with-positions
           'edit-indirect-after-commit-functions beg-marker (point))
          (set-marker beg-marker nil)
          (set-marker end-marker nil))))))

(defun edit-indirect--run-hook-with-positions (hook beg end)
  "Run HOOK with the specified positions BEG and END.
HOOK should be a symbol, a hook variable.
The functions are passed integer positions.
If a function changes the buffer contents, the next function will be
called with updated positions."
  (let ((beg-marker (unless (markerp beg) (copy-marker beg)))
        (end-marker (unless (markerp end) (copy-marker end))))
    (run-hook-wrapped hook
                      (lambda (f beg end)
                        (funcall f (marker-position beg) (marker-position end))
                        nil)
                      (or beg-marker beg) (or end-marker end))
    (when beg-marker (set-marker beg-marker nil))
    (when end-marker (set-marker end-marker nil))))

(defun edit-indirect--abort ()
  "Abort indirect edit."
  (edit-indirect--clean-up))

(defun edit-indirect--clean-up ()
  "Clean up an edit-indirect buffer."
  (delete-overlay edit-indirect--overlay)
  ;; Kill the overlay reference so that `edit-indirect--abort-on-kill-buffer'
  ;; won't try to call us again.
  (setq edit-indirect--overlay nil)
  ;; If we created a window, get rid of it. Kill the buffer we created.
  (if edit-indirect--should-quit-window
      (quit-window t)
    (kill-buffer)))

(defun edit-indirect--abort-on-kill-buffer ()
  "Abort indirect edit.
Should be called only from `kill-buffer-hook'."
  (when edit-indirect--overlay
    (edit-indirect--abort)))

(defun edit-indirect--barf-if-not-indirect ()
  "Signal an error if the current buffer is not an edit-indirect buffer.
The error signaled is `edit-indirect-not-indirect'."
  (unless edit-indirect--overlay
    (signal 'edit-indirect-not-indirect '())))

(provide 'edit-indirect)
;;; edit-indirect.el ends here
