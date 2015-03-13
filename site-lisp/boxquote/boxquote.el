;;; boxquote.el --- Quote text with a semi-box.
;; Copyright 1999-2008 by Dave Pearson <davep@davep.org>
;; $Revision: 1.22 $

;; boxquote.el is free software distributed under the terms of the GNU
;; General Public Licence, version 2 or (at your option) any later version.
;; For details see the file COPYING.

;;; Commentary:

;; boxquote provides a set of functions for using a text quoting style that
;; partially boxes in the left hand side of an area of text, such a marking
;; style might be used to show externally included text or example code.
;;
;; ,----
;; | The default style looks like this.
;; `----
;;
;; A number of functions are provided for quoting a region, a buffer, a
;; paragraph and a defun. There are also functions for quoting text while
;; pulling it in, either by inserting the contents of another file or by
;; yanking text into the current buffer.
;;
;; The latest version of boxquote.el can be found at:
;;
;;   <URL:http://www.davep.org/emacs/#boxquote.el>

;;; Thanks:

;; Kai Grossjohann for inspiring the idea of boxquote. I wrote this code to
;; mimic the "inclusion quoting" style in his Usenet posts. I could have
;; hassled him for his code but it was far more fun to write it myself.
;;
;; Mark Milhollan for providing a patch that helped me get the help quoting
;; functions working with XEmacs.
;;
;; Oliver Much for suggesting the idea of having a `boxquote-kill-ring-save'
;; function.
;;
;; Reiner Steib for suggesting `boxquote-where-is' and the idea of letting
;; `boxquote-describe-key' describe key bindings from other buffers. Also
;; thanks go to Reiner for suggesting `boxquote-insert-buffer'.

;;; Code:

;; Things we need:

(eval-when-compile
  (require 'cl))
(require 'rect)

;; Attempt to handle older/other emacs.
(eval-and-compile
  
  ;; If customize isn't available just use defvar instead.
  (unless (fboundp 'defgroup)
    (defmacro defgroup  (&rest rest) nil)
    (defmacro defcustom (symbol init docstring &rest rest)
      `(defvar ,symbol ,init ,docstring)))
  
  ;; If `line-beginning-position' isn't available provide one.
  (unless (fboundp 'line-beginning-position)
    (defun line-beginning-position (&optional n)
      "Return the `point' of the beginning of the current line."
      (save-excursion
        (beginning-of-line n)
        (point))))

  ;; If `line-end-position' isn't available provide one.
  (unless (fboundp 'line-end-position)
    (defun line-end-position (&optional n)
      "Return the `point' of the end of the current line."
      (save-excursion
        (end-of-line n)
        (point)))))

;; Customize options.

(defgroup boxquote nil
  "Mark regions of text with a half-box."
  :group  'editing
  :prefix "boxquote-")

(defcustom boxquote-top-and-tail "----"
  "*Text that will be used at the top and tail of the box."
  :type  'string
  :group 'boxquote)

(defcustom boxquote-top-corner ","
  "*Text used for the top corner of the box."
  :type  'string
  :group 'boxquote)

(defcustom boxquote-bottom-corner "`"
  "*Text used for the bottom corner of the box."
  :type  'string
  :group 'boxquote)

(defcustom boxquote-side "| "
  "*Text used for the side of the box."
  :type  'string
  :group 'boxquote)

(defcustom boxquote-title-format "[ %s ]"
  "*Format string to use when creating a box title."
  :type  'string
  :group 'boxquote)

(defcustom boxquote-title-files t
  "*Should a `boxquote-insert-file' title the box with the file name?"
  :type '(choice
          (const :tag "Title the box with the file name" t)
          (const :tag "Don't title the box with the file name" nil))
  :group 'boxquote)

(defcustom boxquote-file-title-function #'file-name-nondirectory
  "*Function to apply to a file's name when using it to title a box."
  :type  'function
  :group 'boxquote)

(defcustom boxquote-title-buffers t
  "*Should a `boxquote-insert-buffer' title the box with the buffer name?"
  :type '(choice
          (const :tag "Title the box with the buffer name" t)
          (const :tag "Don't title the box with the buffer name" nil))
  :group 'boxquote)

(defcustom boxquote-buffer-title-function #'identity
  "*Function to apply to a buffer's name when using it to title a box."
  :type  'function
  :group 'boxquote)

(defcustom boxquote-region-hook nil
  "*Hooks to perform when on a region prior to boxquoting.

Note that all forms of boxquoting use `boxquote-region' to create the
boxquote. Because of this any hook you place here will be invoked by any of
the boxquoting functions."
  :type  'hook
  :group 'boxquote)

(defcustom boxquote-yank-hook nil
  "*Hooks to perform on the yanked text prior to boxquoting."
  :type  'hook
  :group 'boxquote)

(defcustom boxquote-insert-file-hook nil
  "*Hooks to perform on the text from an inserted file prior to boxquoting."
  :type  'hook
  :group 'boxquote)

(defcustom boxquote-kill-ring-save-title #'buffer-name
  "*Function for working out the title for a `boxquote-kill-ring-save'.

The string returned from this function will be used as the title for a
boxquote when the saved text is yanked into a buffer with \\[boxquote-yank].

An example of a non-trivial value for this variable might be:

  (lambda ()
    (if (string= mode-name \"Article\")
        (aref gnus-current-headers 4)
      (buffer-name)))

In this case, if you are a `gnus' user, \\[boxquote-kill-ring-save] could be
used to copy text from an article buffer and, when it is yanked into another
buffer using \\[boxquote-yank], the title of the boxquote would be the ID of
the article you'd copied the text from."
  :type  'function
  :group 'boxquote)

(defcustom boxquote-describe-function-title-format "C-h f %s RET"
  "*Format string to use when formatting a function description box title"
  :type  'string
  :group 'boxquote)

(defcustom boxquote-describe-variable-title-format "C-h v %s RET"
  "*Format string to use when formatting a variable description box title"
  :type  'string
  :group 'boxquote)

(defcustom boxquote-describe-key-title-format "C-h k %s"
  "*Format string to use when formatting a key description box title"
  :type  'string
  :group 'boxquote)

(defcustom boxquote-where-is-title-format "C-h w %s RET"
  "*Format string to use when formatting a `where-is' description box title"
  :type  'string
  :group 'boxquote)

(defcustom boxquote-where-is-body-format "%s is on %s"
  "*Format string to use when formatting a `where-is' description."
  :type  'string
  :group 'boxquote)
  
;; Main code:

(defun boxquote-xemacs-p ()
  "Are we running in XEmacs?"
  (and (boundp 'running-xemacs) (symbol-value 'running-xemacs)))

(defun boxquote-points ()
  "Find the start and end points of a boxquote.

If `point' is inside a boxquote then a cons is returned, the `car' is the
start `point' and the `cdr' is the end `point'. NIL is returned if no
boxquote is found."
  (save-excursion
    (beginning-of-line)
    (let* ((re-top    (concat "^" (regexp-quote boxquote-top-corner)
                              (regexp-quote boxquote-top-and-tail)))
           (re-left   (concat "^" (regexp-quote boxquote-side)))
           (re-bottom (concat "^" (regexp-quote boxquote-bottom-corner)
                              (regexp-quote boxquote-top-and-tail)))
           (points
            (flet ((find-box-end (re &optional back)
                     (save-excursion
                       (when (if back
                                 (search-backward-regexp re nil t)
                               (search-forward-regexp re nil t))
                         (point)))))
              (cond ((looking-at re-top)
                     (cons (point) (find-box-end re-bottom)))
                    ((looking-at re-left)
                     (cons (find-box-end re-top t) (find-box-end re-bottom)))
                    ((looking-at re-bottom)
                     (cons (find-box-end re-top t) (line-end-position)))))))
      (when (and (car points) (cdr points))
        points))))

(defun boxquote-quoted-p ()
  "Is `point' inside a boxquote?"
  (not (null (boxquote-points))))

(defun boxquote-points-with-check ()
  "Get the `boxquote-points' and flag an error of no box was found."
  (or (boxquote-points) (error "I can't see a box here")))

(defun boxquote-title-format-as-regexp ()
  "Return a regular expression to match the title."
  (with-temp-buffer
    (insert (regexp-quote boxquote-title-format))
    (setf (point) (point-min))
    (when (search-forward "%s" nil t)
      (replace-match ".*" nil t))
    (buffer-string)))

(defun boxquote-get-title ()
  "Get the title for the current boxquote."
  (multiple-value-bind (prefix-len suffix-len)
      (with-temp-buffer
        (let ((look-for "%s"))
          (insert boxquote-title-format)
          (setf (point) (point-min))
          (search-forward look-for)
          (list (- (point) (length look-for) 1) (- (point-max) (point)))))
    (save-excursion
      (save-restriction
        (boxquote-narrow-to-boxquote)
        (setf (point) (+ (point-min)
                         (length (concat boxquote-top-corner
                                         boxquote-top-and-tail))))
        (if (looking-at (boxquote-title-format-as-regexp))
            (buffer-substring-no-properties (+ (point) prefix-len)
                                            (- (line-end-position) suffix-len))
          "")))))

;;;###autoload
(defun boxquote-title (title)
  "Set the title of the current boxquote to TITLE.

If TITLE is an empty string the title is removed. Note that the title will
be formatted using `boxquote-title-format'."
  (interactive (list (read-from-minibuffer "Title: " (boxquote-get-title))))
  (save-excursion
    (save-restriction
      (boxquote-narrow-to-boxquote)
      (setf (point) (+ (point-min)
                       (length (concat boxquote-top-corner
                                       boxquote-top-and-tail))))
      (unless (eolp)
        (kill-line))
      (unless (zerop (length title))
        (insert (format boxquote-title-format title))))))

;;;###autoload
(defun boxquote-region (start end)
  "Draw a box around the left hand side of a region bounding START and END."
  (interactive "r")
  (save-excursion
    (save-restriction
      (flet ((bol-at-p (n)
               (setf (point) n)
               (bolp))
             (insert-corner (corner pre-break)
               (insert (concat (if pre-break "\n" "")
                               corner boxquote-top-and-tail "\n"))))
        (let ((break-start (not (bol-at-p start)))
              (break-end   (not (bol-at-p end))))
          (narrow-to-region start end)
          (run-hooks 'boxquote-region-hook)
          (setf (point) (point-min))
          (insert-corner boxquote-top-corner break-start)
          (let ((start-point (line-beginning-position)))
            (setf (point) (point-max))
            (insert-corner boxquote-bottom-corner break-end)
            (string-rectangle start-point
                              (progn
                                (setf (point) (point-max))
                                (forward-line -2)
                                (line-beginning-position))
                              boxquote-side)))))))

;;;###autoload
(defun boxquote-buffer ()
  "Apply `boxquote-region' to a whole buffer."
  (interactive)
  (boxquote-region (point-min) (point-max)))

;;;###autoload
(defun boxquote-insert-file (filename)
  "Insert the contents of a file, boxed with `boxquote-region'.

If `boxquote-title-files' is non-nil the boxquote will be given a title that
is the result of applying `boxquote-file-title-function' to FILENAME."
  (interactive "fInsert file: ")
  (insert (with-temp-buffer
            (insert-file-contents filename nil)
            (run-hooks 'boxquote-insert-file-hook)
            (boxquote-buffer)
            (when boxquote-title-files
              (boxquote-title (funcall boxquote-file-title-function filename)))
            (buffer-string))))

;;;###autoload
(defun boxquote-insert-buffer (buffer)
  "Insert the contents of a buffer, boxes with `boxquote-region'.

If `boxquote-title-buffers' is non-nil the boxquote will be given a title that
is the result of applying `boxquote-buffer-title-function' to BUFFER."
  (interactive "bInsert Buffer: ")
  (boxquote-text
   (with-current-buffer buffer
     (buffer-substring-no-properties (point-min) (point-max))))
  (when boxquote-title-buffers
    (boxquote-title (funcall boxquote-buffer-title-function buffer))))

;;;###autoload
(defun boxquote-kill-ring-save ()
  "Like `kill-ring-save' but remembers a title if possible.

The title is acquired by calling `boxquote-kill-ring-save-title'. The title
will be used by `boxquote-yank'."
  (interactive)
  (call-interactively #'kill-ring-save)
  (setf (car kill-ring-yank-pointer)
        (format "%S" (list
                      'boxquote-yank-marker
                      (funcall boxquote-kill-ring-save-title)
                      (car kill-ring-yank-pointer)))))

;;;###autoload
(defun boxquote-yank ()
  "Do a `yank' and box it in with `boxquote-region'.

If the yanked entry was placed on the kill ring with
`boxquote-kill-ring-save' the resulting boxquote will be titled with
whatever `boxquote-kill-ring-save-title' returned at the time."
  (interactive)
  (save-excursion
    (insert (with-temp-buffer
              (yank)
              (setf (point) (point-min))
              (let ((title
                     (let ((yanked (condition-case nil
                                       (read (current-buffer))
                                     (error nil))))
                       (when (listp yanked)
                         (when (eq (car yanked) 'boxquote-yank-marker)
                           (setf (buffer-string) (nth 2 yanked))
                           (nth 1 yanked))))))
                (run-hooks 'boxquote-yank-hook)
                (boxquote-buffer)
                (when title
                  (boxquote-title title))
                (buffer-string))))))

;;;###autoload
(defun boxquote-defun ()
  "Apply `boxquote-region' the current defun."
  (interactive)
  (mark-defun)
  (boxquote-region (region-beginning) (region-end)))

;;;###autoload
(defun boxquote-paragraph ()
  "Apply `boxquote-region' to the current paragraph."
  (interactive)
  (mark-paragraph)
  (boxquote-region (region-beginning) (region-end)))

;;;###autoload
(defun boxquote-boxquote ()
  "Apply `boxquote-region' to the current boxquote."
  (interactive)
  (let ((box (boxquote-points-with-check)))
    (boxquote-region (car box) (1+ (cdr box)))))

(defun boxquote-help-buffer-name (item)
  "Return the name of the help buffer associated with ITEM."
  (if (boxquote-xemacs-p)
      (loop for buffer in (symbol-value 'help-buffer-list)
            when (string-match (concat "^*Help:.*`" item "'") buffer)
            return buffer)
    "*Help*"))

(defun boxquote-quote-help-buffer (help-call title-format item)
  "Perform a help command and boxquote the output.

HELP-CALL is a function that calls the help command.

TITLE-FORMAT is the `format' string to use to product the boxquote title.

ITEM is a function for retrieving the item to get help on."
  (let ((one-window-p (one-window-p)))
    (boxquote-text
     (save-window-excursion
       (funcall help-call)
       (with-current-buffer (boxquote-help-buffer-name (funcall item))
         (buffer-string))))
    (boxquote-title (format title-format (funcall item)))
    (when one-window-p
      (delete-other-windows))))
  
;;;###autoload
(defun boxquote-describe-function ()
  "Call `describe-function' and boxquote the output into the current buffer."
  (interactive)
  (boxquote-quote-help-buffer
   #'(lambda ()
       (call-interactively #'describe-function))
   boxquote-describe-function-title-format
   #'(lambda ()
       (car (if (boxquote-xemacs-p)
                (symbol-value 'function-history)
              minibuffer-history)))))

;;;###autoload
(defun boxquote-describe-variable ()
  "Call `describe-variable' and boxquote the output into the current buffer."
  (interactive)
  (boxquote-quote-help-buffer
   #'(lambda ()
       (call-interactively #'describe-variable))
   boxquote-describe-variable-title-format
   #'(lambda ()
       (car (if (boxquote-xemacs-p)
                (symbol-value 'variable-history)
              minibuffer-history)))))

;;;###autoload
(defun boxquote-describe-key (key)
  "Call `describe-key' and boxquote the output into the current buffer.

If the call to this command is prefixed with \\[universal-argument] you will also be
prompted for a buffer. The key defintion used will be taken from that buffer."
  (interactive "kDescribe key: ")
  (let ((from-buffer (if current-prefix-arg
                         (read-buffer "Buffer: " (current-buffer) t)
                       (current-buffer))))
    (let ((binding
           (with-current-buffer from-buffer
             (key-binding key))))
      (if (or (null binding) (integerp binding))
          (message "%s is undefined" (with-current-buffer from-buffer
                                       (key-description key)))
        (boxquote-quote-help-buffer
         #'(lambda ()
             (with-current-buffer from-buffer
               (describe-key key)))
         boxquote-describe-key-title-format
         #'(lambda ()
             (with-current-buffer from-buffer
               (key-description key))))))))

;;;###autoload
(defun boxquote-shell-command (command)
  "Call `shell-command' with COMMAND and boxquote the output."
  (interactive (list (read-from-minibuffer "Shell command: " nil nil nil 'shell-command-history)))
  (boxquote-text (with-temp-buffer
                   (shell-command command t)
                   (buffer-string)))
  (boxquote-title command))

;;;###autoload
(defun boxquote-where-is (definition)
  "Call `where-is' with DEFINITION and boxquote the result."
  (interactive "CCommand: ")
  (boxquote-text (with-temp-buffer
                   (where-is definition t)
                   (format boxquote-where-is-body-format definition (buffer-string))))
  (boxquote-title (format boxquote-where-is-title-format definition)))

;;;###autoload
(defun boxquote-text (text)
  "Insert TEXT, boxquoted."
  (interactive "sText: ")
  (save-excursion
    (unless (bolp)
      (insert "\n"))
    (insert
     (with-temp-buffer
       (insert text)
       (boxquote-buffer)
       (buffer-string)))))
  
;;;###autoload
(defun boxquote-narrow-to-boxquote ()
  "Narrow the buffer to the current boxquote."
  (interactive)
  (let ((box (boxquote-points-with-check)))
    (narrow-to-region (car box) (cdr box))))

;;;###autoload
(defun boxquote-narrow-to-boxquote-content ()
  "Narrow the buffer to the content of the current boxquote."
  (interactive)
  (let ((box (boxquote-points-with-check)))
    (narrow-to-region (save-excursion
                        (setf (point) (car box))
                        (forward-line 1)
                        (point))
                      (save-excursion
                        (setf (point) (cdr box))
                        (line-beginning-position)))))

;;;###autoload
(defun boxquote-kill ()
  "Kill the boxquote and its contents."
  (interactive)
  (let ((box (boxquote-points-with-check)))
    (kill-region (car box) (1+ (cdr box)))))

;;;###autoload
(defun boxquote-fill-paragraph (arg)
  "Perform a `fill-paragraph' inside a boxquote."
  (interactive "P")
  (if (boxquote-quoted-p)
      (save-restriction
        (boxquote-narrow-to-boxquote-content)
        (let ((fill-prefix boxquote-side))
          (fill-paragraph arg)))
    (fill-paragraph arg)))
  
;;;###autoload
(defun boxquote-unbox-region (start end)
  "Remove a box created with `boxquote-region'."
  (interactive "r")
  (save-excursion
    (save-restriction
      (narrow-to-region start end)
      (setf (point) (point-min))
      (if (looking-at (concat "^" (regexp-quote boxquote-top-corner)
                              (regexp-quote boxquote-top-and-tail)))
          (let ((ends (concat "^[" (regexp-quote boxquote-top-corner)
                              (regexp-quote boxquote-bottom-corner)
                              "]" boxquote-top-and-tail))
                (lines (concat "^" (regexp-quote boxquote-side))))
            (loop while (< (point) (point-max))
                  if (looking-at ends)  do (kill-line t)
                  if (looking-at lines) do (delete-char 2)
                  do (forward-line)))
        (error "I can't see a box here")))))

;;;###autoload
(defun boxquote-unbox ()
  "Remove the boxquote that contains `point'."
  (interactive)
  (let ((box (boxquote-points-with-check)))
    (boxquote-unbox-region (car box) (1+ (cdr box)))))

(provide 'boxquote)

;;; boxquote.el ends here.
