;;; fence-edit.el --- Edit fenced code blocks in a specific mode.

;; Copyright (c) 2017 Aaron Bieber

;; Author: Aaron Bieber <aaron@aaronbieber.com>
;; Version: 0.1
;; Package-Requires: ((emacs "24.4"))
;; Keywords: tools mode
;; Homepage: https://github.com/aaronbieber/fence-edit.el

;; Fence Edit requires at least GNU Emacs 24.4.

;; This file is not part of GNU Emacs.

;;; Commentary:

;; Fence Edit provides a convenient way to edit the contents of
;; "fenced code blocks" used by markup formats like Markdown in a
;; dedicated window set to the major mode appropriate for its
;; language.
;;
;; Simply bind a key to `fence-edit-code-at-point' and call it from
;; within any code block matching one of the patterns described in
;; `fence-edit-blocks'.  Based on a language symbol extracted from the
;; fence block pattern, the corresponding mode in
;; `fence-edit-lang-modes' will be set for the edit buffer.

;;; Code:
(defcustom fence-edit-lang-modes
  '(("cl" . lisp-interaction-mode))
  "A mapping from markdown language symbols to the modes they should be edited in."
  :group 'fence-edit
  :type '(repeat
          (cons
           (string "Language name")
           (symbol "Major mode"))))

(defcustom fence-edit-default-mode
  'text-mode
  "The default mode to use if a language-appropriate mode cannot be determined."
  :group 'fence-edit
  :type '(symbol))

(defcustom fence-edit-blocks
  '(("^[[:blank:]]*\\(?:```\\|~~~\\)[ ]?\\([^[:space:]]+\\|{[^}]*}\\)?\\(?:[[:space:]]*?\\)$"
     "^[[:blank:]]*\\(?:```\\|~~~\\)\\s *?$"
     1))
  "Alist of regexps matching editable blocks.

Each element takes the form
\(START-REGEXP END-REGEXP LANG-RULE)

Where START- and END-REGEXP are patterns matching the start and end of
the block, respectively.

If LANG-RULE is a symbol, that symbol is assumed to be a language
name.

If LANG-RULE is an integer, it is assumed to be the number of a
capture group to pass to `match-string' to get the language (a capture
group within the START-REGEXP).

If the language value with `-mode' appended to it does not resolve to
a bound function, it will be used to look up a mode in
`fence-edit-lang-modes'.  If the symbol doesn't match a key in
that list, the `fence-edit-default-mode' will be used."
  :group 'fence-edit
  :type '(repeat
          (list
           (regexp "Start regexp")
           (regexp "End regexp")
           (choice (integer "Capture group number")
                   (symbol "Language name")))))

(defconst fence-edit-window-layout 48529384
  "Register in which to save the window layout.

Registers are chars, so this is set to an int that is not likely to be
used by anything else.")

(defvar-local fence-edit-previous-mode nil
  "Mode set before narrowing, restored upon widening.")

(defvar-local fence-edit-overlay nil
  "An overlay used to indicate the original text being edited.")

(defvar-local fence-edit-mark-beg nil
  "A marker at the beginning of the edited text block.

Used to replace the text upon completion of editing.")

(defvar-local fence-edit-mark-end nil
  "A marker at the end of the edited text block.

Used to replace the text upon completion of editing.")

(defvar-local fence-edit-block-indent nil
  "The indentation of the first line.

Used to strip and replace the indentation upon beginning/completion of editing.")

(defvar fence-edit-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-c") 'fence-edit-exit)
    (define-key map (kbd "C-c '")   'fence-edit-exit)
    (define-key map (kbd "C-c C-k") 'fence-edit-abort)
    (define-key map (kbd "C-x C-s") 'fence-edit-save)
    map)
  "The keymap used in ‘fence-edit-mode’.")

(define-minor-mode fence-edit-mode
  "A minor mode used when editing a fence-edit block."
  nil "Fence-Edit"
  fence-edit-mode-map)

(defvar fence-edit-mode-hook nil
  "Hook run when fence-edit has set the block's language mode.

You may want to use this to disable language mode configurations that
don't work well in the snippet view.")

(defun fence-edit-mode-configure ()
  "Configure the fence-edit edit buffer."
  (add-hook 'kill-buffer-hook
            #'(lambda () (delete-overlay fence-edit-overlay)) nil 'local))

(add-hook 'fence-edit-mode-hook 'fence-edit-mode-configure)

(defsubst fence-edit-set-local (var value)
  "Make VAR local in current buffer and set it to VALUE."
  (set (make-local-variable var) value))

(defun fence-edit--make-edit-buffer-name (base-buffer-name lang)
  "Make an edit buffer name from BASE-BUFFER-NAME and LANG."
  (concat "*Narrowed Edit " base-buffer-name "[" lang "]*"))

(defun fence-edit--next-line-beginning-position-at-pos (pos)
  "Return the position of the beginning of the line after the line at POS.

Used to find the position at which the code to edit begins, covering
for a common case where the block start regexp doesn't match the
ending line break and that break gets sucked into the block of code to
edit."
  (interactive)
  (save-excursion
    (goto-char pos)
    (forward-line)
    (line-beginning-position)))

(defun fence-edit--get-block-around-point ()
  "Return metadata about block surrounding point.

Return nil if no block is found."
  (save-excursion
    (beginning-of-line)
    (let ((pos (point))
          (blocks fence-edit-blocks)
          block re-start re-end lang-id start end lang)
      (catch 'exit
        (while (setq block (pop blocks))
          (save-excursion
            (setq re-start (car block)
                  re-end (nth 1 block)
                  lang-id (nth 2 block))
            (if (or (looking-at re-start)
                    (re-search-backward re-start nil t))
                (progn
                  (setq start (fence-edit--next-line-beginning-position-at-pos (match-end 0))
                        lang (if (integerp lang-id)
                                 (match-string lang-id)
                               (symbol-name lang-id)))
                  (if (and (and (goto-char (match-end 0))
                                (re-search-forward re-end nil t))
                           (>= (match-beginning 0) pos))
                      (throw 'exit `(,start ,(match-beginning 0) ,lang)))))))))))

(defun fence-edit--get-mode-for-lang (lang)
  "Try to get a mode function from language name LANG.

The assumption is that language `LANG' has a mode `LANG-mode'."
  (let ((mode-name (intern (concat lang "-mode"))))
    (if (fboundp mode-name)
        mode-name
      (if (assoc lang fence-edit-lang-modes)
          (cdr (assoc lang fence-edit-lang-modes))
        fence-edit-default-mode))))

(defun fence-edit-code-at-point ()
  "Look for a code block at point and, if found, edit it."
  (interactive)
  (let* ((block (fence-edit--get-block-around-point))
         (pos (point))
         (beg (make-marker))
         (end (copy-marker (make-marker) t))
         (block-indent "")
         edit-point lang code mode ovl edit-buffer vars first-line)
    (if block
        (progn
          (setq beg (move-marker beg (car block))
                end (move-marker end (nth 1 block))
                edit-point (1+ (- pos beg))
                lang (nth 2 block)
                code (buffer-substring-no-properties beg end)
                mode (fence-edit--get-mode-for-lang lang)
                ovl (make-overlay beg end)
                edit-buffer (generate-new-buffer
                             (fence-edit--make-edit-buffer-name (buffer-name) lang)))
          (window-configuration-to-register fence-edit-window-layout)
          (if (string-match-p (rx "\n" string-end) code)
              (setq code (replace-regexp-in-string (rx "\n" string-end) "" code)))
          (setq first-line (car (split-string code "\n")))
          (string-match "^[[:blank:]]*" first-line)
          (setq block-indent (match-string 0 first-line))
          (setq code (replace-regexp-in-string (concat "^" block-indent) "" code))
          (overlay-put ovl 'edit-buffer edit-buffer)
          (overlay-put ovl 'face 'secondary-selection)
          (overlay-put ovl :read-only "Please don't.")
          (switch-to-buffer-other-window edit-buffer t)
          (insert code)
          (remove-text-properties (point-min) (point-max)
                                  '(display nil invisible nil intangible nil))
          (condition-case e
              (funcall mode)
            (error
             (message "Language mode `%s' fails with: %S" mode (nth 1 e))))
          (fence-edit-mode)
          (fence-edit-set-local 'fence-edit-editor t)
          (fence-edit-set-local 'fence-edit-mark-beg beg)
          (fence-edit-set-local 'fence-edit-mark-end end)
          (fence-edit-set-local 'fence-edit-block-indent block-indent)
          (fence-edit-set-local 'fence-edit-overlay ovl)
          (fence-edit-set-local 'header-line-format "Press C-c ' (C-c apostrophe) to save, C-c C-k to abort.")
          (goto-char edit-point)
          (set-buffer-modified-p nil)))))

(defun fence-edit--guard-edit-buffer ()
  "Throw an error if current buffer doesn't look like an edit buffer."
  (unless (bound-and-true-p fence-edit-editor)
    (error "This is not a fence-edit editor; something is wrong")))

(defun fence-edit--abandon-edit-buffer (dest-buffer)
  "Trash the edit buffer and switch to DEST-BUFFER.

The edit buffer is expected to be the current buffer."
  (interactive "P")
  (fence-edit--guard-edit-buffer)
  (let ((buffer (current-buffer)))
    (switch-to-buffer-other-window dest-buffer)
    (jump-to-register fence-edit-window-layout)
    (with-current-buffer buffer
      (set-buffer-modified-p nil))
    (kill-buffer buffer)))

(defun fence-edit-save () 
  "Save the original buffer with the new text."
  (interactive)
  (fence-edit--guard-edit-buffer)
  (let ((beg fence-edit-mark-beg))
    (fence-edit-replace)
    (set-buffer-modified-p nil)
    (with-current-buffer (marker-buffer beg)
      (save-buffer))))

(defun fence-edit-exit ()
  "Conclude editing, replacing the original text."
  (interactive)
  (fence-edit--guard-edit-buffer)
  (let ((code (buffer-string))
        (edit-point (point))
        (beg fence-edit-mark-beg)
        (end fence-edit-mark-end))
    (fence-edit-replace)
    (fence-edit--abandon-edit-buffer (marker-buffer beg))
    (goto-char (1- (+ beg edit-point)))
    (set-marker beg nil)
    (set-marker end nil)))

(defun fence-edit-replace ()
  "Continue editing, replacing the original text."
  (interactive)
  (fence-edit--guard-edit-buffer)
  (let ((buffer (current-buffer))
        (code (buffer-string))
        (beg fence-edit-mark-beg)
        (end fence-edit-mark-end)
        (block-indent fence-edit-block-indent)
        (edit-point (point))
        (ovl fence-edit-overlay))
    (if (not (string-match-p (rx "\n" string-end) code))
        (setq code (concat code "\n")))
    (setq code (replace-regexp-in-string "\n" (concat "\n" block-indent) code))
    (setq code (concat block-indent code))
    (setq code (replace-regexp-in-string (concat "\n" block-indent "$") "\n" code))
    (with-current-buffer (marker-buffer beg)
      (goto-char beg)
      (undo-boundary)
      (delete-region beg end)
      (insert code))))

(defun fence-edit-abort ()
  "Conclude editing, discarding the edited text."
  (interactive)
  (fence-edit--guard-edit-buffer)
  (let ((dest-buffer (marker-buffer fence-edit-mark-beg)))
    (fence-edit--abandon-edit-buffer dest-buffer)))

(provide 'fence-edit)
;;; fence-edit.el ends here
