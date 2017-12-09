;;; js3-util.el -- JavaScript utilities

;;; Code

(eval-when-compile
  (require 'cl))


;; Emacs21 compatibility, plus some stuff to avoid runtime dependency on CL

(unless (fboundp #'looking-back)
  (defun looking-back (regexp &optional limit greedy)
    "Return non-nil if text before point matches regular expression REGEXP.
Like `looking-at' except matches before point, and is slower.
LIMIT if non-nil speeds up the search by specifying a minimum
starting position, to avoid checking matches that would start
before LIMIT.

If GREEDY is non-nil, extend the match backwards as far as possible,
stopping when a single additional previous character cannot be part
of a match for REGEXP."
    (let ((start (point))
          (pos
           (save-excursion
             (and (re-search-backward (concat "\\(?:" regexp "\\)\\=") limit t)
                  (point)))))
      (if (and greedy pos)
          (save-restriction
            (narrow-to-region (point-min) start)
            (while (and (> pos (point-min))
                        (save-excursion
                          (goto-char pos)
                          (backward-char 1)
                          (looking-at (concat "\\(?:"  regexp "\\)\\'"))))
              (setq pos (1- pos)))
            (save-excursion
              (goto-char pos)
              (looking-at (concat "\\(?:"  regexp "\\)\\'")))))
      (not (null pos)))))

(unless (fboundp #'copy-overlay)
  (defun copy-overlay (o)
    "Return a copy of overlay O."
    (let ((o1 (make-overlay (overlay-start o) (overlay-end o)
                            ;; FIXME: there's no easy way to find the
                            ;; insertion-type of the two markers.
                            (overlay-buffer o)))
          (props (overlay-properties o)))
      (while props
        (overlay-put o1 (pop props) (pop props)))
      o1)))

(unless (fboundp #'remove-overlays)
  (defun remove-overlays (&optional beg end name val)
    "Clear BEG and END of overlays whose property NAME has value VAL.
Overlays might be moved and/or split.
BEG and END default respectively to the beginning and end of buffer."
    (unless beg (setq beg (point-min)))
    (unless end (setq end (point-max)))
    (if (< end beg)
        (setq beg (prog1 end (setq end beg))))
    (save-excursion
      (dolist (o (overlays-in beg end))
        (when (eq (overlay-get o name) val)
          ;; Either push this overlay outside beg...end
          ;; or split it to exclude beg...end
          ;; or delete it entirely (if it is contained in beg...end).
          (if (< (overlay-start o) beg)
              (if (> (overlay-end o) end)
                  (progn
                    (move-overlay (copy-overlay o)
                                  (overlay-start o) beg)
                    (move-overlay o end (overlay-end o)))
                (move-overlay o (overlay-start o) beg))
            (if (> (overlay-end o) end)
                (move-overlay o end (overlay-end o))
              (delete-overlay o))))))))

;; we don't want a runtime dependency on the CL package, so define
;; our own versions of these functions.

(defun js3-delete-if (predicate list)
  "Remove all items satisfying PREDICATE in LIST."
  (loop for item in list
        if (not (funcall predicate item))
        collect item))

(defun js3-position (element list)
  "Find 0-indexed position of ELEMENT in LIST comparing with `eq'.
Returns nil if element is not found in the list."
  (let ((count 0)
        found)
    (while (and list (not found))
      (if (eq element (car list))
          (setq found t)
        (setq count (1+ count)
              list (cdr list))))
    (if found count)))

(defun js3-find-if (predicate list)
  "Find first item satisfying PREDICATE in LIST."
  (let (result)
    (while (and list (not result))
      (if (funcall predicate (car list))
          (setq result (car list)))
      (setq list (cdr list)))
    result))

;;; end Emacs 21 compat

(defmacro js3-time (form)
  "Evaluate FORM, discard result, and return elapsed time in sec"
  (let ((beg (make-symbol "--js3-time-beg--"))
        (delta (make-symbol "--js3-time-end--")))
    `(let ((,beg (current-time))
           ,delta)
       ,form
       (/ (truncate (* (- (float-time (current-time))
                          (float-time ,beg))
                       10000))
          10000.0))))

(def-edebug-spec js3-time t)

(defsubst neq (expr1 expr2)
  "Return (not (eq expr1 expr2))."
  (not (eq expr1 expr2)))

(defsubst js3-same-line (pos)
  "Return t if POS is on the same line as current point."
  (and (>= pos (point-at-bol))
       (<= pos (point-at-eol))))

(defsubst js3-same-line-2 (p1 p2)
  "Return t if p1 is on the same line as p2."
  (save-excursion
    (goto-char p1)
    (js3-same-line p2)))

(defun js3-code-bug ()
  "Signal an error when we encounter an unexpected code path."
  (error "failed assertion"))

(defsubst js3-record-text-property (beg end prop value)
  "Record a text property to set when parsing finishes."
  (push (list beg end prop value) js3-mode-deferred-properties))

;; I'd like to associate errors with nodes, but for now the
;; easiest thing to do is get the context info from the last token.
(defsubst js3-record-parse-error (msg &optional arg pos len)
  (push (list (list msg arg)
              (or pos js3-token-beg)
              (or len (- js3-token-end js3-token-beg)))
        js3-parsed-errors))

(defsubst js3-report-error (msg &optional msg-arg pos len)
  "Signal a syntax error or record a parse error."
  (if js3-recover-from-parse-errors
      (js3-record-parse-error msg msg-arg pos len)
    (signal 'js3-syntax-error
            (list msg
                  js3-ts-lineno
                  (save-excursion
                    (goto-char js3-ts-cursor)
                    (current-column))
                  js3-ts-hit-eof))))

(defsubst js3-report-warning (msg &optional msg-arg pos len)
  (if js3-compiler-report-warning-as-error
      (js3-report-error msg msg-arg pos len)
    (push (list (list msg msg-arg)
                (or pos js3-token-beg)
                (or len (- js3-token-end js3-token-beg)))
          js3-parsed-warnings)))

(defsubst js3-add-strict-warning (msg-id &optional msg-arg beg end)
  (if js3-compiler-strict-mode
      (js3-report-warning msg-id msg-arg beg
                          (and beg end (- end beg)))))

(put 'js3-syntax-error 'error-conditions
     '(error syntax-error js3-syntax-error))
(put 'js3-syntax-error 'error-message "Syntax error")

(put 'js3-parse-error 'error-conditions
     '(error parse-error js3-parse-error))
(put 'js3-parse-error 'error-message "Parse error")

(defmacro js3-clear-flag (flags flag)
  `(setq ,flags (logand ,flags (lognot ,flag))))

(defmacro js3-set-flag (flags flag)
  "Logical-or FLAG into FLAGS."
  `(setq ,flags (logior ,flags ,flag)))

(defsubst js3-flag-set-p (flags flag)
  (/= 0 (logand flags flag)))

(defsubst js3-flag-not-set-p (flags flag)
  (zerop (logand flags flag)))

;; Stolen shamelessly from James Clark's nxml-mode.
(defmacro js3-with-unmodifying-text-property-changes (&rest body)
  "Evaluate BODY without any text property changes modifying the buffer.
Any text properties changes happen as usual but the changes are not treated as
modifications to the buffer."
  (let ((modified (make-symbol "modified")))
    `(let ((,modified (buffer-modified-p))
           (inhibit-read-only t)
           (inhibit-modification-hooks t)
           (buffer-undo-list t)
           (deactivate-mark nil)
           ;; Apparently these avoid file locking problems.
           (buffer-file-name nil)
           (buffer-file-truename nil))
       (unwind-protect
           (progn ,@body)
         (unless ,modified
           (restore-buffer-modified-p nil))))))

(put 'js3-with-unmodifying-text-property-changes 'lisp-indent-function 0)
(def-edebug-spec js3-with-unmodifying-text-property-changes t)

(defmacro js3-with-underscore-as-word-syntax (&rest body)
  "Evaluate BODY with the _ character set to be word-syntax."
  (let ((old-syntax (make-symbol "old-syntax")))
    `(let ((,old-syntax (string (char-syntax ?_))))
       (unwind-protect
           (progn
             (modify-syntax-entry ?_ "w" js3-mode-syntax-table)
             ,@body)
         (modify-syntax-entry ?_ ,old-syntax js3-mode-syntax-table)))))

(put 'js3-with-underscore-as-word-syntax 'lisp-indent-function 0)
(def-edebug-spec js3-with-underscore-as-word-syntax t)

(defmacro with-buffer (buf form)
  "Executes FORM in buffer BUF.
BUF can be a buffer name or a buffer object.
If the buffer doesn't exist, it's created."
  `(let ((buffer (gentemp)))
     (setq buffer
           (if (stringp ,buf)
               (get-buffer-create ,buf)
             ,buf))
     (save-excursion
       (set-buffer buffer)
       ,form)))

(defsubst char-is-uppercase (c)
  "Return t if C is an uppercase character.
Handles unicode and latin chars properly."
  (/= c (downcase c)))

(defsubst char-is-lowercase (c)
  "Return t if C is an uppercase character.
Handles unicode and latin chars properly."
  (/= c (upcase c)))

(put 'with-buffer 'lisp-indent-function 1)
(def-edebug-spec with-buffer t)

(provide 'js3-util)

;;; js3-util.el ends here
