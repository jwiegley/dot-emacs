;;; js3-foot.el

(eval-when-compile
  (require 'cl))

(require 'imenu)
(require 'cc-cmds)  ; for `c-fill-paragraph'


;;;###autoload (add-to-list 'auto-mode-alist '("\\.js$" . js3-mode))

;;;###autoload
(defun js3-mode ()
  "Major mode for editing JavaScript code.\n\n\\{js3-mode-map}"
  (interactive)
  (js3-mode-check-compat)
  (kill-all-local-variables)
  (set-syntax-table js3-mode-syntax-table)
  (use-local-map js3-mode-map)
  (make-local-variable 'comment-start)
  (make-local-variable 'comment-end)
  (make-local-variable 'comment-start-skip)
  (setq major-mode 'js3-mode
        mode-name "JavaScript-IDE"
        comment-start "//"  ; used by comment-region; don't change it
        comment-end "")
  (setq local-abbrev-table js3-mode-abbrev-table)
  (set (make-local-variable 'max-lisp-eval-depth)
       (max max-lisp-eval-depth 3000))
  (set (make-local-variable 'indent-line-function) #'js3-indent-line)
  (set (make-local-variable 'indent-tabs-mode) js3-indent-tabs-mode)

  ;; I tried an "improvement" to `c-fill-paragraph' that worked out badly
  ;; on most platforms other than the one I originally wrote it on.
  ;; So it's back to `c-fill-paragraph'.
  (set (make-local-variable 'fill-paragraph-function) #'c-fill-paragraph)

  (set (make-local-variable 'next-error-function) #'js3-next-error)
  (set (make-local-variable 'beginning-of-defun-function) #'js3-beginning-of-defun)
  (set (make-local-variable 'end-of-defun-function) #'js3-end-of-defun)
  ;; We un-confuse `parse-partial-sexp' by setting syntax-table properties
  ;; for characters inside regexp literals.
  (set (make-local-variable 'parse-sexp-lookup-properties) t)
  ;; this is necessary to make `show-paren-function' work properly
  (set (make-local-variable 'parse-sexp-ignore-comments) t)
  ;; needed for M-x rgrep, among other things
  (put 'js3-mode 'find-tag-default-function #'js3-mode-find-tag)

  ;; some variables needed by cc-engine for paragraph-fill, etc.
  (setq c-comment-prefix-regexp js3-comment-prefix-regexp
        c-comment-start-regexp "/[*/]\\|\\s|"
        c-line-comment-starter "//"
        c-paragraph-start js3-paragraph-start
        c-paragraph-separate "$"
        comment-start-skip js3-comment-start-skip
        c-syntactic-ws-start js3-syntactic-ws-start
        c-syntactic-ws-end js3-syntactic-ws-end
        c-syntactic-eol js3-syntactic-eol)

  (if js3-emacs22
      (let ((c-buffer-is-cc-mode t))
        ;; Copied from `js-mode'.  Also see Bug#6071.
        (make-local-variable 'paragraph-start)
        (make-local-variable 'paragraph-separate)
        (make-local-variable 'paragraph-ignore-fill-prefix)
        (make-local-variable 'adaptive-fill-mode)
        (make-local-variable 'adaptive-fill-regexp)
        (c-setup-paragraph-variables)))

  (setq js3-default-externs
        (append js3-ecma-262-externs
                (if js3-include-browser-externs
                    js3-browser-externs)
                (if js3-include-gears-externs
                    js3-gears-externs)
                (if js3-include-rhino-externs
                    js3-rhino-externs)))

  ;; We do our own syntax highlighting based on the parse tree.
  ;; However, we want minor modes that add keywords to highlight properly
  ;; (examples:  doxymacs, column-marker).
  ;; To customize highlighted keywords, use `font-lock-add-keywords'.
  (setq font-lock-defaults '(nil t))

  ;; Experiment:  make reparse-delay longer for longer files.
  (if (plusp js3-dynamic-idle-timer-adjust)
      (setq js3-idle-timer-delay
            (* js3-idle-timer-delay
               (/ (point-max) js3-dynamic-idle-timer-adjust))))

  (add-hook 'change-major-mode-hook #'js3-mode-exit nil t)
  (add-hook 'after-change-functions #'js3-mode-edit nil t)
  (setq imenu-create-index-function #'js3-mode-create-imenu-index)
  (imenu-add-to-menubar (concat "IM-" mode-name))
  (when js3-mirror-mode
    (js3-enter-mirror-mode))
  (add-to-invisibility-spec '(js3-outline . t))
  (set (make-local-variable 'line-move-ignore-invisible) t)
  (set (make-local-variable 'forward-sexp-function) #'js3-mode-forward-sexp)

  (if (fboundp 'run-mode-hooks)
      (run-mode-hooks 'js3-mode-hook)
    (run-hooks 'js3-mode-hook))

  (setq js3-mode-functions-hidden nil
        js3-mode-comments-hidden nil
        js3-mode-buffer-dirty-p t
        js3-mode-parsing nil)
  (if (not (zerop (buffer-size)))
      (js3-reparse)))

(defun js3-mode-check-compat ()
  "Signal an error if we can't run with this version of Emacs."
  (if (and js3-mode-must-byte-compile
           (not (byte-code-function-p (symbol-function 'js3-mode))))
      (error "You must byte-compile js3-mode before using it."))
  (if (and (boundp 'running-xemacs) running-xemacs)
      (error "js3-mode is not compatible with XEmacs"))
  (unless (>= emacs-major-version 21)
    (error "js3-mode requires GNU Emacs version 21 or higher")))

(defun js3-mode-exit ()
  (interactive)
  (when js3-mode-node-overlay
    (delete-overlay js3-mode-node-overlay)
    (setq js3-mode-node-overlay nil))
  (js3-remove-overlays)
  (setq js3-mode-ast nil)
  (remove-hook 'change-major-mode-hook #'js3-mode-exit t)
  (remove-from-invisibility-spec '(js3-outline . t))
  (js3-mode-show-all)
  (js3-with-unmodifying-text-property-changes
   (js3-clear-face (point-min) (point-max))))

(defsubst js3-mode-reset-timer ()
  (if js3-mode-parse-timer
      (cancel-timer js3-mode-parse-timer))
  (setq js3-mode-parsing nil)
  (setq js3-mode-parse-timer
        (run-with-idle-timer js3-idle-timer-delay nil #'js3-reparse)))

(defun js3-mode-edit (beg end len)
  "Schedule a new parse after buffer is edited.
Also clears the `js3-magic' bit on autoinserted parens/brackets
if the edit occurred on a line different from the magic paren."
  (let* ((magic-pos (next-single-property-change (point-min) 'js3-magic))
         (line (if magic-pos (line-number-at-pos magic-pos))))
    (and line
         (or (/= (line-number-at-pos beg) line)
             (and (> 0 len)
                  (/= (line-number-at-pos end) line)))
         (js3-mode-mundanify-parens)))
  (setq js3-mode-buffer-dirty-p t)
  (js3-mode-hide-overlay)
  (js3-mode-reset-timer))

(defun js3-reparse (&optional force)
  "Re-parse current buffer after user finishes some data entry.
If we get any user input while parsing, including cursor motion,
we discard the parse and reschedule it.  If FORCE is nil, then the
buffer will only rebuild its `js3-mode-ast' if the buffer is dirty."
  (let (time
        interrupted-p
        (js3-compiler-strict-mode js3-mode-show-strict-warnings))
    (unless js3-mode-parsing
      (setq js3-mode-parsing t)
      (unwind-protect
          (when (or js3-mode-buffer-dirty-p force)
            (js3-remove-overlays)
            (js3-with-unmodifying-text-property-changes
             (setq js3-mode-buffer-dirty-p nil
                   js3-mode-fontifications nil
                   js3-mode-deferred-properties nil)
             (if js3-mode-verbose-parse-p
                 (message "parsing..."))
             (setq time
                   (js3-time
                    (setq interrupted-p
                          (catch 'interrupted
                            (setq js3-mode-ast (js3-parse))
                            ;; if parsing is interrupted, comments and regex
                            ;; literals stay ignored by `parse-partial-sexp'
                            (remove-text-properties (point-min) (point-max)
                                                    '(syntax-table))
                            (js3-mode-apply-deferred-properties)
                            (js3-mode-remove-suppressed-warnings)
                            (js3-mode-show-warnings)
                            (js3-mode-show-errors)
                            (js3-mode-highlight-magic-parens)
                            (if (>= js3-highlight-level 1)
                                (js3-highlight-jsdoc js3-mode-ast))
                            nil))))
             (if interrupted-p
                 (progn
                   ;; unfinished parse => try again
                   (setq js3-mode-buffer-dirty-p t)
                   (js3-mode-reset-timer))
               (if js3-mode-verbose-parse-p
                   (message "Parse time: %s" time)))))
        ;; finally
        (setq js3-mode-parsing nil)
        (unless interrupted-p
          (setq js3-mode-parse-timer nil))))))

(defun js3-mode-show-node ()
  "Debugging aid:  highlight selected AST node on mouse click."
  (interactive)
  (let ((node (js3-node-at-point))
        beg
        end)
    (when js3-mode-show-overlay
      (if (null node)
          (message "No node found at location %s" (point))
        (setq beg (js3-node-abs-pos node)
              end (+ beg (js3-node-len node)))
        (if js3-mode-node-overlay
            (move-overlay js3-mode-node-overlay beg end)
          (setq js3-mode-node-overlay (make-overlay beg end))
          (overlay-put js3-mode-node-overlay 'font-lock-face 'highlight))
        (js3-with-unmodifying-text-property-changes
         (put-text-property beg end 'point-left #'js3-mode-hide-overlay))
        (message "%s, parent: %s"
                 (js3-node-short-name node)
                 (if (js3-node-parent node)
                     (js3-node-short-name (js3-node-parent node))
                   "nil"))))))

(defun js3-mode-hide-overlay (&optional p1 p2)
  "Remove the debugging overlay when the point moves."
  (when js3-mode-node-overlay
    (let ((beg (overlay-start js3-mode-node-overlay))
          (end (overlay-end js3-mode-node-overlay)))
      ;; Sometimes we're called spuriously.
      (unless (and p2
                   (>= p2 beg)
                   (<= p2 end))
        (js3-with-unmodifying-text-property-changes
         (remove-text-properties beg end '(point-left nil)))
        (delete-overlay js3-mode-node-overlay)
        (setq js3-mode-node-overlay nil)))))

(defun js3-mode-reset ()
  "Debugging helper; resets everything."
  (interactive)
  (js3-mode-exit)
  (js3-mode))

(defsubst js3-mode-show-warn-or-err (e face)
  "Highlight a warning or error E with FACE.
E is a list of ((MSG-KEY MSG-ARG) BEG END)."
  (let* ((key (first e))
         (beg (second e))
         (end (+ beg (third e)))
         ;; Don't inadvertently go out of bounds.
         (beg (max (point-min) (min beg (point-max))))
         (end (max (point-min) (min end (point-max))))
         (js3-highlight-level 3)    ; so js3-set-face is sure to fire
         (ovl (make-overlay beg end)))
    (overlay-put ovl 'font-lock-face face)
    (overlay-put ovl 'js3-error t)
    (put-text-property beg end 'help-echo (js3-get-msg key))
    (put-text-property beg end 'point-entered #'js3-echo-error)))

(defun js3-remove-overlays ()
  "Remove overlays from buffer that have a `js3-error' property."
  (let ((beg (point-min))
        (end (point-max)))
    (save-excursion
      (dolist (o (overlays-in beg end))
        (when (overlay-get o 'js3-error)
          (delete-overlay o))))))

(defun js3-error-at-point (&optional pos)
  "Return non-nil if there's an error overlay at POS.
Defaults to point."
  (loop with pos = (or pos (point))
        for o in (overlays-at pos)
        thereis (overlay-get o 'js3-error)))

(defun js3-mode-apply-deferred-properties ()
  "Apply fontifications and other text properties recorded during parsing."
  (when (plusp js3-highlight-level)
    ;; We defer clearing faces as long as possible to eliminate flashing.
    (js3-clear-face (point-min) (point-max))
    ;; Have to reverse the recorded fontifications list so that errors
    ;; and warnings overwrite the normal fontifications.
    (dolist (f (nreverse js3-mode-fontifications))
      (put-text-property (first f) (second f) 'font-lock-face (third f)))
    (setq js3-mode-fontifications nil))
  (dolist (p js3-mode-deferred-properties)
    (apply #'put-text-property p))
  (setq js3-mode-deferred-properties nil))

(defun js3-mode-show-errors ()
  "Highlight syntax errors."
  (when js3-mode-show-parse-errors
    (dolist (e (js3-ast-root-errors js3-mode-ast))
      (js3-mode-show-warn-or-err e 'js3-error-face))))

(defun js3-mode-remove-suppressed-warnings ()
  "Take suppressed warnings out of the AST warnings list.
This ensures that the counts and `next-error' are correct."
  (setf (js3-ast-root-warnings js3-mode-ast)
        (js3-delete-if
         (lambda (e)
           (let ((key (caar e)))
             (or
              (and (not js3-strict-trailing-comma-warning)
                   (string-match "trailing\\.comma" key))
              (and (not js3-strict-cond-assign-warning)
                   (string= key "msg.equal.as.assign"))
              (and js3-missing-semi-one-line-override
                   (string= key "msg.missing.semi")
                   (let* ((beg (second e))
                          (node (js3-node-at-point beg))
                          (fn (js3-mode-find-parent-fn node))
                          (body (and fn (js3-function-node-body fn)))
                          (lc (and body (js3-node-abs-pos body)))
                          (rc (and lc (+ lc (js3-node-len body)))))
                     (and fn
                          (or (null body)
                              (save-excursion
                                (goto-char beg)
                                (and (js3-same-line lc)
                                     (js3-same-line rc))))))))))
         (js3-ast-root-warnings js3-mode-ast))))

(defun js3-mode-show-warnings ()
  "Highlight strict-mode warnings."
  (when js3-mode-show-strict-warnings
    (dolist (e (js3-ast-root-warnings js3-mode-ast))
      (js3-mode-show-warn-or-err e 'js3-warning-face))))

(defun js3-echo-error (old-point new-point)
  "Called by point-motion hooks."
  (let ((msg (get-text-property new-point 'help-echo)))
    (when (and (stringp msg)
               (not (active-minibuffer-window))
               (not (current-message)))
      (message msg))))

(defalias 'js3-echo-help #'js3-echo-error)

(defun js3-enter-key ()
  "Handle user pressing the Enter key."
  (interactive)
  (let ((parse-status (save-excursion
                        (parse-partial-sexp (point-min) (point)))))
    (cond
     ;; check if inside a string
     ((nth 3 parse-status)
      (if (nth 5 parse-status)
          (js3-mode-split-string-with-backslash)
        (js3-mode-split-string parse-status)))
     ;; check if inside a block comment
     ((nth 4 parse-status)
      (js3-mode-extend-comment))
     (t
      ;; should probably figure out what the mode-map says we should do
      (if (and js3-indent-on-enter-key
               (not (zerop (buffer-size))))
          (js3-indent-line))
      (delete-horizontal-space t)
      (insert "\n")
      (if js3-enter-indents-newline
          (js3-indent-line))))))

(defun js3-mode-split-string-with-backslash ()
  "Turn a newline after backslash in mid-string into backslash-newline-separated multiline string."
  (insert "\n")
  (js3-mode-force-backslash))

(defun js3-mode-force-backslash ()
  "Force backslash character after a line of non-terminated string."
  (let* ((parse-status
          (save-excursion
            (parse-partial-sexp (point-min) (line-end-position)))))
    (when (and
           (not (nth 5 parse-status))
           (nth 3 parse-status))
      (save-excursion
        (end-of-line)
        (insert "\\")))))

(defun js3-mode-split-string (parse-status)
  "Turn a newline in mid-string into a string concatenation."
  (let* ((col (current-column))
         (quote-char (nth 3 parse-status))
         (quote-string (string quote-char))
         (string-beg (nth 8 parse-status))
         (indent (save-match-data
                   (or
                    (save-excursion
                      (back-to-indentation)
                      (if (looking-at "\\+")
                          (current-column)))
                    (save-excursion
                      (goto-char string-beg)
                      (if (looking-back "\\+\\s-+" nil)
                          (goto-char (match-beginning 0)))
                      (current-column))))))
    (insert quote-char "\n")
    (indent-to indent)
    (insert "+ " quote-string)
    (when (eolp)
      (insert quote-string)
      (backward-char 1))))

(defun js3-mode-extend-comment ()
  "Indent the line and, when inside a comment block, add comment prefix."
  (let (star single col first-line needs-close)
    (save-excursion
      (back-to-indentation)
      (cond
       ((looking-at "\\*[^/]")
        (setq star t
              col (current-column)))
       ((looking-at "/\\*")
        (setq star t
              first-line t
              col (1+ (current-column))))
       ((looking-at "//")
        (setq single t
              col (current-column)))))
    ;; Heuristic for whether we need to close the comment:
    ;; if we've got a parse error here, assume it's an unterminated
    ;; comment.
    (setq needs-close
          (or
           (eq (get-text-property (1- (point)) 'point-entered)
               'js3-echo-error)
           ;; The heuristic above doesn't work well when we're
           ;; creating a comment and there's another one downstream,
           ;; as our parser thinks this one ends at the end of the
           ;; next one.  (You can have a /* inside a js block comment.)
           ;; So just close it if the next non-ws char isn't a *.
           (and first-line
                (eolp)
                (save-excursion
                  (skip-chars-forward " \t\r\n")
                  (not (eq (char-after) ?*))))))
    (insert "\n")
    (cond
     (star
      (indent-to col)
      (insert "* ")
      (if (and first-line needs-close)
          (save-excursion
            (insert "\n")
            (indent-to col)
            (insert "*/"))))
     ((and single
           (save-excursion
             (and (zerop (forward-line 1))
                  (looking-at "\\s-*//"))))
      (indent-to col)
      (insert "// "))
     (js3-enter-indents-newline
      (js3-indent-line)))))

(defun js3-fill-string (beg quote)
  "Line-wrap a single-line string into a multi-line string.
BEG is the string beginning, QUOTE is the quote char."
  (let* ((squote (string quote))
         (end (if (re-search-forward (concat "[^\\]" squote)
                                     (point-at-eol) t)
                  (1+ (match-beginning 0))
                (point-at-eol)))
         (tag (make-marker))
         (fill-column (- fill-column 4)))  ; make room
    (unwind-protect
        (progn
          (move-marker tag end)
          (fill-paragraph nil)
          (goto-char beg)
          (while (not (js3-same-line tag))
            (goto-char (point-at-eol))
            (insert squote)
            (when (zerop (forward-line 1))
              (back-to-indentation)
              (if (looking-at (concat squote "\\s-*$"))
                  (progn
                    (setq end (point-at-eol))
                    (forward-line -1)
                    (delete-region (point-at-eol) end))
                (insert "+ " squote)))))
      (move-marker tag nil))))

(defun js3-fill-comment (parse-status arg)
  "Fill-paragraph in a block comment."
  (let* ((beg (nth 8 parse-status))
         (end (save-excursion
                (goto-char beg)
                (re-search-forward "[^\\]\\*/" nil t)))
         indent
         end-marker)
    (when end
      (setq end-marker (make-marker))
      (move-marker end-marker end))
    (when (and end js3-mode-squeeze-spaces)
      (save-excursion
        (save-restriction
          (narrow-to-region beg end)
          (goto-char (point-min))
          (while (re-search-forward "[ \t][ \t]+" nil t)
            (replace-match " ")))))
    ;; `c-fill-paragraph' doesn't indent the continuation stars properly
    ;; if the comment isn't left-justified.  They align to the first star
    ;; on the first continuation line after the comment-open, so we make
    ;; sure the first continuation line has the proper indentation.
    (save-excursion
      (goto-char beg)
      (setq indent (1+ (current-column)))
      (goto-char (point-at-eol))
      (skip-chars-forward " \t\r\n")
      (indent-line-to indent)

      ;; Invoke `c-fill-paragraph' from the first continuation line,
      ;; since it provides better results.  Otherwise if you're on the
      ;; last line, it doesn't prefix with stars the way you'd expect.
      ;; TODO:  write our own fill function that works in Emacs 21
      (let ((fill-paragraph-function 'c-fill-paragraph))
        (c-fill-paragraph arg)))

    ;; last line is typically indented wrong, so fix it
    (when end-marker
      (save-excursion
        (goto-char end-marker)
        (js3-indent-line)))))

(defun js3-beginning-of-line ()
  "Toggles point between bol and first non-whitespace char in line.
Also moves past comment delimiters when inside comments."
  (interactive)
  (let (node beg)
    (cond
     ((bolp)
      (back-to-indentation))
     ((looking-at "//")
      (skip-chars-forward "/ \t"))
     ((and (eq (char-after) ?*)
           (setq node (js3-comment-at-point))
           (memq (js3-comment-node-format node) '(jsdoc block))
           (save-excursion
             (skip-chars-backward " \t")
             (bolp)))
      (skip-chars-forward "\* \t"))
     (t
      (goto-char (point-at-bol))))))

(defun js3-end-of-line ()
  "Toggles point between eol and last non-whitespace char in line."
  (interactive)
  (if (eolp)
      (skip-chars-backward " \t")
    (goto-char (point-at-eol))))

(defun js3-enter-mirror-mode()
  "Turns on mirror mode, where quotes, brackets etc are mirrored automatically
on insertion."
  (interactive)
  (define-key js3-mode-map (read-kbd-macro "{")  'js3-mode-match-curly)
  (define-key js3-mode-map (read-kbd-macro "}")  'js3-mode-magic-close-paren)
  (define-key js3-mode-map (read-kbd-macro "\"") 'js3-mode-match-double-quote)
  (define-key js3-mode-map (read-kbd-macro "'")  'js3-mode-match-single-quote)
  (define-key js3-mode-map (read-kbd-macro "(")  'js3-mode-match-paren)
  (define-key js3-mode-map (read-kbd-macro ")")  'js3-mode-magic-close-paren)
  (define-key js3-mode-map (read-kbd-macro "[")  'js3-mode-match-bracket)
  (define-key js3-mode-map (read-kbd-macro "]")  'js3-mode-magic-close-paren))

(defun js3-leave-mirror-mode()
  "Turns off mirror mode."
  (interactive)
  (dolist (key '("{" "\"" "'" "(" ")" "[" "]"))
    (define-key js3-mode-map (read-kbd-macro key) 'self-insert-command)))

(defsubst js3-mode-inside-string ()
  "Return non-nil if inside a string.
Actually returns the quote character that begins the string."
  (let ((parse-state (save-excursion
                       (parse-partial-sexp (point-min) (point)))))
    (nth 3 parse-state)))

(defsubst js3-mode-inside-comment-or-string ()
  "Return non-nil if inside a comment or string."
  (or
   (let ((comment-start
          (save-excursion
            (goto-char (point-at-bol))
            (if (re-search-forward "//" (point-at-eol) t)
                (match-beginning 0)))))
     (and comment-start
          (<= comment-start (point))))
   (let ((parse-state (save-excursion
                        (parse-partial-sexp (point-min) (point)))))
     (or (nth 3 parse-state)
         (nth 4 parse-state)))))

(defsubst js3-make-magic-delimiter (delim &optional pos)
  "Add `js3-magic' and `js3-magic-paren-face' to DELIM, a string.
Sets value of `js3-magic' text property to line number at POS."
  (propertize delim
              'js3-magic (line-number-at-pos pos)
              'font-lock-face 'js3-magic-paren-face))

(defun js3-mode-match-delimiter (open close)
  "Insert OPEN (a string) and possibly matching delimiter CLOSE.
The rule we use, which as far as we can tell is how Eclipse works,
is that we insert the match if we're not in a comment or string,
and the next non-whitespace character is either punctuation or
occurs on another line."
  (insert open)
  (when (and (looking-at "\\s-*\\([[:punct:]]\\|$\\)")
             (not (js3-mode-inside-comment-or-string)))
    (save-excursion
      (insert (js3-make-magic-delimiter close)))
    (when js3-auto-indent-p
      (js3-indent-line))))

(defun js3-mode-match-bracket ()
  "Insert matching bracket."
  (interactive)
  (js3-mode-match-delimiter "[" "]"))

(defun js3-mode-match-paren ()
  "Insert matching paren unless already inserted."
  (interactive)
  (js3-mode-match-delimiter "(" ")"))

(defun js3-mode-match-curly (arg)
  "Insert matching curly-brace.
With prefix arg, no formatting or indentation will occur -- the close-brace
is simply inserted directly at the point."
  (interactive "p")
  (let (try-pos)
    (cond
     (current-prefix-arg
      (js3-mode-match-delimiter "{" "}"))
     ((and js3-auto-insert-catch-block
           (setq try-pos (if (looking-back "\\s-*\\(try\\)\\s-*"
                                           (point-at-bol))
                             (match-beginning 1))))
      (js3-insert-catch-skel try-pos))
     (t
      ;; Otherwise try to do something smarter.
      (insert "{")
      (unless (or (not (looking-at "\\s-*$"))
                  (save-excursion
                    (skip-chars-forward " \t\r\n")
                    (and (looking-at "}")
                         (js3-error-at-point)))
                  (js3-mode-inside-comment-or-string))
        (undo-boundary)
        ;; absolutely mystifying bug:  when inserting the next "\n",
        ;; the buffer-undo-list is given two new entries:  the inserted range,
        ;; and the incorrect position of the point.  It's recorded incorrectly
        ;; as being before the opening "{", not after it.  But it's recorded
        ;; as the correct value if you're debugging `js3-mode-match-curly'
        ;; in edebug.  I have no idea why it's doing this, but incrementing
        ;; the inserted position fixes the problem, so that the undo takes us
        ;; back to just after the user-inserted "{".
        (insert "\n")
        (ignore-errors
         (incf (cadr buffer-undo-list)))
        (js3-indent-line)
        (save-excursion
          (insert "\n}")
          (js3-indent-line)))))))

(defun js3-insert-catch-skel (try-pos)
  "Complete a try/catch block after inserting a { following a try keyword.
Rationale is that a try always needs a catch or a finally, and the catch is
the more likely of the two.

TRY-POS is the buffer position of the try keyword.  The open-curly should
already have been inserted."
  (insert "{")
  (let ((try-col (save-excursion
                   (goto-char try-pos)
                   (current-column))))
    (insert "\n")
    (undo-boundary)
    (js3-indent-line) ;; indent the blank line where cursor will end up
    (save-excursion
      (insert "\n")
      (indent-to try-col)
      (insert "} catch (x) {\n\n")
      (indent-to try-col)
      (insert "}"))))

(defun js3-mode-highlight-magic-parens ()
  "Re-highlight magic parens after parsing nukes the 'face prop."
  (let ((beg (point-min))
        end)
    (while (setq beg (next-single-property-change beg 'js3-magic))
      (setq end (next-single-property-change (1+ beg) 'js3-magic))
      (if (get-text-property beg 'js3-magic)
          (js3-with-unmodifying-text-property-changes
           (put-text-property beg (or end (1+ beg))
                              'font-lock-face 'js3-magic-paren-face))))))

(defun js3-mode-mundanify-parens ()
  "Clear all magic parens and brackets."
  (let ((beg (point-min))
        end)
    (while (setq beg (next-single-property-change beg 'js3-magic))
      (setq end (next-single-property-change (1+ beg) 'js3-magic))
      (remove-text-properties beg (or end (1+ beg))
                              '(js3-magic face)))))

(defsubst js3-match-quote (quote-string)
  (let ((start-quote (js3-mode-inside-string)))
    (cond
     ;; inside a comment - don't do quote-matching, since we can't
     ;; reliably figure out if we're in a string inside the comment
     ((js3-comment-at-point)
      (insert quote-string))
     ((not start-quote)
      ;; not in string => insert matched quotes
      (insert quote-string)
      ;; exception:  if we're just before a word, don't double it.
      (unless (looking-at "[^ \t\r\n]")
        (save-excursion
          (insert quote-string))))
     ((looking-at quote-string)
      (if (looking-back "[^\\]\\\\" nil)
          (insert quote-string)
        (forward-char 1)))
     ((and js3-mode-escape-quotes
           (save-excursion
             (save-match-data
               (re-search-forward quote-string (point-at-eol) t))))
      ;; inside terminated string, escape quote (unless already escaped)
      (insert (if (looking-back "[^\\]\\\\" nil)
                  quote-string
                (concat "\\" quote-string))))
     (t
      (insert quote-string)))))        ; else terminate the string

(defun js3-mode-match-single-quote ()
  "Insert matching single-quote."
  (interactive)
  (let ((parse-status (parse-partial-sexp (point-min) (point))))
    ;; don't match inside comments, since apostrophe is more common
    (if (nth 4 parse-status)
        (insert "'")
      (js3-match-quote "'"))))

(defun js3-mode-match-double-quote ()
  "Insert matching double-quote."
  (interactive)
  (js3-match-quote "\""))

;; Eclipse works as follows:
;;  * type an open-paren and it auto-inserts close-paren
;;    - auto-inserted paren gets a green bracket
;;    - green bracket means typing close-paren there will skip it
;;  * if you insert any text on a different line, it turns off
(defun js3-mode-magic-close-paren ()
  "Skip over close-paren rather than inserting, where appropriate."
  (interactive)
  (let* ((here (point))
         (parse-status (parse-partial-sexp (point-min) here))
         (open-pos (nth 1 parse-status))
         (close last-input-event)
         (open (cond
                ((eq close ?\))
                 ?\()
                ((eq close ?\])
                 ?\[)
                ((eq close ?})
                 ?{)
                (t nil))))
    (if (and (eq (char-after) close)
             (eq open (char-after open-pos))
             (js3-same-line open-pos)
             (get-text-property here 'js3-magic))
        (progn
          (remove-text-properties here (1+ here) '(js3-magic face))
          (forward-char 1))
      (insert-char close 1))
    (blink-matching-open)))

(defun js3-mode-wait-for-parse (callback)
  "Invoke CALLBACK when parsing is finished.
If parsing is already finished, calls CALLBACK immediately."
  (if (not js3-mode-buffer-dirty-p)
      (funcall callback)
    (push callback js3-mode-pending-parse-callbacks)
    (add-hook 'js3-parse-finished-hook #'js3-mode-parse-finished)))

(defun js3-mode-parse-finished ()
  "Invoke callbacks in `js3-mode-pending-parse-callbacks'."
  ;; We can't let errors propagate up, since it prevents the
  ;; `js3-parse' method from completing normally and returning
  ;; the ast, which makes things mysteriously not work right.
  (unwind-protect
      (dolist (cb js3-mode-pending-parse-callbacks)
        (condition-case err
            (funcall cb)
          (error (message "%s" err))))
    (setq js3-mode-pending-parse-callbacks nil)))

(defun js3-mode-flag-region (from to flag)
  "Hide or show text from FROM to TO, according to FLAG.
If FLAG is nil then text is shown, while if FLAG is t the text is hidden.
Returns the created overlay if FLAG is non-nil."
  (remove-overlays from to 'invisible 'js3-outline)
  (when flag
    (let ((o (make-overlay from to)))
      (overlay-put o 'invisible 'js3-outline)
      (overlay-put o 'isearch-open-invisible
                   'js3-isearch-open-invisible)
      o)))

;; Function to be set as an outline-isearch-open-invisible' property
;; to the overlay that makes the outline invisible (see
;; `js3-mode-flag-region').
(defun js3-isearch-open-invisible (overlay)
  ;; We rely on the fact that isearch places point on the matched text.
  (js3-mode-show-element))

(defun js3-mode-invisible-overlay-bounds (&optional pos)
  "Return cons cell of bounds of folding overlay at POS.
Returns nil if not found."
  (let ((overlays (overlays-at (or pos (point))))
        o)
    (while (and overlays
                (not o))
      (if (overlay-get (car overlays) 'invisible)
          (setq o (car overlays))
        (setq overlays (cdr overlays))))
    (if o
        (cons (overlay-start o) (overlay-end o)))))

(defun js3-mode-function-at-point (&optional pos)
  "Return the innermost function node enclosing current point.
Returns nil if point is not in a function."
  (let ((node (js3-node-at-point pos)))
    (while (and node (not (js3-function-node-p node)))
      (setq node (js3-node-parent node)))
    (if (js3-function-node-p node)
        node)))

(defun js3-mode-toggle-element ()
  "Hide or show the foldable element at the point."
  (interactive)
  (let (comment fn pos)
    (save-excursion
      (save-match-data
        (cond
         ;; /* ... */ comment?
         ((js3-block-comment-p (setq comment (js3-comment-at-point)))
          (if (js3-mode-invisible-overlay-bounds
               (setq pos (+ 3 (js3-node-abs-pos comment))))
              (progn
                (goto-char pos)
                (js3-mode-show-element))
            (js3-mode-hide-element)))

         ;; //-comment?
         ((save-excursion
            (back-to-indentation)
            (looking-at js3-mode-//-comment-re))
          (js3-mode-toggle-//-comment))

         ;; function?
         ((setq fn (js3-mode-function-at-point))
          (setq pos (and (js3-function-node-body fn)
                         (js3-node-abs-pos (js3-function-node-body fn))))
          (goto-char (1+ pos))
          (if (js3-mode-invisible-overlay-bounds)
              (js3-mode-show-element)
            (js3-mode-hide-element)))
         (t
          (message "Nothing at point to hide or show")))))))

(defun js3-mode-hide-element ()
  "Fold/hide contents of a block, showing ellipses.
Show the hidden text with \\[js3-mode-show-element]."
  (interactive)
  (if js3-mode-buffer-dirty-p
      (js3-mode-wait-for-parse #'js3-mode-hide-element))
  (let (node body beg end)
    (cond
     ((js3-mode-invisible-overlay-bounds)
      (message "already hidden"))
     (t
      (setq node (js3-node-at-point))
      (cond
       ((js3-block-comment-p node)
        (js3-mode-hide-comment node))
       (t
        (while (and node (not (js3-function-node-p node)))
          (setq node (js3-node-parent node)))
        (if (and node
                 (setq body (js3-function-node-body node)))
            (progn
              (setq beg (js3-node-abs-pos body)
                    end (+ beg (js3-node-len body)))
              (js3-mode-flag-region (1+ beg) (1- end) 'hide))
          (message "No collapsable element found at point"))))))))

(defun js3-mode-show-element ()
  "Show the hidden element at current point."
  (interactive)
  (let ((bounds (js3-mode-invisible-overlay-bounds)))
    (if bounds
        (js3-mode-flag-region (car bounds) (cdr bounds) nil)
      (message "Nothing to un-hide"))))

(defun js3-mode-show-all ()
  "Show all of the text in the buffer."
  (interactive)
  (js3-mode-flag-region (point-min) (point-max) nil))

(defun js3-mode-toggle-hide-functions ()
  (interactive)
  (if js3-mode-functions-hidden
      (js3-mode-show-functions)
    (js3-mode-hide-functions)))

(defun js3-mode-hide-functions ()
  "Hides all non-nested function bodies in the buffer.
Use \\[js3-mode-show-all] to reveal them, or \\[js3-mode-show-element]
to open an individual entry."
  (interactive)
  (if js3-mode-buffer-dirty-p
      (js3-mode-wait-for-parse #'js3-mode-hide-functions))
  (if (null js3-mode-ast)
      (message "Oops - parsing failed")
    (setq js3-mode-functions-hidden t)
    (js3-visit-ast js3-mode-ast #'js3-mode-function-hider)))

(defun js3-mode-function-hider (n endp)
  (when (not endp)
    (let ((tt (js3-node-type n))
          body beg end)
      (cond
       ((and (= tt js3-FUNCTION)
             (setq body (js3-function-node-body n)))
        (setq beg (js3-node-abs-pos body)
              end (+ beg (js3-node-len body)))
        (js3-mode-flag-region (1+ beg) (1- end) 'hide)
        nil)   ; don't process children of function
       (t
        t))))) ; keep processing other AST nodes

(defun js3-mode-show-functions ()
  "Un-hide any folded function bodies in the buffer."
  (interactive)
  (setq js3-mode-functions-hidden nil)
  (save-excursion
    (goto-char (point-min))
    (while (/= (goto-char (next-overlay-change (point)))
               (point-max))
      (dolist (o (overlays-at (point)))
        (when (and (overlay-get o 'invisible)
                   (not (overlay-get o 'comment)))
          (js3-mode-flag-region (overlay-start o) (overlay-end o) nil))))))

(defun js3-mode-hide-comment (n)
  (let* ((head (if (eq (js3-comment-node-format n) 'jsdoc)
                   3                    ; /**
                 2))                    ; /*
         (beg (+ (js3-node-abs-pos n) head))
         (end (- (+ beg (js3-node-len n)) head 2))
         (o (js3-mode-flag-region beg end 'hide)))
    (overlay-put o 'comment t)))

(defun js3-mode-toggle-hide-comments ()
  "Folds all block comments in the buffer.
Use \\[js3-mode-show-all] to reveal them, or \\[js3-mode-show-element]
to open an individual entry."
  (interactive)
  (if js3-mode-comments-hidden
      (js3-mode-show-comments)
    (js3-mode-hide-comments)))

(defun js3-mode-hide-comments ()
  (interactive)
  (if js3-mode-buffer-dirty-p
      (js3-mode-wait-for-parse #'js3-mode-hide-comments))
  (if (null js3-mode-ast)
      (message "Oops - parsing failed")
    (setq js3-mode-comments-hidden t)
    (dolist (n (js3-ast-root-comments js3-mode-ast))
      (let ((format (js3-comment-node-format n)))
        (when (js3-block-comment-p n)
          (js3-mode-hide-comment n))))
    (js3-mode-hide-//-comments)))

(defsubst js3-mode-extend-//-comment (direction)
  "Find start or end of a block of similar //-comment lines.
DIRECTION is -1 to look back, 1 to look forward.
INDENT is the indentation level to match.
Returns the end-of-line position of the furthest adjacent
//-comment line with the same indentation as the current line.
If there is no such matching line, returns current end of line."
  (let ((pos (point-at-eol))
        (indent (current-indentation)))
    (save-excursion
      (save-match-data
        (while (and (zerop (forward-line direction))
                    (looking-at js3-mode-//-comment-re)
                    (eq indent (length (match-string 1))))
          (setq pos (point-at-eol)))
        pos))))

(defun js3-mode-hide-//-comments ()
  "Fold adjacent 1-line comments, showing only snippet of first one."
  (let (beg end)
    (save-excursion
      (save-match-data
        (goto-char (point-min))
        (while (re-search-forward js3-mode-//-comment-re nil t)
          (setq beg (point)
                end (js3-mode-extend-//-comment 1))
          (unless (eq beg end)
            (overlay-put (js3-mode-flag-region beg end 'hide)
                         'comment t))
          (goto-char end)
          (forward-char 1))))))

(defun js3-mode-toggle-//-comment ()
  "Fold or un-fold any multi-line //-comment at point.
Caller should have determined that this line starts with a //-comment."
  (let* ((beg (point-at-eol))
         (end beg))
    (save-excursion
      (goto-char end)
      (if (js3-mode-invisible-overlay-bounds)
          (js3-mode-show-element)
        ;; else hide the comment
        (setq beg (js3-mode-extend-//-comment -1)
              end (js3-mode-extend-//-comment 1))
        (unless (eq beg end)
          (overlay-put (js3-mode-flag-region beg end 'hide)
                       'comment t))))))

(defun js3-mode-show-comments ()
  "Un-hide any hidden comments, leaving other hidden elements alone."
  (interactive)
  (setq js3-mode-comments-hidden nil)
  (save-excursion
    (goto-char (point-min))
    (while (/= (goto-char (next-overlay-change (point)))
               (point-max))
      (dolist (o (overlays-at (point)))
        (when (overlay-get o 'comment)
          (js3-mode-flag-region (overlay-start o) (overlay-end o) nil))))))

(defun js3-mode-display-warnings-and-errors ()
  "Turn on display of warnings and errors."
  (interactive)
  (setq js3-mode-show-parse-errors t
        js3-mode-show-strict-warnings t)
  (js3-reparse 'force))

(defun js3-mode-hide-warnings-and-errors ()
  "Turn off display of warnings and errors."
  (interactive)
  (setq js3-mode-show-parse-errors nil
        js3-mode-show-strict-warnings nil)
  (js3-reparse 'force))

(defun js3-mode-toggle-warnings-and-errors ()
  "Toggle the display of warnings and errors.
Some users don't like having warnings/errors reported while they type."
  (interactive)
  (setq js3-mode-show-parse-errors (not js3-mode-show-parse-errors)
        js3-mode-show-strict-warnings (not js3-mode-show-strict-warnings))
  (if (called-interactively-p 'interactive)
      (message "warnings and errors %s"
               (if js3-mode-show-parse-errors
                   "enabled"
                 "disabled")))
  (js3-reparse 'force))

(defun js3-mode-customize ()
  (interactive)
  (customize-group 'js3-mode))

(defun js3-mode-forward-sexp (&optional arg)
  "Move forward across one statement or balanced expression.
With ARG, do it that many times.  Negative arg -N means
move backward across N balanced expressions."
  (interactive "p")
  (setq arg (or arg 1))
  (if js3-mode-buffer-dirty-p
      (js3-mode-wait-for-parse #'js3-mode-forward-sexp))
  (let (node end (start (point)))
    (cond
     ;; backward-sexp
     ;; could probably make this "better" for some cases:
     ;;  - if in statement block (e.g. function body), go to parent
     ;;  - infix exprs like (foo in bar) - maybe go to beginning
     ;;    of infix expr if in the right-side expression?
     ((and arg (minusp arg))
      (dotimes (i (- arg))
        (js3-backward-sws)
        (forward-char -1)  ; enter the node we backed up to
        (setq node (js3-node-at-point (point) t))
        (goto-char (if node
                       (js3-node-abs-pos node)
                     (point-min)))))
     (t
      ;; forward-sexp
      (js3-forward-sws)
      (dotimes (i arg)
        (js3-forward-sws)
        (setq node (js3-node-at-point (point) t)
              end (if node (+ (js3-node-abs-pos node)
                              (js3-node-len node))))
        (goto-char (or end (point-max))))))))

(defun js3-next-error (&optional arg reset)
  "Move to next parse error.
Typically invoked via \\[next-error].
ARG is the number of errors, forward or backward, to move.
RESET means start over from the beginning."
  (interactive "p")
  (if (or (null js3-mode-ast)
          (and (null (js3-ast-root-errors js3-mode-ast))
               (null (js3-ast-root-warnings js3-mode-ast))))
      (message "No errors")
    (when reset
      (goto-char (point-min)))
    (let* ((errs (copy-sequence
                  (append (js3-ast-root-errors js3-mode-ast)
                          (js3-ast-root-warnings js3-mode-ast))))
           (continue t)
           (start (point))
           (count (or arg 1))
           (backward (minusp count))
           (sorter (if backward '> '<))
           (stopper (if backward '< '>))
           (count (abs count))
           all-errs
           err)
      ;; sort by start position
      (setq errs (sort errs (lambda (e1 e2)
                              (funcall sorter (second e1) (second e2))))
            all-errs errs)
      ;; find nth error with pos > start
      (while (and errs continue)
        (when (funcall stopper (cadar errs) start)
          (setq err (car errs))
          (if (zerop (decf count))
              (setq continue nil)))
        (setq errs (cdr errs)))
      (if err
          (goto-char (second err))
        ;; wrap around to first error
        (goto-char (second (car all-errs)))
        ;; if we were already on it, echo msg again
        (if (= (point) start)
            (js3-echo-error (point) (point)))))))

(defun js3-down-mouse-3 ()
  "Make right-click move the point to the click location.
This makes right-click context menu operations a bit more intuitive.
The point will not move if the region is active, however, to avoid
destroying the region selection."
  (interactive)
  (when (and js3-move-point-on-right-click
             (not mark-active))
    (let ((e last-input-event))
      (ignore-errors
       (goto-char (cadadr e))))))

(defun js3-mode-create-imenu-index ()
  "Return an alist for `imenu--index-alist'."
  ;; This is built up in `js3-parse-record-imenu' during parsing.
  (when js3-mode-ast
    ;; if we have an ast but no recorder, they're requesting a rescan
    (unless js3-imenu-recorder
      (js3-reparse 'force))
    (prog1
        (js3-build-imenu-index)
      (setq js3-imenu-recorder nil
            js3-imenu-function-map nil))))

(defun js3-mode-find-tag ()
  "Replacement for `find-tag-default'.
`find-tag-default' returns a ridiculous answer inside comments."
  (let (beg end)
    (js3-with-underscore-as-word-syntax
     (save-excursion
       (if (and (not (looking-at "[A-Za-z0-9_$]"))
                (looking-back "[A-Za-z0-9_$]" nil))
           (setq beg (progn (forward-word -1) (point))
                 end (progn (forward-word 1) (point)))
         (setq beg (progn (forward-word 1) (point))
               end (progn (forward-word -1) (point))))
       (replace-regexp-in-string
        "[\"']" ""
        (buffer-substring-no-properties beg end))))))

(defun js3-mode-forward-sibling ()
  "Move to the end of the sibling following point in parent.
Returns non-nil if successful, or nil if there was no following sibling."
  (let* ((node (js3-node-at-point))
         (parent (js3-mode-find-enclosing-fn node))
         sib)
    (when (setq sib (js3-node-find-child-after (point) parent))
      (goto-char (+ (js3-node-abs-pos sib)
                    (js3-node-len sib))))))

(defun js3-mode-backward-sibling ()
  "Move to the beginning of the sibling node preceding point in parent.
Parent is defined as the enclosing script or function."
  (let* ((node (js3-node-at-point))
         (parent (js3-mode-find-enclosing-fn node))
         sib)
    (when (setq sib (js3-node-find-child-before (point) parent))
      (goto-char (js3-node-abs-pos sib)))))

(defun js3-beginning-of-defun ()
  "Go to line on which current function starts, and return non-nil.
If we're not in a function, go to beginning of previous script-level element."
  (interactive)
  (let ((parent (js3-node-parent-script-or-fn (js3-node-at-point)))
        pos sib)
    (cond
     ((and (js3-function-node-p parent)
           (not (eq (point) (setq pos (js3-node-abs-pos parent)))))
      (goto-char pos))
     (t
      (js3-mode-backward-sibling)))))

(defun js3-end-of-defun ()
  "Go to the char after the last position of the current function.
If we're not in a function, skips over the next script-level element."
  (interactive)
  (let ((parent (js3-node-parent-script-or-fn (js3-node-at-point))))
    (if (not (js3-function-node-p parent))
        ;; punt:  skip over next script-level element beyond point
        (js3-mode-forward-sibling)
      (goto-char (+ 1 (+ (js3-node-abs-pos parent)
                         (js3-node-len parent)))))))

(defun js3-mark-defun (&optional allow-extend)
  "Put mark at end of this function, point at beginning.
The function marked is the one that contains point.

Interactively, if this command is repeated,
or (in Transient Mark mode) if the mark is active,
it marks the next defun after the ones already marked."
  (interactive "p")
  (let (extended)
    (when (and allow-extend
               (or (and (eq last-command this-command) (mark t))
                   (and transient-mark-mode mark-active)))
      (let ((sib (save-excursion
                   (goto-char (mark))
                   (if (js3-mode-forward-sibling)
                       (point))))
            node)
        (if sib
            (progn
              (set-mark sib)
              (setq extended t))
          ;; no more siblings - try extending to enclosing node
          (goto-char (mark t)))))
    (when (not extended)
      (let ((node (js3-node-at-point (point) t)) ; skip comments
            ast fn stmt parent beg end)
        (when (js3-ast-root-p node)
          (setq ast node
                node (or (js3-node-find-child-after (point) node)
                         (js3-node-find-child-before (point) node))))
        ;; only mark whole buffer if we can't find any children
        (if (null node)
            (setq node ast))
        (if (js3-function-node-p node)
            (setq parent node)
          (setq fn (js3-mode-find-enclosing-fn node)
                stmt (if (or (null fn)
                             (js3-ast-root-p fn))
                         (js3-mode-find-first-stmt node))
                parent (or stmt fn)))
        (setq beg (js3-node-abs-pos parent)
              end (+ beg (js3-node-len parent)))
        (push-mark beg)
        (goto-char end)
        (exchange-point-and-mark)))))

(defun js3-narrow-to-defun ()
  "Narrow to the function enclosing point."
  (interactive)
  (let* ((node (js3-node-at-point (point) t))  ; skip comments
         (fn (if (js3-script-node-p node)
                 node
               (js3-mode-find-enclosing-fn node)))
         (beg (js3-node-abs-pos fn)))
    (unless (js3-ast-root-p fn)
      (narrow-to-region beg (+ beg (js3-node-len fn))))))

(defun js3-add-to-globals ()
  (interactive)
  (let ((var (word-at-point)))
    (when (not (member var js3-declared-globals))
      (save-excursion
        (goto-char 0)
        (when (not (looking-at "^/\\*\\s-*globals? "))
          (newline 1)
          (forward-line -1)
          (insert "/*global*/")
          (goto-char 0))
        (if (not (re-search-forward "[*]/" nil t))
            (message "Invalid global declaration")
          (delete-char -2)
          (when (not (looking-back " " nil))
            (insert " "))
          (insert (concat var " */")))))))

(defalias 'js3r 'js3-mode-reset)

(provide 'js3)
(provide 'js3-mode)

;;; js3-foot.el ends here

;;; js3-mode.el ends here
