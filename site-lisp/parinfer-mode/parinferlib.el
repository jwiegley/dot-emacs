;;; parinferlib.el --- a Parinfer implementation in Emacs Lisp
;; v1.0.0
;; https://github.com/oakmac/parinfer-elisp
;;
;; More information about Parinfer can be found here:
;; http://shaunlebron.github.io/parinfer/
;;
;; Copyright (c) 2016, Chris Oakman
;; Released under the ISC license
;; https://github.com/oakmac/parinfer-elisp/blob/master/LICENSE.md

;; NOTE: everything is namespaced under `parinferlib` with the assumption that
;;       Emacs extensions might use `parinfer`

;;------------------------------------------------------------------------------
;; Constants / Predicates
;;------------------------------------------------------------------------------

(defconst parinferlib--BACKSLASH "\\")
(defconst parinferlib--BLANK_SPACE " ")
(defconst parinferlib--DOUBLE_SPACE "  ")
(defconst parinferlib--DOUBLE_QUOTE "\"")
(defconst parinferlib--NEWLINE "\n")
(defconst parinferlib--LINE_ENDING_REGEX "\r?\n")
(defconst parinferlib--SEMICOLON ";")
(defconst parinferlib--TAB "\t")

;; A Stack Element is a Vector of 4 items (alphabetically ordered)
;; idx : item
;;   0 : ch
;;   1 : indentDelta
;;   2 : lineNo
;;   3 : x
(defconst parinferlib--CH_IDX 0)
(defconst parinferlib--INDENT_DELTA_IDX 1)
(defconst parinferlib--LINE_NO_IDX 2)
(defconst parinferlib--X_IDX 3)

;; determines if a line only contains a Paren Trail (possibly w/ a comment)
(defconst parinferlib--STANDALONE_PAREN_TRAIL "^[][:space:])}]*\\(;.*\\)?$")

(defconst parinferlib--PARENS (make-hash-table :test 'equal))
(puthash "{" "}" parinferlib--PARENS)
(puthash "}" "{" parinferlib--PARENS)
(puthash "[" "]" parinferlib--PARENS)
(puthash "]" "[" parinferlib--PARENS)
(puthash "(" ")" parinferlib--PARENS)
(puthash ")" "(" parinferlib--PARENS)

(defun parinferlib--empty? (stack)
  (zerop (length stack)))

(defun parinferlib--not-empty? (stack)
  (not (parinferlib--empty? stack)))

(defun parinferlib--open-paren? (ch)
  (or (string= "(" ch)
      (string= "{" ch)
      (string= "[" ch)))

(defun parinferlib--close-paren? (ch)
  (or (string= ")" ch)
      (string= "}" ch)
      (string= "]" ch)))

;;------------------------------------------------------------------------------
;; Result Structure
;;------------------------------------------------------------------------------

(defun parinferlib--create-initial-result (text mode options)
  (let ((lines-vector (vconcat (split-string text parinferlib--LINE_ENDING_REGEX)))
        (result (make-hash-table)))
    (puthash :mode mode result)

    (puthash :origText text result)
    (puthash :origLines lines-vector result)
    (puthash :origCursorX nil result)

    (puthash :lines (make-vector (length lines-vector) nil) result)
    (puthash :lineNo -1 result)
    (puthash :ch "" result)
    (puthash :x 0 result)

    (puthash :parenStack '() result)
    (puthash :tabStops '() result)

    (puthash :parenTrailLineNo nil result)
    (puthash :parenTrailStartX nil result)
    (puthash :parenTrailEndX nil result)
    (puthash :parenTrailOpeners '() result)

    (puthash :cursorX nil result)
    (puthash :cursorLine nil result)
    (puthash :cursorDx nil result)
    (puthash :previewCursorScope nil result)
    (puthash :canPreviewCursorScope nil result)

    (puthash :isInCode t result)
    (puthash :isEscaping nil result)
    (puthash :isInStr nil result)
    (puthash :isInComment nil result)
    (puthash :commentX nil result)

    (puthash :quoteDanger nil result)
    (puthash :trackingIndent nil result)
    (puthash :skipChar nil result)
    (puthash :success nil result)

    (puthash :maxIndent nil result)
    (puthash :indentDelta 0 result)

    (puthash :error nil result)

    ;; a plist of potential error positions
    (puthash :errorPosCache '() result)

    ;; merge options if they are valid
    (when (integerp (plist-get options :cursor-x))
      (puthash :cursorX (plist-get options :cursor-x) result)
      (puthash :origCursorX (plist-get options :cursor-x) result))
    (when (integerp (plist-get options :cursor-line))
      (puthash :cursorLine (plist-get options :cursor-line) result))
    (when (integerp (plist-get options :cursor-dx))
      (puthash :cursorDx (plist-get options :cursor-dx) result))
    (when (booleanp (plist-get options :preview-cursor-scope))
      (puthash :previewCursorScope (plist-get options :preview-cursor-scope) result))

    result))

;;------------------------------------------------------------------------------
;; Errors
;;------------------------------------------------------------------------------

(defconst parinferlib--ERR_QUOTE_DANGER "quote-danger")
(defconst parinferlib--ERR_EOL_BACKSLASH "eol-backslash")
(defconst parinferlib--ERR_UNCLOSED_QUOTE "unclosed-quote")
(defconst parinferlib--ERR_UNCLOSED_PAREN "unclosed-paren")

(defconst parinferlib--ERR_MESSAGES (make-hash-table :test 'equal))
(puthash parinferlib--ERR_QUOTE_DANGER   "Quotes must balanced inside comment blocks." parinferlib--ERR_MESSAGES)
(puthash parinferlib--ERR_EOL_BACKSLASH  "Line cannot end in a hanging backslash." parinferlib--ERR_MESSAGES)
(puthash parinferlib--ERR_UNCLOSED_QUOTE "String is missing a closing quote." parinferlib--ERR_MESSAGES)
(puthash parinferlib--ERR_UNCLOSED_PAREN "Unmatched open-paren." parinferlib--ERR_MESSAGES)

(defun parinferlib--cache-error-pos (result error-name line-no x)
  (let* ((error-cache (gethash :errorPosCache result))
         (position (list :line-no line-no :x x))
         (updated-error-cache (plist-put error-cache error-name position)))
    (puthash :errorPosCache updated-error-cache result)))

(defun parinferlib--create-error (result error-name line-no x)
  (let* ((error-cache (gethash :errorPosCache result))
         (error-msg (gethash error-name parinferlib--ERR_MESSAGES))
         (error-position (plist-get error-cache error-name)))
    (when (not line-no)
      (setq line-no (plist-get error-position :line-no)))
    (when (not x)
      (setq x (plist-get error-position :x)))

    ;; return a plist of the error
    (list :name error-name
          :message error-msg
          :line-no line-no
          :x x)))

;;------------------------------------------------------------------------------
;; String Operations
;;------------------------------------------------------------------------------

(defun parinferlib--replace-within-string (orig start end replace)
  (let* ((orig-length (length orig))
         (head (substring orig 0 start))
         (tail (if (>= end orig-length)
                 ""
                 (substring orig end))))
    (concat head replace tail)))

;;------------------------------------------------------------------------------
;; Line Operations
;;------------------------------------------------------------------------------

(defun parinferlib--cursor-affected? (result start end)
  (let ((cursor-x (gethash :cursorX result)))
    (if (and (equal cursor-x start)
             (equal cursor-x end))
        (zerop cursor-x)
      (>= cursor-x end))))

(defun parinferlib--shift-cursor-on-edit (result line-no start end replace)
  (let* ((old-length (- end start))
         (new-length (length replace))
         (dx (- new-length old-length))
         (cursor-line (gethash :cursorLine result))
         (cursor-x (gethash :cursorX result)))
    (when (and dx
               (not (zerop dx))
               (equal cursor-line line-no)
               cursor-x
               (parinferlib--cursor-affected? result start end))
      (puthash :cursorX (+ cursor-x dx) result))))

(defun parinferlib--replace-within-line (result line-no start end replace)
  (let* ((lines (gethash :lines result))
         (line (aref lines line-no))
         (new-line (parinferlib--replace-within-string line start end replace)))
    (aset lines line-no new-line)
    (parinferlib--shift-cursor-on-edit result line-no start end replace)))

(defun parinferlib--insert-within-line (result line-no idx insert)
  (parinferlib--replace-within-line result line-no idx idx insert))

(defun parinferlib--init-line (result line)
  (let* ((current-line-no (gethash :lineNo result))
         (new-line-no (1+ current-line-no))
         (lines (gethash :lines result)))
    (aset lines new-line-no line)

    (puthash :x 0 result)
    (puthash :lineNo new-line-no result)

    ;; reset line-specific state
    (puthash :commentX nil result)
    (puthash :indentDelta 0 result)))

;; if the current character has changed, commit it's change to the current line
(defun parinferlib--commit-char (result orig-ch)
  (let* ((line-no (gethash :lineNo result))
         (x (gethash :x result))
         (ch (gethash :ch result))
         (ch-length (length ch))
         (orig-ch-length (length orig-ch)))
    (when (not (string= orig-ch ch))
      (parinferlib--replace-within-line result line-no x (+ x orig-ch-length) ch))
    (puthash :x (+ x ch-length) result)))

;;------------------------------------------------------------------------------
;; Util
;;------------------------------------------------------------------------------

(defun parinferlib--clamp (val-n min-n max-n)
  (when min-n
    (setq val-n (if (> min-n val-n) min-n val-n)))
  (when max-n
    (setq val-n (if (< max-n val-n) max-n val-n)))
  val-n)

;;------------------------------------------------------------------------------
;; Character functions
;;------------------------------------------------------------------------------

(defun parinferlib--valid-close-paren? (paren-stack ch)
  (if (parinferlib--empty? paren-stack)
    nil
    (let* ((top-of-stack (car paren-stack))
           (top-of-stack-ch (aref top-of-stack parinferlib--CH_IDX)))
      (string= top-of-stack-ch (gethash ch parinferlib--PARENS)))))

(defun parinferlib--on-open-paren (result)
  (when (gethash :isInCode result)
    (let* ((new-stack-el (vector (gethash :ch result)
                                 (gethash :indentDelta result)
                                 (gethash :lineNo result)
                                 (gethash :x result)))
           (paren-stack (gethash :parenStack result))
           (new-paren-stack (cons new-stack-el paren-stack)))
      (puthash :parenStack new-paren-stack result))))

(defun parinferlib--on-matched-close-paren (result)
  (let* ((paren-stack (gethash :parenStack result))
         (opener (pop paren-stack))
         (opener-x (aref opener parinferlib--X_IDX))
         (result-x (gethash :x result))
         (openers (gethash :parenTrailOpeners result))
         (new-openers (cons opener openers)))
    (puthash :parenTrailEndX (1+ result-x) result)
    (puthash :parenTrailOpeners new-openers result)
    (puthash :maxIndent opener-x result)
    ;; the first element of paren-stack was removed when we called "pop" earlier
    (puthash :parenStack paren-stack result)))

(defun parinferlib--on-unmatched-close-paren (result)
  (puthash :ch "" result))

(defun parinferlib--on-close-paren (result)
  (when (gethash :isInCode result)
    (if (parinferlib--valid-close-paren? (gethash :parenStack result) (gethash :ch result))
      (parinferlib--on-matched-close-paren result)
      (parinferlib--on-unmatched-close-paren result))))

(defun parinferlib--on-tab (result)
  (when (gethash :isInCode result)
    (puthash :ch parinferlib--DOUBLE_SPACE result)))

(defun parinferlib--on-semicolon (result)
  (when (gethash :isInCode result)
    (puthash :isInComment t result)
    (puthash :commentX (gethash :x result) result)))

(defun parinferlib--on-newline (result)
  (puthash :isInComment nil result)
  (puthash :ch "" result))

(defun parinferlib--on-quote (result)
  (cond ((gethash :isInStr result)
         (puthash :isInStr nil result))

        ((gethash :isInComment result)
         (let ((quote-danger (gethash :quoteDanger result)))
           (puthash :quoteDanger (not quote-danger) result)
           (when (gethash :quoteDanger result)
             (let ((line-no (gethash :lineNo result))
                   (x (gethash :x result)))
               (parinferlib--cache-error-pos result parinferlib--ERR_QUOTE_DANGER line-no x)))))

        (t
         (let ((line-no (gethash :lineNo result))
               (x (gethash :x result)))
           (puthash :isInStr t result)
           (parinferlib--cache-error-pos result parinferlib--ERR_UNCLOSED_QUOTE line-no x)))))

(defun parinferlib--on-backslash (result)
  (puthash :isEscaping t result))

(defun parinferlib--after-backslash (result)
  (puthash :isEscaping nil result)
  (when (string= (gethash :ch result) parinferlib--NEWLINE)
    (when (gethash :isInCode result)
      (let ((line-no (gethash :lineNo result))
            (x (gethash :x result)))
        (throw 'parinferlib-error (parinferlib--create-error result parinferlib--ERR_EOL_BACKSLASH line-no (1- x)))))
    (parinferlib--on-newline result)))

(defun parinferlib--on-char (result)
  (let ((ch (gethash :ch result)))
    (cond ((gethash :isEscaping result)   (parinferlib--after-backslash result))
          ((parinferlib--open-paren? ch)  (parinferlib--on-open-paren result))
          ((parinferlib--close-paren? ch) (parinferlib--on-close-paren result))
          ((string= ch parinferlib--DOUBLE_QUOTE) (parinferlib--on-quote result))
          ((string= ch parinferlib--SEMICOLON)    (parinferlib--on-semicolon result))
          ((string= ch parinferlib--BACKSLASH)    (parinferlib--on-backslash result))
          ((string= ch parinferlib--TAB)          (parinferlib--on-tab result))
          ((string= ch parinferlib--NEWLINE)      (parinferlib--on-newline result))))
  (let ((in-comment? (gethash :isInComment result))
        (in-string? (gethash :isInStr result)))
    (puthash :isInCode (and (not in-comment?) (not in-string?)) result)))

;;------------------------------------------------------------------------------
;; Cursor functions
;;------------------------------------------------------------------------------

(defun parinferlib--cursor-on-left? (result)
  (let* ((line-no (gethash :lineNo result))
         (cursor-line (gethash :cursorLine result))
         (cursor-x (gethash :cursorX result))
         (result-x (gethash :x result)))
    (and (equal line-no cursor-line)
         cursor-x
         result-x
         (<= cursor-x result-x))))

(defun parinferlib--cursor-on-right? (result x)
  (let* ((line-no (gethash :lineNo result))
         (cursor-line (gethash :cursorLine result))
         (cursor-x (gethash :cursorX result)))
    (and (equal line-no cursor-line)
         cursor-x
         x
         (> cursor-x x))))

(defun parinferlib--cursor-in-comment? (result)
  (parinferlib--cursor-on-right? result (gethash :commentX result)))

(defun parinferlib--handle-cursor-delta (result)
  (let* ((cursor-dx (gethash :cursorDx result))
         (cursor-line (gethash :cursorLine result))
         (line-no (gethash :lineNo result))
         (cursor-x (gethash :cursorX result))
         (x (gethash :x result))
         (indent-delta (gethash :indentDelta result))
         (has-delta? (and cursor-dx
                          (equal cursor-line line-no)
                          (equal cursor-x x))))
    (when has-delta?
      (puthash :indentDelta (+ indent-delta cursor-dx) result))))

;;------------------------------------------------------------------------------
;; Paren Trail functions
;;------------------------------------------------------------------------------

(defun parinferlib--reset-paren-trail (result line-no x)
  (puthash :parenTrailLineNo line-no result)
  (puthash :parenTrailStartX x result)
  (puthash :parenTrailEndX x result)
  (puthash :parenTrailOpeners '() result)
  (puthash :maxIndent nil result))

(defun parinferlib--update-paren-trail-bounds (result)
  (let* ((lines (gethash :lines result))
         (line-no (gethash :lineNo result))
         (line (aref lines line-no))
         (x (gethash :x result))
         (prev-ch (if (> x 0)
                    (string (aref line (1- x)))
                    nil))
         (ch (gethash :ch result))
         (should-reset? (and (gethash :isInCode result)
                             (or (not (parinferlib--close-paren? ch))
                                 (string= prev-ch parinferlib--BACKSLASH))
                             (not (string= ch ""))
                             (or (not (string= ch parinferlib--BLANK_SPACE))
                                 (string= prev-ch parinferlib--BACKSLASH))
                             (not (string= ch parinferlib--DOUBLE_SPACE)))))
    (when should-reset?
      (parinferlib--reset-paren-trail result line-no (1+ x)))))

(defun parinferlib--clamp-paren-trail-to-cursor (result)
  (let* ((start-x (gethash :parenTrailStartX result))
         (end-x (gethash :parenTrailEndX result))
         (cursor-clamping? (and (parinferlib--cursor-on-right? result start-x)
                                (not (parinferlib--cursor-in-comment? result)))))
    (when cursor-clamping?
      (let* ((cursor-x (gethash :cursorX result))
             (new-start-x (max start-x cursor-x))
             (new-end-x (max end-x cursor-x))
             (line-no (gethash :lineNo result))
             (lines (gethash :lines result))
             (line (aref lines line-no))
             (remove-count 0)
             (i start-x))
        (while (< i new-start-x)
          (when (parinferlib--close-paren? (string (aref line i)))
            (setq remove-count (1+ remove-count)))
          (setq i (1+ i)))
        (when (> remove-count 0)
          (let* ((openers (gethash :parenTrailOpeners result))
                 (new-openers (nbutlast openers remove-count)))
            (puthash :parenTrailOpeners new-openers result)))
        (puthash :parenTrailStartX new-start-x result)
        (puthash :parenTrailEndX new-end-x result)))))

(defun parinferlib--pop-paren-trail (result)
  (let ((start-x (gethash :parenTrailStartX result))
        (end-x (gethash :parenTrailEndX result)))
    (when (not (equal start-x end-x))
      (let ((openers (gethash :parenTrailOpeners result))
            (paren-stack (gethash :parenStack result)))
        (while (parinferlib--not-empty? openers)
          (setq paren-stack (cons (pop openers) paren-stack)))
        (puthash :parenTrailOpeners openers result)
        (puthash :parenStack paren-stack result)))))

(defun parinferlib--correct-paren-trail (result indent-x)
  (let ((parens "")
        (paren-stack (gethash :parenStack result))
        (break? nil))
    (while (and (> (length paren-stack) 0)
                (not break?))
      (let* ((opener (car paren-stack))
             (opener-x (aref opener parinferlib--X_IDX))
             (opener-ch (aref opener parinferlib--CH_IDX)))
        (if (>= opener-x indent-x)
          (progn (pop paren-stack)
                 (setq parens (concat parens (gethash opener-ch parinferlib--PARENS))))
          (setq break? t))))
    (puthash :parenStack paren-stack result)
    (let ((paren-trail-line-no (gethash :parenTrailLineNo result))
          (paren-trail-start-x (gethash :parenTrailStartX result))
          (paren-trail-end-x (gethash :parenTrailEndX result)))
      (parinferlib--replace-within-line result paren-trail-line-no paren-trail-start-x paren-trail-end-x parens))))

(defun parinferlib--clean-paren-trail (result)
  (let* ((start-x (gethash :parenTrailStartX result))
         (end-x (gethash :parenTrailEndX result))
         (line-no (gethash :lineNo result))
         (paren-trail-line-no (gethash :parenTrailLineNo result))
         (exit-early? (or (equal start-x end-x)
                          (not (equal line-no paren-trail-line-no)))))
    (when (not exit-early?)
      (let* ((lines (gethash :lines result))
             (line (aref lines line-no))
             (new-trail "")
             (space-count 0)
             (i start-x))
        (while (< i end-x)
          (let ((ch (string (aref line i))))
            (if (parinferlib--close-paren? ch)
              (setq new-trail (concat new-trail ch))
              (setq space-count (1+ space-count))))
          (setq i (1+ i)))
        (when (> space-count 0)
          (parinferlib--replace-within-line result line-no start-x end-x new-trail)
          (let* ((paren-trail-end-x (gethash :parenTrailEndX result))
                 (new-pt-end-x (- paren-trail-end-x space-count)))
            (puthash :parenTrailEndX new-pt-end-x result)))))))

(defun parinferlib--append-paren-trail (result)
  (let* ((paren-stack (gethash :parenStack result))
         (opener (pop paren-stack))
         (opener-ch (aref opener parinferlib--CH_IDX))
         (opener-x (aref opener parinferlib--X_IDX))
         (close-ch (gethash opener-ch parinferlib--PARENS))
         (paren-trail-line-no (gethash :parenTrailLineNo result))
         (end-x (gethash :parenTrailEndX result)))
    (puthash :parenStack paren-stack result)
    (puthash :maxIndent opener-x result)
    (parinferlib--insert-within-line result paren-trail-line-no end-x close-ch)
    (puthash :parenTrailEndX (1+ end-x) result)))

(defun parinferlib--invalidate-paren-trail (result)
  (puthash :parenTrailLineNo nil result)
  (puthash :parenTrailStartX nil result)
  (puthash :parenTrailEndX nil result)
  (puthash :parenTrailOpeners '() result))

(defun parinferlib--finish-new-paren-trail (result)
  (let* ((in-str? (gethash :isInStr result))
         (mode (gethash :mode result))
         (line-no (gethash :lineNo result))
         (cursor-line (gethash :cursorLine result)))
    (cond
      (in-str?
       (parinferlib--invalidate-paren-trail result))

      ((equal mode :indent)
       (progn
         (parinferlib--clamp-paren-trail-to-cursor result)
         (parinferlib--pop-paren-trail result)))


      ((and (equal mode :paren)
            (not (equal line-no cursor-line)))
       (parinferlib--clean-paren-trail result)))))

;;------------------------------------------------------------------------------
;; Indentation functions
;;------------------------------------------------------------------------------

(defun parinferlib--correct-indent (result)
  (let* ((orig-indent (gethash :x result))
         (new-indent orig-indent)
         (min-indent 0)
         (max-indent (gethash :maxIndent result))
         (paren-stack (gethash :parenStack result))
         (opener (car paren-stack)))
    (when opener
      (let* ((opener-x (aref opener parinferlib--X_IDX))
             (opener-indent-delta (aref opener parinferlib--INDENT_DELTA_IDX)))
        (setq min-indent (1+ opener-x))
        (setq new-indent (+ new-indent opener-indent-delta))))
    (setq new-indent (parinferlib--clamp new-indent min-indent max-indent))
    (when (not (equal new-indent orig-indent))
      (let* ((indent-str (make-string new-indent (aref parinferlib--BLANK_SPACE 0)))
             (line-no (gethash :lineNo result))
             (indent-delta (gethash :indentDelta result))
             (new-indent-delta (+ indent-delta (- new-indent orig-indent))))
        (parinferlib--replace-within-line result line-no 0 orig-indent indent-str)
        (puthash :x new-indent result)
        (puthash :indentDelta new-indent-delta result)))))

(defun parinferlib--try-preview-cursor-scope (result)
  (when (gethash :canPreviewCursorScope result)
    (let ((cursor-x (gethash :cursorX result))
          (cursor-line (gethash :cursorLine result))
          (result-x (gethash :x result)))
      (when (> cursor-x result-x)
        (parinferlib--correct-paren-trail result cursor-x)
        (parinferlib--reset-paren-trail result cursor-line cursor-x))
      (puthash :canPreviewCursorScope nil result))))

(defun parinferlib--on-indent (result)
  (puthash :trackingIndent nil result)
  (when (gethash :quoteDanger result)
    (throw 'parinferlib-error (parinferlib--create-error result parinferlib--ERR_QUOTE_DANGER nil nil)))
  (let ((mode (gethash :mode result))
        (x (gethash :x result)))
    (when (equal mode :indent)
      (parinferlib--try-preview-cursor-scope result)
      (parinferlib--correct-paren-trail result x))
    (when (equal mode :paren)
      (parinferlib--correct-indent result))))

(defun parinferlib--on-leading-close-paren (result)
  (puthash :skipChar t result)
  (puthash :trackingIndent t result)
  (when (equal :paren (gethash :mode result))
    (let* ((paren-stack (gethash :parenStack result))
           (ch (gethash :ch result)))
      (when (parinferlib--valid-close-paren? paren-stack ch)
        (if (parinferlib--cursor-on-left? result)
          (progn (puthash :skipChar nil result)
                 (parinferlib--on-indent result))
          (parinferlib--append-paren-trail result))))))

(defun parinferlib--check-indent (result)
  (let ((ch (gethash :ch result))
        (result-x (gethash :x result))
        (cursor-x (gethash :cursorX result))
        (line-no (gethash :lineNo result)))
    (cond ((parinferlib--close-paren? ch)
           (parinferlib--on-leading-close-paren result))

          ((string= ch parinferlib--SEMICOLON)
           (puthash :trackingIndent nil result))

          ((not (or (string= ch parinferlib--NEWLINE)
                    (string= ch parinferlib--BLANK_SPACE)
                    (string= ch parinferlib--TAB)))
           (parinferlib--on-indent result)))))

(defun parinferlib--init-preview-cursor-scope (result)
  (let* ((preview-cursor-scope (gethash :previewCursorScope result))
         (cursor-line (gethash :cursorLine result))
         (line-no (gethash :lineNo result))
         (lines (gethash :lines result))
         (line (aref lines line-no))
         (semicolon-x (string-match ";" line))
         (cursor-x (gethash :cursorX result)))
    (when (and preview-cursor-scope
               (equal cursor-line line-no))
      (puthash :canPreviewCursorScope
               (and (gethash :trackingIndent result)
                    (string-match parinferlib--STANDALONE_PAREN_TRAIL line)
                    (or (not semicolon-x)
                        (<= cursor-x semicolon-x)))
               result))))

(defun parinferlib--init-indent (result)
  (let ((mode (gethash :mode result))
        (in-str? (gethash :isInStr result)))
    (when (equal :indent mode)
      ;; length of list > 0 means the same as the list not being null
      (puthash :trackingIndent (and (gethash :parenStack result)
                                    (not in-str?))
               result)
      (parinferlib--init-preview-cursor-scope result))
    (when (equal :paren mode)
       (puthash :trackingIndent (not in-str?) result))))

(defun parinferlib--set-tab-stops (result)
  (let ((cursor-line (gethash :cursorLine result))
        (line-no (gethash :lineNo result))
        (mode (gethash :mode result)))
    (when (and (equal cursor-line line-no)
               (equal :indent mode))
      (let ((current-stops (gethash :tabStops result))
            (new-stops '()))
        (dolist (stackel (gethash :parenStack result))
          (let ((new-stop (list :ch (aref stackel parinferlib--CH_IDX)
                                :line-no (aref stackel parinferlib--LINE_NO_IDX)
                                :x (aref stackel parinferlib--X_IDX))))
            (setq new-stops (push new-stop new-stops))))
        (puthash :tabStops (append current-stops new-stops) result)))))

;;------------------------------------------------------------------------------
;; High-level processing functions
;;------------------------------------------------------------------------------

(defun parinferlib--process-char (result ch)
  (let* ((orig-ch ch)
         (mode (gethash :mode result)))
    (puthash :ch ch result)
    (puthash :skipChar nil result)

    (when (equal :paren mode)
      (parinferlib--handle-cursor-delta result))

    (when (gethash :trackingIndent result)
      (parinferlib--check-indent result))

    (if (gethash :skipChar result)
      (puthash :ch "" result)
      (progn (parinferlib--on-char result)
             (parinferlib--update-paren-trail-bounds result)))

    (parinferlib--commit-char result orig-ch)))

(defun parinferlib--process-line (result line)
  (parinferlib--init-line result line)
  (parinferlib--init-indent result)
  (parinferlib--set-tab-stops result)
  (let* ((i 0)
         (chars (concat line parinferlib--NEWLINE))
         (chars-length (length chars)))
    (while (< i chars-length)
      (parinferlib--process-char result (string (aref chars i)))
      (setq i (1+ i))))

  (when (equal (gethash :lineNo result)
               (gethash :parenTrailLineNo result))
    (parinferlib--finish-new-paren-trail result)))

(defun parinferlib--finalize-result (result)
  (when (gethash :quoteDanger result)
    (throw 'parinferlib-error
           (parinferlib--create-error result parinferlib--ERR_QUOTE_DANGER nil nil)))
  (when (gethash :isInStr result)
    (throw 'parinferlib-error
           (parinferlib--create-error result parinferlib--ERR_UNCLOSED_QUOTE nil nil)))
  (let* ((paren-stack (gethash :parenStack result))
         (mode (gethash :mode result)))
    (when (parinferlib--not-empty? paren-stack)
      (when (equal mode :paren)
        (let* ((paren-stack (gethash :parenStack result))
               (opener (car paren-stack))
               (opener-line-no (aref opener parinferlib--LINE_NO_IDX))
               (opener-x (aref opener parinferlib--X_IDX)))
          (throw 'parinferlib-error
                 (parinferlib--create-error result parinferlib--ERR_UNCLOSED_PAREN opener-line-no opener-x))))
      (when (equal mode :indent)
        (puthash :x 0 result)
        (parinferlib--on-indent result))))
  (puthash :success t result))

(defun parinferlib--process-error (result err)
  (puthash :success nil result)
  (puthash :error err result))

(defun parinferlib--process-text (text mode options)
  (let* ((result (parinferlib--create-initial-result text mode options))
         (orig-lines (gethash :origLines result))
         (lines-length (length orig-lines))
         (i 0)
         (err (catch 'parinferlib-error
                (while (< i lines-length)
                  (parinferlib--process-line result (aref orig-lines i))
                  (setq i (1+ i)))
                (parinferlib--finalize-result result)
                nil)))
    (when err
      (parinferlib--process-error result err))
    result))

(defun parinferlib--get-changed-lines (result)
  (let* ((orig-lines (gethash :origLines result))
         (lines (gethash :lines result))
         (lines-length (min (length orig-lines) (length lines)))
         (changed-lines nil))
    (dotimes (i lines-length changed-lines)
      (let ((line (aref lines i))
            (orig-line (aref orig-lines i)))
        (unless (string= line orig-line)
          (push (list :line-no i :line line) changed-lines))))))

(defun parinferlib--public-result (result)
  "Return a plist for the Public API."
  (if (gethash :success result)
    (let* ((lines (gethash :lines result))
           (result-text (mapconcat 'identity lines parinferlib--NEWLINE))
           (cursor-x (gethash :cursorX result))
           (tab-stops (gethash :tabStops result)))
      (list :success t
            :cursor-x cursor-x
            :text result-text
            :changed-lines (parinferlib--get-changed-lines result)
            :tab-stops tab-stops))
    (let ((orig-text (gethash :origText result))
          (public-error (gethash :error result))
          (orig-cursor-x (gethash :origCursorX result)))
      (list :success nil
            :text orig-text
            :cursor-x orig-cursor-x
            :error public-error))))

;;------------------------------------------------------------------------------
;; Public API
;;------------------------------------------------------------------------------

(defun parinferlib-indent-mode (text &optional options)
  "Indent Mode public function"
  (let ((result (parinferlib--process-text text :indent options)))
    (parinferlib--public-result result)))

(defun parinferlib-paren-mode (text &optional options)
  "Paren Mode public function"
  (let ((result (parinferlib--process-text text :paren options)))
    (parinferlib--public-result result)))

(provide 'parinferlib)

;;; parinferlib.el ends here
