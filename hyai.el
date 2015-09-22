;;; hyai.el --- Haskell Yet Another Indentation -*- lexical-binding: t -*-

;; Copyright (C) 2014-2015 by Iku Iwasa

;; Author:    Iku Iwasa <iku.iwasa@gmail.com>
;; URL:       https://github.com/iquiw/hyai
;; Version:   1.0.0
;; Package-Requires: ((cl-lib "0.5") (emacs "24"))

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; HYAI is an indentation minor mode for Haskell.
;;
;; To enable HYAI in `haskell-mode', add `hyai-mode' to `haskell-mode-hook'.
;;
;;     (add-hook 'haskell-mode-hook #'hyai-mode)
;;

;;; Code:

(require 'cl-lib)

(defconst hyai-basic-offset 4)
(defconst hyai-where-offset 2)

(defun hyai-indent-line (&optional inverse)
  "Indent the current line according to the current context.
If there are multiple indent candidates, they are rotated by pressing tab key.
If INVERSE is non-nil, rotation is performed in the reverse order."
  (pcase-let* ((cc (current-column))
               (ppss (syntax-ppss))
               (`(,offset . ,head) (hyai--current-offset-head))
               (indents)
               (nexts)
               (command (if inverse
                            #'hyai-indent-backward
                          #'indent-for-tab-command)))
    (cond
     ((string= head "-}")
      (forward-line 0)
      (indent-line-to (save-excursion
                        (hyai--goto-comment-start)
                        (current-column)))
      (when (> cc offset)
        (forward-char (- cc offset))))
     ((member head '("{-" "--"))
      (unless (hyai--in-comment-p ppss)
        (indent-line-to offset)))
     ((or (hyai--in-nestable-comment-p ppss)
          (hyai--in-multiline-string-p ppss))
      (hyai-indent-comment)
      (when (> cc offset)
        (forward-char (- cc offset))))
     (t
      (setq indents (hyai-indent-candidates head))
      (if (null indents)
          (indent-line-to offset)
        (cond
         (inverse (setq indents (nreverse indents)))
         ((hyai--previous-line-empty-p)
          (setq indents (hyai--cycle-zero-first indents))))
        (setq nexts (when (eq this-command command)
                      (cdr (member offset indents))))
        (indent-line-to (car (or nexts indents)))
        (when (> cc offset)
          (forward-char (- cc offset))))))))

(defun hyai-indent-backward ()
  "Indent the current line as `hyai-indent-line', but inversely."
  (interactive)
  (hyai-indent-line t))

(defun hyai-indent-comment ()
  "Indent the current line in nestable comment or multiline string."
  (pcase-let ((`(,offset . ,head) (save-excursion
                                    (forward-line -1)
                                    (hyai--current-offset-head))))
    (if (string= head "{-")
        (indent-line-to (+ offset 3))
      (indent-line-to offset))))

(defun hyai-indent-candidates (head)
  "Return list of indent candidates in the current line.
HEAD is the first token in the current line."
  (if (member head '("{-" "--"))
      '()
    (save-excursion
      (forward-line 0)
      (hyai--skip-space-backward)
      (if (bobp)
          '(0)
        (or (save-excursion (hyai--indent-candidates-from-current head))
            (save-excursion (hyai--indent-candidates-from-previous))
            (save-excursion (hyai--indent-candidates-from-backward)))))))

(defun hyai--indent-candidates-from-current (head)
  "Return list of indent candidates according to HEAD."
  (pcase head
    (`"module" '(0))
    (`"where" (if (hyai--search-token-backward nil '("where"))
                  (list (+ (current-indentation) hyai-basic-offset))
                (list (+ (current-indentation) hyai-where-offset))))

    (`"then" (hyai--offsetnize (hyai--search-token-backward nil '("if"))
                               hyai-basic-offset))
    (`"else" (let ((offset (hyai--search-token-backward nil '("then"))))
               (hyai--offsetnize
                (if (equal offset (current-indentation))
                    offset
                  (hyai--search-token-backward nil '("if"))))))

    (`"in" (hyai--offsetnize (hyai--search-token-backward nil '("let"))))

    (`"("
     (let (offset)
       (save-excursion
         (when (member (hyai--search-context) '("import" "module"))
           (setq offset (current-column))
           (list (+ offset hyai-basic-offset))))))

    (`"{"
     (list (+ (hyai--previous-offset) hyai-basic-offset)))

    (`")"
     (hyai--offsetnize (hyai--search-comma-bracket ?\))))

    (`"]"
     (hyai--offsetnize (hyai--search-comma-bracket ?\])))

    (`"}"
     (hyai--offsetnize (hyai--search-comma-bracket ?\})))

    (`","
     (hyai--offsetnize (hyai--search-comma-bracket ?,)))

    ((or `"->" `"=>")
     (let (limit)
       (or (hyai--offsetnize
            (save-excursion
              (prog1 (hyai--search-token-backward '("::") nil)
                (setq limit (point)))))
           (hyai--offsetnize (hyai--search-vertical limit t))
           (list hyai-basic-offset))))

    (`"|" (let (limit ctx offset)
            (save-excursion
              (setq ctx (hyai--search-context))
              (setq limit (point))
              (setq offset (current-indentation)))
            (if (equal ctx "data")
                (hyai--search-vertical-equal limit)
              (or (save-excursion (hyai--search-vertical limit))
                  (cond
                   ((equal ctx "where")
                    (list (+ offset hyai-where-offset hyai-basic-offset)))
                   ((equal ctx "case")
                    (list (+ (hyai--previous-offset) hyai-basic-offset)))
                   (t (list (+ (current-indentation) hyai-basic-offset))))))))))

(defun hyai--indent-candidates-from-previous ()
  "Return list of indent candidates according to the last token in previous line."
  (if (bobp)
      '(0)
    (cl-case (char-syntax (char-before))
      (?w (pcase (hyai--grab-syntax-backward "w")
            (`"do"
             (list (+ (current-indentation) hyai-basic-offset)))
            (`"where"
             (if (hyai--botp)
                 (list (+ (current-column) hyai-where-offset))
               (or (hyai--offsetnize
                    (hyai--search-token-backward nil '("where"))
                    hyai-basic-offset)
                   (if (looking-at-p "module")
                       (list (current-indentation))
                     (list (+ (current-indentation) hyai-basic-offset))))))
            (`"of"
             (let ((offset (hyai--search-token-backward nil '("case"))))
               (when offset
                 (mapcar (lambda (x) (+ x hyai-basic-offset))
                         (list (current-indentation) offset)))))
            ((or `"then" `"else")
             (if (hyai--botp)
                 (list (+ (current-column) hyai-basic-offset))
               (hyai--offsetnize
                (hyai--search-token-backward nil '("if"))
                hyai-basic-offset)))))

      (?. (pcase (hyai--grab-syntax-backward ".")
            (`"="
             (list (+ (current-indentation) hyai-basic-offset)))
            (`"->"
             (let ((off1 (hyai--search-equal-line))
                   (off2 (current-indentation)))
               (if off1
                   (list (+ off2 hyai-basic-offset) off1)
                 (list off2 (+ off2 hyai-basic-offset)))))
            (","
             (let* ((off1 (hyai--previous-offset))
                    (off2 (hyai--search-comma-bracket ?,)))
               (list (or (and off2
                              (progn
                                (forward-char)
                                (skip-syntax-forward " ")
                                (unless (eolp)
                                  (current-column))))
                         off1))))))

      (?\( (cl-case (char-before)
             (?\( (list (+ (current-column) 1)))
             ((?\{ ?\[)
              (let ((cc (current-column))
                    (offset (hyai--previous-offset)))
                (if (= offset (- cc 1))
                    (list (+ offset 2))
                  (list (+ offset hyai-basic-offset)))))))

      (?\) (cl-case (char-before)
             (?\) (when (equal (hyai--search-context) "import")
                    '(0))))))))

(defun hyai--indent-candidates-from-backward ()
  "Return list of indent candidates according to backward tokens."
  (pcase-let* ((`(,offs1 . ,token) (hyai--possible-offsets))
               (offs2)
               (`(,offset . ,head) (hyai--current-offset-head))
               (minoff (or (car offs1) offset))
               (poffset minoff))
    (if (and offs1 (member token '("(" "[" "{" "then")))
        offs1

      (when (equal token "else")
        (hyai--search-token-backward nil '("if"))
        (setq offset (current-column)))

      (unless offs1
        (push (+ offset hyai-basic-offset) offs1)
        (push offset offs1))

      (while (and (> offset hyai-basic-offset)
                  (>= (forward-line -1) 0))
        (when (and (< offset minoff) (< offset poffset)
                   (not (member head '("|" "->"))))
          (push offset offs2)
          (setq poffset offset))
        (pcase-let ((`(,o . ,h) (hyai--current-offset-head)))
          (setq offset o)
          (setq head h)))
      (when (and (= offset hyai-basic-offset)
                 (< offset minoff))
        (push offset offs2))
      (when (< 0 minoff)
        (push 0 offs2))
      (let ((result (append offs1 offs2)))
        (if (hyai--type-signature-p)
            (hyai--cycle-zero-first result)
          result)))))

(defun hyai--current-offset-head ()
  "Return cons of the first token and indent offset in the current line."
  (save-excursion
    (forward-line 0)
    (skip-syntax-forward " ")
    (if (eobp)
        (cons (current-column) "")
      (let* ((c (char-after))
             (cc (current-column))
             (head (cl-case (char-syntax c)
                     (?w (hyai--grab-syntax-forward "w"))
                     (?_ (hyai--grab-syntax-forward "_"))
                     (?\( (if (looking-at-p "{-") "{-" (string c)))
                     (?\) (string c))
                     (?. (if (looking-at-p "-}") "-}"
                           (hyai--grab-syntax-forward ".")))
                     (t ""))))
        (cons cc head)))))

(defun hyai--search-token-backward (symbols words)
  "Search token specified in SYMBOLS or WORDS backward."
  (skip-syntax-backward " >")
  (let (result)
    (hyai--process-syntax-backward
     (lambda (syn c)
       (cl-case syn
         (?> (if (/= (char-syntax (char-after)) ?\s)
                 'stop
               (backward-char)
               'next))
         (?w (cond
              ((null words)
               (skip-syntax-backward "w")
               nil)
              ((member (hyai--grab-syntax-backward "w") words)
               (setq result (current-column))
               'stop)
              (t 'next)))
         (?. (cond
              ((null symbols)
               (skip-syntax-backward ".")
               nil)
              ((member (hyai--grab-syntax-backward ".") symbols)
               (setq result (current-column))
               'stop)
              (t 'next))))))
    result))

(defun hyai--possible-offsets ()
  "Return cons of list of possible indent offsets and last token."
  (let (offs prev beg curr last-token)
    (hyai--process-syntax-backward
     (lambda (syn c)
       (cl-case syn
         (?\s (setq prev (current-column))
              (skip-syntax-backward " ")
              'next)
         (?w (setq curr (current-column))
             (setq last-token (hyai--grab-syntax-backward "w"))
             (cond
              ((member last-token '("let" "then" "else"))
               (push (or prev curr) offs) 'stop)
              (t 'next)))
         (?. (setq curr (current-column))
             (setq last-token (hyai--grab-syntax-backward "."))
             (when (member last-token '("=" "->" "<-" "::"))
               (push (or prev curr) offs)
               (setq beg (current-column)))
             'next)
         (?\( (setq curr (current-column))
              (setq last-token (string c))
              (push (if (= (char-syntax (char-after)) ?\s) prev curr) offs)
              'stop)
         (?> 'stop))))
    (setq curr (current-indentation))
    (cons
     (cond
      ((and beg (/= beg curr) (/= curr 0))
       (cons curr offs))
      (t offs))
     last-token)))

(defun hyai--search-vertical (limit &optional after-blank)
  "Search vertical bar backward until LIMIT.
If AFTER-BLANK is non-nil, include the last space position in the result."
  (let (result prev)
    (hyai--process-syntax-backward
     (lambda (syn c)
       (cl-case syn
         (?\s (when after-blank
                (setq prev (current-column))
                (skip-syntax-backward " ")
                'next))
         (?. (let ((s (hyai--grab-syntax-backward ".")))
               (when (string= s "|")
                 (push (or prev (current-column)) result))
               'next))))
     limit)
    (cl-remove-duplicates result)))

(defun hyai--search-vertical-equal (limit)
  "Search vertical bar or equal backward until LIMIT.
Return the first non-space position after it."
  (let (result)
    (hyai--process-syntax-backward
     (lambda (syn c)
       (when (= syn ?.)
         (let ((s (hyai--grab-syntax-backward ".")) offset)
           (setq offset (current-column))
           (cond
            ((or (string= s "|")
                 (= offset (current-indentation)))
             (push offset result))
            ((string= s "=") (push offset result)))
           'next)))
     limit)
    (cl-remove-duplicates result)))

(defun hyai--search-equal-line ()
  "Search equal backward and return the first non-space position after it."
  (let (result)
    (hyai--process-syntax-backward
     (lambda (syn c)
       (cl-case syn
         (?> (setq result nil)
             'stop)
         (?\s (setq result (current-column))
              (skip-syntax-backward " ")
              'next)
         (?. (if (string= (hyai--grab-syntax-backward ".") "=")
                 'stop
               'next)))))
    result))

(defun hyai--search-comma-bracket (origin)
  "Search comma or bracket backward and return the position.
ORIGIN is a charcter at the original position."
  (let (result)
    (hyai--process-syntax-backward
     (lambda (syn c)
       (cl-case syn
         (?\s (when (hyai--botp)
                (setq result (current-column)))
              nil)
         (?\( (backward-char)
              (cond
               ((null result) (setq result (current-column)))
               ((= origin ?,) (setq result (current-column)))
               ((= c ?\{) (setq result (current-indentation))))
              'stop)
         (?. (pcase (hyai--grab-syntax-backward ".")
               (`"|" (if (= origin ?,)
                         (progn (setq result (current-column)) 'stop)
                       'next))
               (`","
                (if (hyai--botp)
                    (progn (setq result (current-column)) 'stop)
                  (setq result nil) 'next))
               (_ 'next)))
         (?> (backward-char)
             (skip-syntax-backward " ")
             'next))))
    result))

(defun hyai--skip-space-backward ()
  "Skip whitespaces backward across lines."
  (hyai--process-syntax-backward
   (lambda (syn c)
     (cl-case syn
       (?\s (skip-syntax-backward " ")
            'next)
       (?> (backward-char)
           (skip-syntax-backward " ")
           'next)
       (t 'stop)))))

(defun hyai--process-syntax-backward (callback &optional limit)
  "Perform syntax-aware string processing backward.
CALLBACK is called with syntax and character and should return 'stop, 'next
or nil.

 'stop: stop the processing.
 'next: skip to the previous char.
   nil: skip to the previous different syntax.

Process is stopped at the optoinal LIMIT position."
  (setq limit (or limit 0))
  (let (res)
    (while (and (null (eq res 'stop))
                (> (point) limit)
                (null (bobp)))
      (let* ((c (char-before))
             (syn (char-syntax c))
             (ppss (syntax-ppss))
             (comm-type (nth 4 ppss)))
        (cond
         (comm-type (hyai--goto-comment-start ppss))
         ((and (= c ?\}) (looking-back "-}"))
          (backward-char)
          (hyai--goto-comment-start ppss))
         (t
          (setq res (funcall callback syn c))
          (unless res
            (condition-case nil
                (cl-case syn
                  (?> (backward-char))
                  (?\) (backward-sexp))
                  (?\" (backward-sexp))
                  (t (if (= c ?')
                         (backward-sexp)
                       (skip-syntax-backward (string syn)))))
              (error (setq res 'stop))))))))))

(defun hyai--search-context ()
  "Search the current context backward.
Context is \"case\", \"where\" or the token that starts from the BOL."
  (let (result)
    (hyai--process-syntax-backward
     (lambda (syn c)
       (cl-case syn
         (?> (when (looking-at "^\\([^#[:space:]]+\\)")
               (setq result (match-string-no-properties 1))
               'stop))
         (?w (let ((token (hyai--grab-syntax-backward "w")))
               (when (or (bobp) (member token '("case" "where")))
                 (setq result token)
                 'stop))))))
    result))

(defun hyai--previous-offset ()
  "Return the previous offset with empty lines ignored."
  (skip-syntax-backward " >")
  (current-indentation))

(defun hyai--botp ()
  "Return non-nil if the current column is same as the current indentation."
  (= (current-column) (current-indentation)))

(defun hyai--in-multiline-string-p (ppss)
  "Return non-nil if the current point is in a multiline string using PPSS."
  (and (nth 3 ppss)
       (< (nth 8 ppss)
          (save-excursion (forward-line 0) (point)))))

(defun hyai--in-comment-p (ppss)
  "Return non-nil if the current point is in a comment using PPSS."
  (nth 4 ppss))

(defun hyai--in-nestable-comment-p (ppss)
  "Return non-nil if the current point is in a nestable comment using PPSS."
  (numberp (hyai--in-comment-p ppss)))

(defun hyai--goto-comment-start (&optional ppss)
  "Goto the point where the comment is started usinng PPSS.
If PPSS is not supplied, `syntax-ppss' is called internally."
  (let ((p (nth 8 (or ppss (syntax-ppss)))))
    (when p (goto-char p))))

(defun hyai--grab-syntax-forward (syntax)
  "Skip SYNTAX forward and return substring from the current point to it."
  (buffer-substring-no-properties
   (point)
   (progn (skip-syntax-forward syntax) (point))))

(defun hyai--grab-syntax-backward (syntax)
  "Skip SYNTAX backward and return substring from the current point to it."
  (buffer-substring-no-properties
   (point)
   (progn (skip-syntax-backward syntax) (point))))

(defun hyai--offsetnize (obj &optional plus)
  "Make list of offsets from OBJ.
If OBJ is a list, return new list with PLUS added for each element.
If OBJ is a number, return (OBJ + PLUS).
Otherwise, return nil."
  (setq plus (or plus 0))
  (cond
   ((listp obj) (mapcar (lambda (x) (+ x plus)) obj))
   ((numberp obj) (list (+ obj plus)))
   (t nil)))

(defun hyai--cycle-zero-first (offsets)
  "Return new list with modifying OFFSETS so that 0 is the first element.
If OFFSETS does not contain 0, return OFFSETS as is."
  (or
   (catch 'result
     (let (lst i (rest offsets))
       (while (setq i (car rest))
         (if (= i 0)
             (throw 'result (nconc rest (nreverse lst)))
           (push i lst))
         (setq rest (cdr rest)))))
   offsets))

(defun hyai--previous-line-empty-p ()
  "Return non-nil if the previous line is empty.
Comment only lines are ignored."
  (save-excursion
    (catch 'result
      (while (>= (forward-line -1) 0)
        (cond
         ((looking-at-p "^[[:space:]]*$")
          (throw 'result t))
         ((not (looking-at-p "^[[:space:]]*--"))
          (throw 'result nil)))))))

(defun hyai--type-signature-p ()
  "Return non-nil if type signature follows after the current point."
  (looking-at-p "^[[:word:][:punct:]]*[[:space:]]*::"))

(defvar hyai-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "<backtab>") #'hyai-indent-backward)
    map))

;;;###autoload
(define-minor-mode hyai-mode
  "Haskell Yet Another Indentation minor mode."
  :lighter " HYAI"
  :keymap hyai-mode-map
  (kill-local-variable 'indent-line-function)
  (when hyai-mode
    (set (make-local-variable 'indent-line-function) 'hyai-indent-line)))

(provide 'hyai)
;;; hyai.el ends here
