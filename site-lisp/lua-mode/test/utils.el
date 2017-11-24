;; -*- flycheck-disabled-checkers: (emacs-lisp-checkdoc) -*-

(require 'lua-mode)
(require 'buttercup)


(defun to-be-fontified-as (text faces)
  (let ((expected-faces (lua-mk-font-lock-faces faces))
        (result-faces (lua-get-line-faces text))
        (lineno 1))
    (when (/= (length expected-faces) (length result-faces))
        (buttercup-fail "\
Fontification check failed for:
%S
  Text contains %d lines, face list contains %d lines"
                        text (length result-faces) (length expected-faces)))
    (while expected-faces
      (unless (equal (car expected-faces) (car result-faces))
        (buttercup-fail "\
Fontification check failed on line %d for:
%S
  Result faces:   %S
  Expected faces: %S"
                        lineno text (car expected-faces) (car result-faces)))
      (setq expected-faces (cdr expected-faces)
            result-faces (cdr result-faces)
            lineno (1+ lineno)))
    (cons t "Fontification check passed")))


(buttercup-define-matcher :to-be-fontified-as (text faces)
  (to-be-fontified-as text faces))


(buttercup-define-matcher :to-precede (pos regexp)
  (save-excursion
    (goto-char pos)
    (let* ((precedes (looking-at regexp))
           (substr-begin (min (point-max) pos))
           (substr-end (min (point-max) (+ pos 100)))
           (found-after (format "%S" (buffer-substring-no-properties
                                      substr-begin substr-end ))))
      (goto-char substr-end)
      (when (eobp) (setq found-after (concat found-after " (end-of-buffer)")))
      (cons precedes (format "Expected %s to see after point at %s: %S.  Found: %s"
                             (if precedes "NOT" "")
                             pos regexp found-after)))))



(defun get-str-faces (str)
  "Find contiguous spans of non-default faces in STR.

E.g. for properly fontified Lua string \"local x = 100\" it should return
  '(\"local\" font-lock-keyword-face
    \"x\" font-lock-variable-name-face
    \"100\" font-lock-constant-face)
"
  (let ((pos 0)
        nextpos
        result prop newprop)
    (while pos
      (setq nextpos (next-property-change pos str)
            newprop (or (get-text-property pos 'face str)
                        (get-text-property pos 'font-lock-face str)))
      (when (not (equal prop newprop))
        (setq prop newprop)

        (when (listp prop)
          (when (eq (car-safe (last prop)) 'default)
            (setq prop (butlast prop)))
          (when (= 1 (length prop))
            (setq prop (car prop)))
          (when (symbolp prop)
            (when (eq prop 'default)
              (setq prop nil))))
        (when prop
          (push (substring-no-properties str pos nextpos) result)
          (push prop result)))
      (setq pos nextpos))
    (nreverse result)))

(defun lua-fontify-str (str)
  "Return string fontified according to lua-mode's rules"
  (with-temp-buffer
    (lua-mode)
    (insert str)
    (font-lock-fontify-buffer)
    (buffer-string)))

(defun get-buffer-line-faces ()
  (font-lock-fontify-buffer)
  (mapcar 'get-str-faces
          (split-string (buffer-string) "\n" nil)))


(defun lua-get-line-faces (str)
  "Find contiguous spans of non-default faces in each line of STR.

The result is a list of lists."
  (mapcar
   'get-str-faces
   (split-string (lua-fontify-str str) "\n" nil)))

(defun lua-mk-font-lock-faces (sym)
  "Decorate symbols with font-lock-%s-face recursively.

This is a mere typing/reading aid for lua-mode's font-lock tests."
  (or (cond
       ((symbolp sym) (intern-soft (format "font-lock-%s-face" (symbol-name sym))))
       ((listp sym) (mapcar 'lua-mk-font-lock-faces sym)))
      sym))

(defmacro should-lua-font-lock-equal (strs faces)
  `(should (equal (lua-get-line-faces ,strs)
                  (lua-mk-font-lock-faces ,faces))))

;; suppress fontification messages in emacs23 output
(setq font-lock-verbose nil)


(defun lua-join-lines (strs)
  (mapconcat (lambda (x) (concat x "\n")) strs ""))

(defmacro with-lua-buffer (&rest body)
  (declare (debug (&rest form)))
  `(with-temp-buffer
     (lua-mode)
     (set (make-local-variable 'lua-process) nil)
     (set (make-local-variable 'lua-process-buffer) nil)
     (font-lock-fontify-buffer)
     (pop-to-buffer (current-buffer))
     (unwind-protect
      (progn ,@body)
      (when (buffer-live-p lua-process-buffer)
        (lua-kill-process)))))

(defun lua-get-indented-strs (strs)
  (butlast
   (split-string
    (with-lua-buffer
     (insert (replace-regexp-in-string "^\\s *" "" (lua-join-lines strs)))
     (font-lock-fontify-buffer)
     (indent-region (point-min) (point-max))
     (buffer-substring-no-properties
      (point-min) (point-max)))
    "\n" nil)))

(defun lua-insert-goto-<> (strs)
  "Insert sequence of strings and put point in place of \"<>\"."
  (insert (lua-join-lines strs))
  (goto-char (point-min))
  (re-search-forward "<>")
  (replace-match "")
  ;; Inserted text may contain multiline constructs which will only be
  ;; recognized after fontification.
  (font-lock-fontify-buffer))

(defmacro lua-buffer-strs (&rest body)
  `(butlast
    (split-string
     (with-lua-buffer
      (progn ,@body)
      (buffer-substring-no-properties (point-min) (point-max)))
     "\n" nil)))

(defun lua--reindent-like (str)
  (let ((strs (split-string str "\n"))
        (indent-tabs-mode nil)
        (font-lock-verbose nil))
    (equal strs (lua-get-indented-strs strs))))
