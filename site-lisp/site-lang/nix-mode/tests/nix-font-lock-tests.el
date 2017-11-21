;;  -*- lexical-binding: t -*-
(require 'ert)
(require 'nix-mode)

(defun check-syntax-and-face-match-range (beg end syntax face)
  "Check if all charaters between positions BEG and END have
syntax set to SYNTAX and face set to FACE.
If SYNTAX or FACE are set to t then any syntex respective face is
not checked."
  (let (all-syntaxes
        all-faces
        (syntax-classes "-.w_()'\"$\\/<>@!|")
        (text (buffer-substring-no-properties beg end)))
    (while (< beg end)
      (cl-pushnew (char-to-string (aref syntax-classes (syntax-class (syntax-after beg)))) all-syntaxes :test #'equal)
      (cl-pushnew (get-text-property beg 'face) all-faces :test #'equal)
      (setq beg (1+ beg)))
    (unless (eq syntax t)
      (should (equal (list text (mapconcat #'identity (sort (mapcar (lambda (syn) (char-to-string syn)) syntax) #'string<) ""))
                     (list text (mapconcat #'identity (sort all-syntaxes #'string<) "")))))
    (unless (eq face t)
      (should (equal (list text (list face))
                     (list text all-faces))))))

(defmacro with-nix-test-buffer (mode &rest body)
  "Run BODY in the context of a new buffer set to `nix-mode'.
Buffer is named *nix-mode-buffer*. It is not deleted
after a test as this aids interactive debugging."
  (declare (indent 1) (debug t))
  `(progn
     ;; we want to create buffer from scratch so that there are no
     ;; leftover state from the previous test
     (when (get-buffer "*nix-test-buffer*")
       (kill-buffer "*nix-test-buffer*"))
     (save-current-buffer
       (set-buffer (get-buffer-create "*nix-test-buffer*"))
       (funcall ,mode)
       ,@body)))

(defun check-properties (lines-or-contents props &optional mode)
  "Check if syntax properties and font-lock properties as set properly.
LINES is a list of strings that will be inserted to a new
buffer. Then PROPS is a list of tripples of (string syntax
face). String is searched for in the buffer and then is checked
if all of its characters have syntax and face. See
`check-syntax-and-face-match-range`."
  (with-nix-test-buffer (or mode #'nix-mode)
                        (if (consp lines-or-contents)
                            (dolist (line lines-or-contents)
                              (let ((pos (point)))
                                (insert line "\n")
                                (save-excursion
                                  ;; For some reason font-lock-fontify-region moves the
                                  ;; point. I do not think it is guaranteed it should not,
                                  ;; but then it might be our fault. Investigate later.
                                  (font-lock-fontify-region pos (point)))))
                          (insert lines-or-contents)
                          (font-lock-fontify-buffer))

                        (goto-char (point-min))
                        (dolist (prop props)
                          (cl-destructuring-bind (string syntax face) prop
                            (let ((case-fold-search nil))
                              (search-forward string))
                            (check-syntax-and-face-match-range (match-beginning 0) (match-end 0) syntax face)))))


(ert-deftest nix-equals-1 ()
  (check-properties
   '("pattern = 3")
   '(("pattern" t nix-attribute-face))))

(ert-deftest nix-equals-2 ()
  (check-properties
   '("pattern == 3")
   '(("pattern" t nil))))

;; Local Variables:
;; flycheck-disabled-checkers: (emacs-lisp-checkdoc)
;; End:
