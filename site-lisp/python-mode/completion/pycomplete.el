;;; Complete symbols at point using Pymacs.

;; Copyright (C) 2007  Skip Montanaro

;; Author:     Skip Montanaro
;; Maintainer: skip@pobox.com
;; Created:    Oct 2004
;; Keywords:   python pymacs emacs

;; This software is provided as-is, without express or implied warranty.
;; Permission to use, copy, modify, distribute or sell this software,
;; without fee, for any purpose and by any individual or organization, is
;; hereby granted, provided that the above copyright notice and this
;; paragraph appear in all copies.

;; Along with pycomplete.py this file allows programmers to complete Python
;; symbols within the current buffer.  See pycomplete.py for the Python side
;; of things and a short description of what to expect.

(require 'pymacs)

(pymacs-load "pycomplete")

(defun py-symbol-near-point ()
  "Return the first textual item to the nearest point."
  ;; alg stolen from etag.el
  (save-excursion
    (with-syntax-table py-dotted-expression-syntax-table
      (if (or (bobp) (not (memq (char-syntax (char-before)) '(?w ?_))))
          (while (not (looking-at "\\sw\\|\\s_\\|\\'"))
            (forward-char 1)))
      (while (looking-at "\\sw\\|\\s_")
        (forward-char 1))
      (if (re-search-backward "\\sw\\|\\s_" nil t)
          (progn (forward-char 1)
                 (buffer-substring (point)
                                   (progn (forward-sexp -1)
                                          (while (looking-at "\\s'")
                                            (forward-char 1))
                                          (point))))
        nil))))

(defun py-find-global-imports ()
  (save-excursion
    (let (first-class-or-def imports)
      (goto-char (point-min))
      (setq first-class-or-def
	    (re-search-forward "^ *\\(def\\|class\\) " nil t))
      (goto-char (point-min))
      (setq imports nil)
      (while (re-search-forward
	      "^\\(import \\|from \\([A-Za-z_][A-Za-z_0-9]*\\) import \\).*"
	      nil t)
	(setq imports (append imports
			      (list (buffer-substring
				     (match-beginning 0)
				     (match-end 0))))))
      imports)))

(defun py-complete ()
  (interactive)
  (let* ((pymacs-forget-mutability t)
         (symbol (py-symbol-near-point))
         (completions
          (pycomplete-pycomplete symbol
                                 (py-find-global-imports))))
    (cond ((null completions) ; no matching symbol
           (message "Can't find completion for \"%s\"" symbol)
           (ding))
          ((null (cdr completions))
           (if (string= "" (car completions))
               (tab-to-tab-stop)
             ;; sole completion
             (insert (car completions))))
          (t
           (message "Making completion list...")
           (with-output-to-temp-buffer "*PythonCompletions*"
             (display-completion-list completions))
           (message "Making completion list...%s" "done")))))

(provide 'pycomplete)
