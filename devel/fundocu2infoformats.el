;;; -*- lexical-binding: t; -*- 

(defcustom py-devel-directory-out ""
  "Output directory when developing Python-mode. "
  :type 'string
  :group 'python-mode)

(defcustom py-devel-directory-in ""
  "Input directory when developing Python-mode. "
  :type 'string
  :group 'python-mode)

(defun python-components-mode-list-actives (&optional directory)
  "Return a list, which components will be loaded. "
  (interactive)
  (let ((directory (or directory default-directory))
        componentslist)
    (find-file (concat directory "python-components-mode.el"))
    (save-restriction
      (widen)
      (goto-char (point-min))
      (while (re-search-forward "^[ \t]*(require '\\([^)]+\\))" nil (quote move) 1)
        (when (save-match-data
                (string-match "python-components" (match-string-no-properties 0)))
          (add-to-list 'componentslist (prin1-to-string (match-string-no-properties 1)))))
      (dolist (ele componentslist)
        (find-file (concat directory ele)
                   (finds (concat ele ".el")))))))

(defun finds-from-programm ()
  (let ((directory-in (or (and (not (string= "" py-devel-directory-in)) py-devel-directory-in) default-directory))
        (directory-out (or (and (not (string= "" py-devel-directory-out)) py-devel-directory-out default-directory)) (concat default-directory "doc"))
        (erg (buffer-file-name))
        (buffer (current-buffer)))
    (message "Lade %s" erg)
    (find-file erg)
    (finds buffer directory-in directory-out)))

(defvar python-mode-el-doku-list (list "autopair/autopair.el" "python-mode.el" "completion/auto-complete-pycomplete.el" "completion/company-pycomplete.el" "completion/pycomplete.el" "pymacs.el" "extensions/py-smart-operator.el"))

(defun finds-alle ()
  "Write doku for files listet in python-mode-el-doku-list. "
  (interactive)
  (dolist (ele python-mode-el-doku-list)
    (when
        (and (load (concat "~/arbeit/emacs/python-modes/python-mode/" ele))
             (find-file (concat "~/arbeit/emacs/python-modes/python-mode/" ele)))
      (finds))))

(defun variable-docu (&optional buffer directory-in directory-out)
  "Writes all variable in BUFFER alongside with their documentation into directory \"doc\" as \*.org and \*rst file ."
  (interactive)
  (variables-prepare "docu"))

(defun variables-base-docu (oldbuf orgname reSTname directory-in directory-out)
  (save-restriction
    (let ((suffix (file-name-nondirectory (buffer-file-name)))
          variableslist)
      ;; (widen)
      (goto-char (point-min))
      ;; (eval-buffer)
      (while (and (not (eobp))(re-search-forward "^(defvar [[:alpha:]]\\|^(defcustom [[:alpha:]]\\|^(defconst [[:alpha:]]" nil t 1))
        (let* ((name (symbol-at-point))
               (docu (documentation-property name 'variable-documentation)))
                         ;; (documentation-property alias 'variable-documentation))))
          ;; (docu (get 'variable-documentation name)))
          (if docu
              (add-to-list 'variableslist (cons (prin1-to-string name) docu))
            (message "don't see docu string for %s" (prin1-to-string name))))
        ;; (add-to-list 'variableslist (list (match-string-no-properties 0)))

        (forward-line 1))
      (setq variableslist (nreverse variableslist))
;;       (with-temp-buffer
;;         (switch-to-buffer (current-buffer))
;;         (insert (concat ";; a list of " suffix " variables
;; \(setq " (replace-regexp-in-string "\\." "-" suffix) "-variables (quote "))
;;         (insert (prin1-to-string variableslist))
;;         (insert "))"))
        ;; (eval-buffer)
      (with-temp-buffer
        ;; org
        ;; (insert (concat (capitalize (substring oldbuf 0 (string-match "\." oldbuf))) " variables" "\n\n"))
        ;; (insert (concat suffix " variables\n\n"))
        (insert "Python-mode variables\n\n")
        (switch-to-buffer (current-buffer))
        (dolist (ele variableslist)
          (if (string-match "^;;; " (car ele))
              (unless (or (string-match "^;;; Constants\\|^;;; Commentary\\|^;;; Code\\|^;;; Macro definitions\\|^;;; Customization" (car ele)))

                (insert (concat (replace-regexp-in-string "^;;; " "* " (car ele)) "\n")))
            (insert (concat "\n** "(car ele) "\n"))
            (insert (concat "   " (cdr ele) "\n\n")))
        (richten)
        (sit-for 0.1)
        (write-file (concat directory-out "variables-" orgname))
        (find-file (concat directory-out "variables-" orgname))))

      (with-temp-buffer
        ;; reST
        (insert "Python-mode variables\n\n")
        ;; (insert (concat (make-string (length (concat (substring oldbuf 0 (string-match "\." oldbuf)) " variables")) ?\=) "\n\n"))
        (insert "====================\n\n")
        (dolist (ele variableslist)
          (insert (concat "\n" (car ele) "\n"))
          (insert (concat (make-string (length (car ele)) ?\-) "\n"))
          (insert (concat (cdr ele) "\n\n")))
        (richten)
        (sit-for 0.1)
        (write-file (concat directory-out "variables-" reSTname))
        (find-file (concat directory-out "variables-" reSTname))))))

(defun finds (&optional buffer directory-in directory-out)
  "Writes all commands in BUFFER alongside with their documentation into directory \"doc\" as \*.org and \*rst file ."
  (interactive)
  (let* ((oldbuf (buffer-name (or buffer (current-buffer))))
         ;; (file (buffer-file-name))
         (orgname (concat (substring oldbuf 0 (string-match "\\." oldbuf)) ".org"))
         (reSTname (concat (substring oldbuf 0 (string-match "\\." oldbuf)) ".rst"))
         (directory-in (or directory-in (and (not (string= "" py-devel-directory-in)) py-devel-directory-in) default-directory))
         (directory-out (or directory-out (expand-file-name finds-directory-out))))
    (finds-base oldbuf orgname reSTname directory-in directory-out)))

(defun finds-base (oldbuf orgname reSTname directory-in directory-out)
  (save-restriction
    (let ((suffix (file-name-nondirectory (buffer-file-name)))
          commandslist)
      ;; (widen)
      (goto-char (point-min))
      ;; (eval-buffer)
      (while (and (not (eobp))(re-search-forward "^(defun [[:alpha:]]\\|^;;; .+" nil t 1)) ;
                                                     (when (save-match-data (commandp (symbol-at-point)))
                                                       (let* ((name (symbol-at-point))
                                                              (docu (documentation name)))
                                                         (if docu
                                                             (add-to-list 'commandslist (cons (prin1-to-string name) docu))
                                                           (message "don't see docu string for %s" (prin1-to-string name)))))
                                                     ;; (add-to-list 'commandslist (list (match-string-no-properties 0)))

                                                     (forward-line 1))
      (setq commandslist (nreverse commandslist))
      (with-temp-buffer
        (switch-to-buffer (current-buffer))
        (insert (concat ";; a list of " suffix " commands
\(setq " (replace-regexp-in-string "\\." "-" suffix) "-commands (quote "))
        (insert (prin1-to-string commandslist))
        (insert "))")
        (eval-buffer))
      (with-temp-buffer
        ;; org
        ;; (insert (concat (capitalize (substring oldbuf 0 (string-match "\." oldbuf))) " commands" "\n\n"))
        (insert (concat suffix " commands\n\n"))
        (dolist (ele commandslist)
          (if (string-match "^;;; " (car ele))
              (unless (or (string-match "^;;; Constants\\|^;;; Commentary\\|^;;; Code\\|^;;; Macro definitions\\|^;;; Customization" (car ele)))

                (insert (concat (replace-regexp-in-string "^;;; " "* " (car ele)) "\n")))
            (insert (concat "** "(car ele) "\n"))
            (insert (concat "   " (cdr ele) "\n\n"))))
        (write-file (concat directory-out "commands-" orgname))
        (find-file (concat directory-out "commands-" orgname)))
      (with-temp-buffer
        ;; reST
        (insert "Commands\n\n")
        ;; (insert (concat (make-string (length (concat (substring oldbuf 0 (string-match "\." oldbuf)) " commands")) ?\=) "\n\n"))
        (insert "====================\n\n")
        (dolist (ele commandslist)
          (insert (concat (car ele) "\n"))
          (insert (concat (make-string (length (car ele)) ?\-) "\n"))
          (insert (concat (cdr ele) "\n\n")))
        (write-file (concat directory-out "commands-" reSTname))
        (find-file (concat directory-out "commands-" reSTname))))))

(defun write-defcustom-docus (&optional buffer directory-in directory-out)
  "Writes all customizable variables w/ documentation into directory \"doc\" as \*.org and \*rst file ."
  (interactive)
  (let* ((oldbuf (buffer-name (or buffer (current-buffer))))
         ;; (file (buffer-file-name))
         (orgname (concat (substring oldbuf 0 (string-match "\\." oldbuf)) ".org"))
         (reSTname (concat (substring oldbuf 0 (string-match "\\." oldbuf)) ".rst"))
         (directory-in (or directory-in (and (not (string= "" py-devel-directory-in)) py-devel-directory-in) default-directory))
         (directory-out (or directory-out (expand-file-name finds-directory-out))))
    (defcustom-docu-base oldbuf orgname reSTname directory-in directory-out)))

(defun defcustom-docu-base (oldbuf orgname reSTname directory-in directory-out)
  (save-restriction
    (let ((suffix (file-name-nondirectory (buffer-file-name)))
          varslist last)
      (goto-char (point-min))
      (while (and (not (eobp))(re-search-forward "^(defcustom [[:alpha:]]" nil t 1))
        (if (save-match-data (boundp (symbol-at-point)))
            (let* ((name (variable-at-point))
                   (docu
                    (or (documentation-property
                         name 'variable-documentation)
                        (documentation-property
                         alias 'variable-documentation))))
              (unless docu (message "don't see docu string for %s" (prin1-to-string name)))
              (add-to-list 'varslist (cons (prin1-to-string name) docu))
              (forward-line 1))
          (add-to-list 'varslist (list (match-string-no-properties 0)))))
      (setq varslist (nreverse varslist))
      (with-temp-buffer
        ;; (switch-to-buffer (current-buffer))
        (insert (concat suffix " variables\n\n"))
        (dolist (ele varslist)
          (insert (concat "** "(car ele) "\n"))
          (insert (concat "   " (cdr ele) "\n\n"))
          (setq last (point)))
        (goto-char last)
        (push-mark)
        ;; (delete-region (point) (goto-char (point-max)))
        (delete-region (point)(point-max))
        (org-mode)
        (push-mark)
        (goto-char (point-min))
        (indent-region (point-min) (point-max) )
        (write-file (concat directory-out "variables-" orgname))
        (find-file (concat directory-out "variables-" orgname)))
      (with-temp-buffer
        ;; reST
        (insert "Variables\n\n")
        ;; (insert (concat (make-string (length (concat (substring oldbuf 0 (string-match "\." oldbuf)) " commands")) ?\=) "\n\n"))
        (insert "====================\n\n")
        (dolist (ele varslist)
          (insert (concat (car ele) "\n"))
          (insert (concat (make-string (length (car ele)) ?\-) "\n"))
          (insert (concat (cdr ele) "\n\n")))
        (write-file (concat directory-out "variables-" reSTname))
        (find-file (concat directory-out "variables-" reSTname))
      ))))

(defun py-variables-unused (&optional buffer directory-in directory-out)
  "Report unused variables. "
  (interactive)
  (variables-prepare "unused"))

(defun variables-prepare (kind)
  "Used by variable-finds, variable-states. "
  (let* ((oldbuf (buffer-name (or buffer (current-buffer))))
         ;; (file (buffer-file-name))
         (orgname (concat (substring oldbuf 0 (string-match "\\." oldbuf)) ".org"))
         (reSTname (concat (substring oldbuf 0 (string-match "\\." oldbuf)) ".rst"))
         (directory-in default-directory)
         (directory-out (or directory-out (expand-file-name finds-directory-out)))
	 (command (concat "variables-base-" kind)))
    (funcall (intern-soft command) oldbuf orgname reSTname directory-in directory-out)))

(defun variables-base-unused (oldbuf orgname reSTname directory-in directory-out)
  (save-restriction
    (let ((suffix (file-name-nondirectory (buffer-file-name)))
          variableslist)
      ;; (widen)
      (goto-char (point-min))
      ;; (eval-buffer)
      (while (and (not (eobp))(re-search-forward "^(defvar [[:alpha:]]\\|^(defcustom [[:alpha:]]\\|^(defconst [[:alpha:]]" nil t 1))
        (let* ((name (symbol-at-point)))
	  (unless
	      (or (eq name 'py-menu)
		  (eq name 'python-mode-map)
		  (string-match "syntax-table" (prin1-to-string name))
		  (save-excursion
		    (re-search-forward (concat "\\_<" (prin1-to-string name) "\\_>") nil t 1)))
	    (add-to-list 'variableslist (prin1-to-string name))))
        (forward-line 1))
      (setq variableslist (nreverse variableslist))
      ;; (with-temp-buffer
      (set-buffer (get-buffer-create "Unused-Python-mode-variables.txt"))
      (erase-buffer)
      ;; org
      (insert "Unused python-mode variables\n\n")
      (switch-to-buffer (current-buffer))
      (dolist (ele variableslist)
	(insert (concat ele "\n"))
        (sit-for 0.01))
      (sit-for 0.01)
      )))

(defun functions-list-base (oldbuf orgname reSTname directory-in directory-out)
  (save-restriction
    (let ((suffix (file-name-nondirectory (buffer-file-name)))
          functionslist)
      ;; (widen)
      (goto-char (point-min))
      ;; (eval-buffer)
      (while (and (not (eobp))(re-search-forward "^(defun [[:alpha:]]+" nil t 1)) ;
	(unless (save-match-data (commandp (symbol-at-point)))
	  (let* ((name (symbol-at-point)))
	    (add-to-list 'functionslist name)))
	(forward-line 1))
      (set-buffer (get-buffer-create "Unused-Python-mode-functions.txt"))
      (erase-buffer)
      ;; org
      (insert "Unused python-mode functions\n\n")
      (switch-to-buffer (current-buffer))
      (dolist (ele functionslist)
	(insert (concat (prin1-to-string ele) "\n"))
        (sit-for 0.01))
      (sit-for 0.01))))

(defun py-functions-unused (&optional buffer directory-in directory-out)
  "Report unused functions. "
  (interactive)
  (functions-prepare "unused"))

(defun functions-prepare (kind)
  "Used by variable-finds, variable-states. "
  (let* ((oldbuf (buffer-name (or buffer (current-buffer))))
         ;; (file (buffer-file-name))
         (orgname (concat (substring oldbuf 0 (string-match "\\." oldbuf)) ".org"))
         (reSTname (concat (substring oldbuf 0 (string-match "\\." oldbuf)) ".rst"))
         (directory-in default-directory)
         (directory-out (or directory-out (expand-file-name finds-directory-out)))
	 (command (concat "functions-base-" kind)))
    (funcall (intern-soft command) oldbuf orgname reSTname directory-in directory-out)))

(defun functions-base-unused (oldbuf orgname reSTname directory-in directory-out)
  (save-restriction
    (let ((suffix (file-name-nondirectory (buffer-file-name)))
          functionslist name)
      ;; (widen)
      (goto-char (point-min))
      ;; (eval-buffer)
      (while (and (not (eobp))(re-search-forward "^(defun [[:alpha:]]+" nil t 1)) ;
	(unless (or (save-match-data (commandp (setq name (symbol-at-point))))
		    (save-excursion
		      (goto-char (point-min)) 
		      (re-search-forward (concat "\\_<\(" (prin1-to-string name) "\\_>") nil t 1)))
	  (add-to-list 'functionslist name))
	(forward-line 1))
      (set-buffer (get-buffer-create "Unused-Python-mode-functions.txt"))
      (erase-buffer)
      ;; org
      (insert "Unused python-mode functions\n\n")
      (switch-to-buffer (current-buffer))
      (dolist (ele functionslist)
	(insert (concat (prin1-to-string ele) "\n"))
        (sit-for 0.01))
      (sit-for 0.01))))

(defun py-all-docu ()
  "Write documentations commands and user-defined variables "
  (interactive)
  (find-file "~/arbeit/emacs/python-modes/python-mode/python-mode.el")
  (eval-buffer)
  (sit-for 0.1 t) 
  (finds)
  (sit-for 0.1 t)
  (write-defcustom-docus))
  
  
