;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;;                         gestion des TAGS
;;--------------------------------------------------------------------------;;

; sous xemacs, visit-tags-table n'a pas d'argument optionnel. Sous gnu emacs :

; Normally M-x visit-tags-table sets the global value of `tags-file-name'.
; With a prefix arg, set the buffer-local value instead.

; mieux vaut sous gnu emacs gérer la variable tags-table-list, qui
; n'existe pas sous xemacs.
; Sous xemacs il faut gérer la variable tag-table-alist qui n'existe pas
; sous gnu emacs.

(require 'etags) 

(defun af2-tags-add-table(table)
  "add tags table"
  (interactive "D directory, location of a file named TAGS to add : ")
  (if proof-running-on-XEmacs
      (let ((association (cons buffer-file-name table)))
	(if (member association tag-table-alist)
	    (message (concat table " already loaded."))
	  (setq tag-table-alist (cons association tag-table-alist))))
					; gnu emacs
    (if (member table tags-table-list)
	(message (concat table " already loaded."))
;    (make-local-variable 'tags-table-list) ; ne focntionne pas
      (setq tags-table-list (cons table tags-table-list))
      )
    )
  )

(defun af2-tags-reset-table()
  "Set tags-table-list to nil."
  (interactive)
;  (make-local-variable 'tags-table-list)
  (if proof-running-on-XEmacs
      (progn
	(setq tag-table-alist (remassoc buffer-file-name tag-table-alist)))
    (setq tags-table-list nil))
  )

(defun af2-tags-add-doc-table()
  "Add tags in text documentation."
  (interactive)
  (af2-tags-add-table (concat af2-doc-dir "/text/TAGS"))
  )

(defun af2-tags-add-lib-table()
  "Add tags in libraries."
  (interactive)
  (af2-tags-add-table (concat af2-lib-dir "TAGS"))
  )
 
(defun af2-tags-add-local-table()
  "Add the tags table created with function af2-create-local-table."
  (interactive)
  (af2-tags-add-table (concat buffer-file-name "TAGS"))
  )

(defun af2-tags-create-local-table()
  "create table on local buffer"
  (interactive)
  (shell-command (concat af2-etags 
			 " -o " 
			 (file-name-nondirectory (buffer-file-name))
			 "TAGS "
			 (file-name-nondirectory (buffer-file-name))))
  )

;; default

(if af2-tags-doc (add-hook 'af2-mode-hook 'af2-tags-add-doc-table))

(provide 'af2-tags)