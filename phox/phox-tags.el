;; $State$ $Date$ $Revision$ 
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


(defun phox-tags-add-table(table)
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
;    (make-local-variable 'tags-table-list) ; ne fonctionne pas
      (setq tags-table-list (cons table tags-table-list))
      )
    )
  )

(defun phox-tags-reset-table()
  "Set tags-table-list to nil."
  (interactive)
;  (make-local-variable 'tags-table-list)
  (if proof-running-on-XEmacs
      (progn
	(setq tag-table-alist (remassoc buffer-file-name tag-table-alist)))
    (setq tags-table-list nil))
  )

(defun phox-tags-add-doc-table()
  "Add tags in text documentation."
  (interactive)
  (phox-tags-add-table (concat phox-doc-dir "/text/TAGS"))
  )

(defun phox-tags-add-lib-table()
  "Add tags in libraries."
  (interactive)
  (phox-tags-add-table (concat phox-lib-dir "/TAGS"))
  )
 
(defun phox-tags-add-local-table()
  "Add the tags table created with function phox-create-local-table."
  (interactive)
  (phox-tags-add-table (concat buffer-file-name "TAGS"))
  )

(defun phox-tags-create-local-table()
  "create table on local buffer"
  (interactive)
  (shell-command (concat phox-etags 
			 " -o " 
			 (file-name-nondirectory (buffer-file-name))
			 "TAGS "
			 (file-name-nondirectory (buffer-file-name))))
  )


(defun phox-complete-tag()
"Complete symbol using tags table. Works with FSF emacs.
 Problems with xemacs."
;; xemacs build a table for completion, tag-completion-table this table
;; donnot contains key words that use ".". There is a problem with
;; syntax-table. In xemacs you need to redefine
;; add-to-tag-completion-table, in order to add your file-type and
;; syntax-table. The modification is very simple, there should be an
;; hook for that.
;; 
(interactive)
(if proof-running-on-XEmacs
     (tag-complete-symbol)
  (complete-tag)
  )
)

;; menu

(defvar phox-tags-menu
     '("Tags"
       ["create a tags table for local buffer" phox-tags-create-local-table t]
       ["------------------" nil nil]
       ["add table"               phox-tags-add-table       t]
       ["add local table"         phox-tags-add-local-table t]
       ["add table for libraries" phox-tags-add-lib-table   t]
       ["add table for text doc"  phox-tags-add-doc-table   t]
       ["reset tags table list"   phox-tags-reset-table     t]
       ["------------------" nil nil]
       ["Find theorem, definition ..." find-tag t]
       ["complete theorem, definition ..." phox-complete-tag t]
      )
"Phox menu for dealing with tags"
)

;; default

(if phox-tags-doc (add-hook 'phox-mode-hook 'phox-tags-add-doc-table))

(provide 'phox-tags)



