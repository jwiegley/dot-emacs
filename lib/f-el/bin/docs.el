(defvar f-root-path
  (expand-file-name ".." (file-name-directory load-file-name)))

(defvar f-lib-file
  (expand-file-name "f.el" f-root-path))

(defvar f-readme-file
  (expand-file-name "README.md" f-root-path))

(defvar f-readme-template
  (expand-file-name "README.md.tpl" f-root-path))

(defvar f-fn-doc-mapping (make-hash-table :test 'equal))

(require 'f f-lib-file)

(-map
 (lambda (lib)
   (when (equal (car lib) f-lib-file)
     (-select
      (lambda (alist)
        (when (and
               (listp alist)
               (equal (car alist) 'defun)
               (s-matches? "^f-[^-][a-z-]+\\??$" (symbol-name (cdr alist))))
          (puthash (symbol-name (cdr alist)) (documentation (cdr alist)) f-fn-doc-mapping)))
      (cdr lib))))
 load-history)

(let ((content (f-read f-readme-template)))
  (maphash
   (lambda (fn doc)
     (setq content (s-replace (concat "{{" fn "}}") doc content)))
   f-fn-doc-mapping)
  (f-write content 'utf-8 f-readme-file))
