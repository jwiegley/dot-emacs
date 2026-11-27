;;; dired-filter-filetags.el --- Filter Dired by filetags -*- lexical-binding: t; -*-

;;; Commentary:

;; Add a filetags filter to dired-filter.  Repeated filters intersect;
;; dired-filter's negate and OR commands work on them as usual.

;;; Code:

(require 'dired-filter)
(require 'dired-filetags)

(dired-filter-define filetags
    "Keep files carrying QUALIFIER as a filetags tag."
  (:description "filetags"
   :reader (completing-read "File tag: "
                            (mapcar #'car (dired-filetags--buffer-tags))
                            nil nil))
  (member qualifier (dired-filetags-tags file-name)))

(define-key dired-filter-map "t" #'dired-filter-by-filetags)

(provide 'dired-filter-filetags)
;;; dired-filter-filetags.el ends here
