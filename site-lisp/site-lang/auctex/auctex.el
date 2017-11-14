;;; auctex.el
;;
;; This can be used for starting up AUCTeX.  The following somewhat
;; strange trick causes tex-site.el to be loaded in a way that can be
;; safely undone using (unload-feature 'tex-site).
;;
(autoload 'TeX-load-hack
  (expand-file-name "tex-site.el" (file-name-directory load-file-name)))
(TeX-load-hack)

