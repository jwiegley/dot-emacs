(require 'f)

(let* ((this-directory (f-dirname load-file-name))
       (wrap-region-root-path (f-parent (f-parent this-directory)))
       (wrap-region-vendor-path (f-expand "vendor" wrap-region-root-path)))
  (add-to-list 'load-path wrap-region-root-path)
  (unless (require 'ert nil 'noerror)
    (require 'ert (f-expand "ert" wrap-region-vendor-path))))

(require 'wrap-region)
(require 'espuds)

(setq default-except-modes wrap-region-except-modes)

(Before
 (switch-to-buffer
  (get-buffer-create "*wrap-region*"))
 (erase-buffer)
 (transient-mark-mode 1)
 (deactivate-mark))

(After
 ;; For scenarios that add wrappers
 (wrap-region-destroy-wrapper "$")
 (wrap-region-destroy-wrapper "#")

 ;; Reset hooks
 (setq wrap-region-hook nil)
 (setq wrap-region-before-wrap-hook nil)
 (setq wrap-region-after-wrap-hook nil)

 ;; Disable wrap-region-mode
 (wrap-region-mode -1)
 (wrap-region-global-mode -1)

 ;; Reset all except modes
 (setq wrap-region-except-modes default-except-modes)

 ;; Do not require negative prefix arg
 (setq wrap-region-only-with-negative-prefix nil)

 ;; Do not keep the wrapped region active
 (setq wrap-region-keep-mark nil)

 ;; Disable delete-selection-mode
 (delete-selection-mode -1))
