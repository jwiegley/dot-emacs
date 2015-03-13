(message "testing")
(setq debug-on-error t)
(add-to-list 'load-path (file-name-directory load-file-name))
(custom-set-variables
 '(custom-file "/tmp/settings.el")
 '(mac-command-modifier 'meta)
 '(initsplit-customizations-alist
   '(("\\`a" "/tmp/a-settings.el")
     ("\\`b" "/tmp/b-settings.el")
     ("\\`[ac]" "/tmp/c-settings.el")
     ("\\`d" "/tmp/a-settings.el")))
 )
(require 'initsplit)

(defgroup test nil "")

(dolist (symbol '(apple boy cat dog))
  (eval `(defcustom ,symbol nil "doc" :group 'test))
  (set symbol t)
  (put symbol 'saved-value '(t)))

(custom-save-all)
(kill-emacs)
(customize-group "test")

;; expectations:
;; a-settings.el: apple, dog
;; b-settings.el: boy
;; c-settings.el: cat
