;;; aggressive-indent-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (aggressive-indent-) "aggressive-indent" "aggressive-indent.el"
;;;;;;  (21587 41662 658130 132000))
;;; Generated autoloads from aggressive-indent.el

(let ((loads (get 'aggressive-indent 'custom-loads))) (if (member '"aggressive-indent" loads) nil (put 'aggressive-indent 'custom-loads (cons '"aggressive-indent" loads))))

(autoload 'aggressive-indent-indent-defun "aggressive-indent" "\
Indent current defun.
Throw an error if parentheses are unbalanced.

\(fn)" t nil)

(autoload 'aggressive-indent-mode "aggressive-indent" "\
Toggle Aggressive-Indent mode on or off.
With a prefix argument ARG, enable Aggressive-Indent mode if ARG is
positive, and disable it otherwise.  If called from Lisp, enable
the mode if ARG is omitted or nil, and toggle it if ARG is `toggle'.
\\{aggressive-indent-mode-map}

\(fn &optional ARG)" t nil)

(defvar global-aggressive-indent-mode nil "\
Non-nil if Global-Aggressive-Indent mode is enabled.
See the command `global-aggressive-indent-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `global-aggressive-indent-mode'.")

(custom-autoload 'global-aggressive-indent-mode "aggressive-indent" nil)

(autoload 'global-aggressive-indent-mode "aggressive-indent" "\
Toggle Aggressive-Indent mode in all buffers.
With prefix ARG, enable Global-Aggressive-Indent mode if ARG is positive;
otherwise, disable it.  If called from Lisp, enable the mode if
ARG is omitted or nil.

Aggressive-Indent mode is enabled in all buffers where
`aggressive-indent-mode' would do it.
See `aggressive-indent-mode' for more information on Aggressive-Indent mode.

\(fn &optional ARG)" t nil)

(defalias 'aggressive-indent-global-mode #'global-aggressive-indent-mode)

;;;***

;;;### (autoloads nil nil ("aggressive-indent-pkg.el") (21587 41662
;;;;;;  753583 753000))

;;;***

(provide 'aggressive-indent-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; aggressive-indent-autoloads.el ends here
