;;; debbugs-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (debbugs-gnu debbugs-gnu-search) "debbugs-gnu"
;;;;;;  "debbugs-gnu.el" (20455 60447))
;;; Generated autoloads from debbugs-gnu.el

(autoload 'debbugs-gnu-search "debbugs-gnu" "\
Search for Emacs bugs interactively.
Search arguments are requested interactively.  The \"search
phrase\" is used for full text search in the bugs database.
Further key-value pairs are requested until an empty key is
returned.  If a key cannot be queried by a SOAP request, it is
marked as \"client-side filter\".

\(fn)" t nil)

(autoload 'debbugs-gnu "debbugs-gnu" "\
List all outstanding Emacs bugs.

\(fn SEVERITIES &optional PACKAGES ARCHIVEDP SUPPRESS)" t nil)

;;;***

;;;### (autoloads nil nil ("debbugs-pkg.el" "debbugs.el") (20455
;;;;;;  60447 404800))

;;;***

(provide 'debbugs-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; debbugs-autoloads.el ends here
