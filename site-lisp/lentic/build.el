(add-to-list 'load-path default-directory)

(require 'lentic-doc)
(require 'commander)

(toggle-debug-on-error)

(defun build/gen-org ()
  (interactive)
  (lentic-doc-orgify-package 'lentic))

(defun build/gen-html ()
  (interactive)
  (lentic-doc-htmlify-package 'lentic))


(commander
 (command "gen-org" "Generate org from el" build/gen-org)
 (command "gen-html" "Generate HTML from org" build/gen-html))
