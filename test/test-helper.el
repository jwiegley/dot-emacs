(require 'undercover)
(require 'f)

(defvar helm-dash-test-path
  (f-dirname (f-this-file)))

(defvar helm-dash-code-path
  (f-parent helm-dash-test-path))

(defun helm-dash-ends-with (string suffix)
  "Return t if STRING ends with SUFFIX."
  (and (string-match (format "%s$" suffix)
                     string)
       t))

(undercover "*.el" "helm-dash/*.el" (:exclude "*-test.el"))
(require 'helm-dash (f-expand "helm-dash.el" helm-dash-code-path))
