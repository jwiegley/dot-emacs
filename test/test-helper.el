
(require 'f)

(defvar ov-test-path
  (f-dirname (f-this-file)))

(defvar ov-code-path
  (f-parent ov-test-path))

(require 'ov (f-expand "ov.el" ov-code-path))
