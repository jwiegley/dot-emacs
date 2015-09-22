(require 'f)

(defvar hyai-support-path
  (f-dirname load-file-name))

(defvar hyai-features-path
  (f-parent hyai-support-path))

(defvar hyai-root-path
  (f-parent hyai-features-path))

(add-to-list 'load-path hyai-root-path)

(require 'undercover)
(if (equal (getenv "UNDERCOVER_SEND_REPORT") "1")
    (undercover "hyai.el")
  (undercover "hyai.el" (:send-report nil)))

(require 'hyai)
(require 'espuds)
(require 'ert)
(require 'haskell-mode)
(require 'haskell-font-lock)

(Setup
 (defvar hyai-test-candidates-output)
 (switch-to-buffer
  (get-buffer-create "*hyai*"))
 (haskell-mode)
 (global-set-key (kbd "RET") 'newline-and-indent)
 (hyai-mode))

(Before
 (setq hyai-test-candidates-output nil))
