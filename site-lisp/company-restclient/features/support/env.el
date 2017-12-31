(require 'f)

(defvar company-restclient-support-path
  (f-dirname load-file-name))

(defvar company-restclient-features-path
  (f-parent company-restclient-support-path))

(defvar company-restclient-root-path
  (f-parent company-restclient-features-path))

(add-to-list 'load-path company-restclient-root-path)

(require 'company-restclient)
(require 'espuds)
(require 'ert)
(require 'restclient)

(defvar company-cabal-test-prefix-output)
(defvar company-cabal-test-candidates-output)

(Before
 (setq company-restclient-test-prefix-output nil)
 (setq company-restclient-test-candidates-output nil)
 (switch-to-buffer
  (get-buffer-create "*company-restclient*"))
 (restclient-mode))
