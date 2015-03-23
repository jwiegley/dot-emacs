(require 'f)

(defvar company-cabal-support-path
  (f-dirname load-file-name))

(defvar company-cabal-features-path
  (f-parent company-cabal-support-path))

(defvar company-cabal-root-path
  (f-parent company-cabal-features-path))

(add-to-list 'load-path company-cabal-root-path)

(require 'company-cabal)
(require 'haskell-cabal)
(require 'espuds)
(require 'ert)

(defvar company-cabal-test-prefix-output)
(defvar company-cabal-test-candidates-output)

(Before
 (setq company-cabal-test-prefix-output nil)
 (setq company-cabal-test-candidates-output nil)
 (switch-to-buffer
  (get-buffer-create "*company-cabal*"))
 (haskell-cabal-mode))

(After)
