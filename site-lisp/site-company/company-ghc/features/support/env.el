(require 'f)

(defvar company-ghc-support-path
  (f-dirname load-file-name))

(defvar company-ghc-features-path
  (f-parent company-ghc-support-path))

(defvar company-ghc-root-path
  (f-parent company-ghc-features-path))

(add-to-list 'load-path company-ghc-root-path)

(require 'ert)
(require 'espuds)
(require 'haskell-mode)
(require 'haskell-font-lock)
(require 'company-ghc)

(defvar company-ghc-test-prefix-output)
(defvar company-ghc-test-candidates-output)
(defvar company-ghc-test-imported-modules-output)
(defvar company-ghc-test-hoogle-candidates-output)

(Setup
 (global-company-mode))

(Before
 (setq company-ghc-test-prefix-output nil)
 (setq company-ghc-test-candidates-output nil)
 (setq company-ghc-test-imported-modules-output nil)
 (setq company-ghc-test-hoogle-candidates-output nil)
 (switch-to-buffer
  (get-buffer-create "*company-ghc*"))
 (haskell-mode))

(After)
