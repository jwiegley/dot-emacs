;;; flycheck-haskell.el --- Flycheck: Automatic Haskell configuration -*- lexical-binding: t; -*-

;; Copyright (C) 2014-2016 Sebastian Wiesner <swiesner@lunaryorn.com>
;; Copyright (C) 2016 Danny Navarro
;; Copyright (C) 2015 Mark Karpov <markkarpov@opmbx.org>
;; Copyright (C) 2015 Michael Alan Dorman <mdorman@ironicdesign.com>
;; Copyright (C) 2015 Alex Rozenshteyn <rpglover64@gmail.com>
;; Copyright (C) 2014 Gracjan Polak <gracjanpolak@gmail.com>

;; Author: Sebastian Wiesner <swiesner@lunaryorn.com>
;; URL: https://github.com/flycheck/flycheck-haskell
;; Keywords: tools, convenience
;; Version: 0.9-cvs
;; Package-Requires: ((emacs "24.3") (flycheck "0.25") (haskell-mode "13.7") (dash "2.4.0") (seq "1.11") (let-alist "1.0.1"))

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Automatically configure Flycheck for Haskell.

;;;; Cabal support

;; Try to find a Cabal file for the current Haskell buffer, and configure syntax
;; checking according to the Cabal project settings.

;;;; Cabal sandboxes

;; Try to find a Cabal sandbox configuration for this project, and configure the
;; Haskell syntax checkers in Flycheck to use the package database from the
;; Sandbox.

;;;; Setup

;; (add-hook 'flycheck-mode-hook #'flycheck-haskell-setup)

;;; Code:

(eval-when-compile
  (require 'rx)
  (require 'let-alist))

(require 'seq)
(require 'haskell-cabal)
(require 'flycheck)
(require 'dash)


;;; Customization

(defgroup flycheck-haskell nil
  "Haskell support for Flycheck."
  :prefix "flycheck-haskell-"
  :group 'flycheck
  :link '(url-link :tag "Github" "https://github.com/flycheck/flycheck-haskell"))

(defcustom flycheck-haskell-runghc-command
  (if (executable-find "stack")
      '("stack" "--verbosity" "silent" "runghc" "--no-ghc-package-path" "--")
    '("runghc"))
  "Command for `runghc'.

This library uses `runghc' to run various Haskell helper scripts
to extract information from Cabal files.  This option provides
the command to invoke `runghc'.  The default is to use `stack'
and otherwise fall back to standard `runghc'."
  :type '(repeat (string :tag "Command"))
  :risky t
  :group 'flycheck-haskell)


;;; Cabal support
(defconst flycheck-haskell-directory
  (file-name-directory (if load-in-progress
                           load-file-name
                         (buffer-file-name)))
  "The package directory of flycheck-haskell.")

(defconst flycheck-haskell-helper
  (expand-file-name "get-cabal-configuration.hs" flycheck-haskell-directory)
  "The helper to dump the Cabal configuration.")

(defconst flycheck-haskell-flags-helper
  (expand-file-name "get-flags.hs" flycheck-haskell-directory)
  "The helper to get compiler flags for the Cabal helper.")

(defun flycheck-haskell-runghc-command (args)
  "Create a runghc command with ARGS.

Take the base command from `flycheck-haskell-runghc-command'."
  (append flycheck-haskell-runghc-command args nil))

(defun flycheck-haskell--get-flags ()
  "Get GHC flags to run the Cabal helper."
  (ignore-errors
    (apply #'process-lines
           (flycheck-haskell-runghc-command
            (list flycheck-haskell-flags-helper)))))

(defun flycheck-haskell-read-cabal-configuration (cabal-file)
  "Read the Cabal configuration from CABAL-FILE."
  (let* ((args (append (flycheck-haskell--get-flags)
                       (list flycheck-haskell-helper cabal-file)))
         (command (flycheck-haskell-runghc-command args)))
    (with-temp-buffer
      (pcase (apply 'call-process (car command) nil t nil (cdr command))
        (0 (goto-char (point-min))
           (read (current-buffer)))
        (retcode (message "Reading Haskell configuration failed with exit code %s and output:\n%s"
                          retcode (buffer-string))
                 nil)))))


;;; Cabal configuration caching
(defconst flycheck-haskell-config-cache (make-hash-table :test 'equal)
  "Cache of Cabal configuration.

A hash table, mapping the name of a cabal file to a
cons-cell `(MODTIME . CONFIG)', where MODTIME is the modification
time of the cabal file, and CONFIG the extracted configuration.")

(defun flycheck-haskell-clear-config-cache ()
  "Clear the cache of configurations."
  (interactive)
  (clrhash flycheck-haskell-config-cache))

(defun flycheck-haskell-get-cached-configuration (cabal-file)
  "Get the cached configuration for CABAL-FILE.

Return the cached configuration, or nil, if there is no cache
entry, or if the cache entry is outdated."
  (pcase-let* ((cache-entry (gethash cabal-file flycheck-haskell-config-cache))
               (`(,modtime . ,config) cache-entry))
    (when (and modtime (file-exists-p cabal-file))
      (let ((current-modtime (nth 5 (file-attributes cabal-file))))
        (if (time-less-p modtime current-modtime)
            ;; The entry is outdated, drop it.  `remhash' always
            ;; returns nil, so we are safe to use it here.
            (remhash cabal-file flycheck-haskell-config-cache)
          ;; The configuration is up to date, use it
          config)))))

(defun flycheck-haskell-read-and-cache-configuration (cabal-file)
  "Read and cache configuration from CABAL-FILE.

Return the configuration."
  (let ((modtime (nth 5 (file-attributes cabal-file)))
        (config (flycheck-haskell-read-cabal-configuration cabal-file)))
    (puthash cabal-file (cons modtime config) flycheck-haskell-config-cache)
    config))

(defun flycheck-haskell-get-configuration (cabal-file)
  "Get the Cabal configuration from CABAL-FILE.

Get the configuration either from our cache, or by reading the
CABAL-FILE.

Return the configuration."
  (or (flycheck-haskell-get-cached-configuration cabal-file)
      (flycheck-haskell-read-and-cache-configuration cabal-file)))


;;; Cabal sandbox support
(defconst flycheck-haskell-cabal-config "cabal.config"
  "The file name of a Cabal configuration.")

(defconst flycheck-haskell-cabal-config-keys '(with-compiler)
  "Keys to parse from a Cabal configuration file.")

(defconst flycheck-haskell-sandbox-config "cabal.sandbox.config"
  "The file name of a Cabal sandbox configuration.")

(defconst flycheck-haskell-sandbox-config-keys '(package-db)
  "Keys to parse from a Cabal sandbox configuration.")

(defmacro flycheck-haskell-with-config-file-buffer (file-name &rest body)
  "Eval BODY in a buffer with the contents of FILE-NAME."
  (declare (indent 1))
  `(with-temp-buffer
     (insert-file-contents ,file-name)
     (goto-char (point-min))
     ,@body))

(defun flycheck-haskell-get-config-value (key)
  "Get the value of a configuration KEY from this buffer.

KEY is a symbol denoting the key whose value to get.  Return
a `(KEY . VALUE)' cons cell."
  (save-excursion
    (goto-char (point-min))
    (-when-let (setting (haskell-cabal--get-field (symbol-name key)))
      (cons key (substring-no-properties setting)))))

(defun flycheck-haskell-parse-config-file (keys config-file)
  "Parse KEYS from CONFIG-FILE.

KEYS is a list of symbols.  Return an alist with all parsed
KEYS."
  (flycheck-haskell-with-config-file-buffer config-file
    (mapcar #'flycheck-haskell-get-config-value keys)))

(defun flycheck-haskell-find-config (config-file)
  "Find a CONFIG-FILE for the current buffer.

Return the absolute path of CONFIG-FILE as string, or nil if
CONFIG-FILE was not found."
  (-when-let (root-dir (locate-dominating-file (buffer-file-name) config-file))
    (expand-file-name config-file root-dir)))

(defun flycheck-haskell-get-cabal-config ()
  "Get Cabal configuration for the current buffer.

Return an alist with the Cabal configuration for the current
buffer."
  (-when-let (file-name (flycheck-haskell-find-config
                         flycheck-haskell-cabal-config))
    (flycheck-haskell-parse-config-file flycheck-haskell-cabal-config-keys
                                        file-name)))

(defun flycheck-haskell-get-sandbox-config ()
  "Get sandbox configuration for the current buffer.

Return an alist with the sandbox configuration for the current
buffer."
  (-when-let (file-name (flycheck-haskell-find-config
                         flycheck-haskell-sandbox-config))
    (flycheck-haskell-parse-config-file flycheck-haskell-sandbox-config-keys
                                        file-name)))


;;; Buffer setup
(defun flycheck-haskell-process-configuration (config)
  "Process the a Cabal CONFIG."
  (let-alist config
    (setq-local flycheck-ghc-search-path
                (append .build-directories .source-directories
                        flycheck-ghc-search-path))
    (setq-local flycheck-ghc-language-extensions
                (append .extensions .languages
                        flycheck-ghc-language-extensions))
    (setq-local flycheck-ghc-args
                (append .other-options
                        (seq-map (apply-partially #'concat "-I")
                                 .autogen-directories)
                        '("-optP-include" "-optPcabal_macros.h")
                        (cons "-hide-all-packages"
                              (seq-mapcat (apply-partially #'list "-package")
                                          .dependencies))
                        flycheck-ghc-args))
    (setq-local flycheck-hlint-args
                (append (seq-mapcat (apply-partially #'list "--cpp-include")
                                    .autogen-directories)
                        '("--cpp-file" "cabal_macros.h")))))

(defun flycheck-haskell-configure ()
  "Set paths and package database for the current project."
  (interactive)
  (when (and (buffer-file-name) (file-directory-p default-directory))
    (-when-let* ((cabal-file (haskell-cabal-find-file))
                 (config (flycheck-haskell-get-configuration cabal-file)))
      (flycheck-haskell-process-configuration config))

    (let-alist (flycheck-haskell-get-cabal-config)
      (when .with-compiler
        (setq-local flycheck-haskell-ghc-executable .with-compiler)))

    (let-alist (flycheck-haskell-get-sandbox-config)
      (when .package-db
        (setq-local flycheck-ghc-package-databases
                    (cons .package-db flycheck-ghc-package-databases))
        (setq-local flycheck-ghc-no-user-package-database t)))))

;;;###autoload
(defun flycheck-haskell-setup ()
  "Setup Haskell support for Flycheck.

If the current file is part of a Cabal project, configure
Flycheck to take the module paths of the Cabal projects into
account.

Also search for Cabal sandboxes and add them to the module search
path as well."
  (add-hook 'hack-local-variables-hook #'flycheck-haskell-configure))

(provide 'flycheck-haskell)

;; Local Variables:
;; indent-tabs-mode: nil
;; coding: utf-8
;; End:

;;; flycheck-haskell.el ends here
