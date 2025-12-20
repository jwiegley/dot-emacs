;;; haskell-setup.el --- Comprehensive Haskell development environment -*- lexical-binding: t; -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@newartisans.com>
;; Version: 1.0.0
;; Package-Requires: ((emacs "27.1") (haskell-mode "17.0") (format-all "0.4") (eglot "1.9"))
;; Keywords: haskell languages tools
;; URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; This package provides a comprehensive, production-ready Haskell development
;; environment for Emacs.  It combines configuration for haskell-mode, LSP
;; integration via eglot, formatting with ormolu, and various productivity
;; enhancements.
;;
;; Features:
;;
;; - Full haskell-mode configuration with sensible defaults
;; - LSP integration using haskell-language-server via eglot
;; - Automatic code formatting with ormolu (via format-all)
;; - Unicode symbol prettification
;; - Hoogle integration (both local server and browser-based)
;; - Type signature reformatting utilities
;; - Cabal project support with customizable build commands
;; - Direnv integration for per-project environments
;; - Comprehensive alignment rules for Haskell syntax
;;
;; Installation:
;;
;; 1. Install required external tools:
;;    - haskell-language-server (for LSP support)
;;    - ormolu (for code formatting, optional)
;;    - hoogle (for documentation lookup, optional)
;;
;; 2. Add to your Emacs configuration:
;;    (require 'haskell-setup)
;;    or with use-package:
;;    (use-package haskell-setup
;;      :demand t)
;;
;; Usage:
;;
;; Open any .hs, .lhs, or .cabal file to activate haskell-mode with all
;; enhancements.
;;
;; Key Bindings (in haskell-mode):
;;
;;   C-c C-h       - my-haskell-hoogle        Search Hoogle for symbol
;;   C-c C-,       - haskell-navigate-imports Navigate to imports section
;;   C-c C-.       - haskell-mode-format-imports Format import statements
;;   C-c C-u       - my-haskell-insert-undefined Insert "undefined"
;;   C-c C-z       - haskell-interactive-switch Switch to REPL
;;   C-c M-q       - haskell-edit-reformat    Reformat type signature
;;
;; Customization:
;;
;; See the variables in the "Customization" section below, particularly:
;;
;;   haskell-setup-use-format-all   - Enable automatic formatting
;;   haskell-setup-use-eglot        - Enable LSP via eglot
;;   haskell-setup-prettify-symbols - Enable Unicode symbol display

;;; Code:

(require 'haskell-mode)
(require 'align)

;;; Customization

(defgroup haskell-setup nil
  "Comprehensive Haskell development environment."
  :group 'haskell
  :prefix "haskell-setup-")

(defcustom haskell-setup-use-format-all t
  "Whether to enable format-all-mode with ormolu formatter.
Requires ormolu to be installed and in PATH."
  :type 'boolean
  :group 'haskell-setup)

(defcustom haskell-setup-use-eglot t
  "Whether to enable eglot LSP integration.
Requires haskell-language-server to be installed and in PATH."
  :type 'boolean
  :group 'haskell-setup)

(defcustom haskell-setup-prettify-symbols t
  "Whether to enable prettify-symbols-mode with Unicode conversions."
  :type 'boolean
  :group 'haskell-setup)

(defcustom haskell-setup-hoogle-port 8687
  "Port for local Hoogle server."
  :type 'integer
  :group 'haskell-setup)

;;; Internal Variables

(defvar haskell-setup--hoogle-server-process nil
  "Process object for the local Hoogle server.")

;;; haskell-edit - Type Signature Reformatting

(defun haskell-setup--find-type-signature (&optional pos)
  "Find the type signature at or before POS.
Returns a cons cell (BEG . END) of the signature region."
  (save-excursion
    (when pos (goto-char pos))
    (re-search-backward "\\(::\\|∷\\)" nil t)
    (skip-chars-backward " ")
    (let ((end (point)) beg token)
      (backward-word)
      (setq beg (point)
            token (buffer-substring beg end))
      (forward-line)
      (while (and (not (eobp))
                  (not (looking-at token)))
        (forward-line))
      (when (looking-at token)
        (cons beg (point))))))

(defun haskell-setup--reformat-type-signature (beg end &optional format-all)
  "Reformat type signature between BEG and END.
If FORMAT-ALL is non-nil, break at every arrow."
  (interactive "r")
  (save-excursion
    (save-restriction
      (let ((endr (copy-marker end t)) (lim fill-column))
        (narrow-to-region beg endr)
        (goto-char (point-min))
        ;; Normalize whitespace
        (while (re-search-forward "[ \t\r\n][ \t\r\n]+" nil t)
          (replace-match " "))
        (when (> (- (marker-position endr) beg) lim)
          (goto-char beg)
          (looking-at "^\\(.+ \\)::")
          (let ((leader (match-string 1)))
            (if format-all
                ;; Break at every arrow
                (while (re-search-forward "\\( \\)\\([-=]> \\)" nil t)
                  (replace-match
                   (concat "\n" (make-string (length leader) ? ) "\\2"))
                  (when (looking-at "(")
                    (forward-sexp)))
              ;; First drop down the constraint if there is one
              (let ((continue t))
                (when (re-search-forward "\\( \\)\\(=> \\)" nil t)
                  (replace-match
                   (concat "\n" (make-string (length leader) ? ) "\\2"))
                  (setq continue
                        (> (- (line-end-position)
                              (line-beginning-position)) lim)))
                ;; If that's not enough, try dropping the last type
                (when continue
                  (goto-char end)
                  (when (re-search-backward "\\( \\)\\([-=]> \\)" nil t)
                    (if (> (- (point) (line-beginning-position)) lim)
                        (haskell-setup--reformat-type-signature beg endr t)
                      (replace-match
                       (concat "\n" (make-string (length leader) ? )
                               "\\2")))))))
            ;; Handle long constraint lists in parentheses
            (goto-char beg)
            (when (and (search-forward " :: (" (line-end-position) t)
                       (> (- (line-end-position)
                             (line-beginning-position)) lim))
              (goto-char (line-end-position))
              (let ((continue t))
                (while (and continue
                            (search-backward ", " (line-beginning-position) t))
                  (when (< (current-column) (1- lim))
                    (replace-match
                     (concat ",\n" (make-string (+ (length leader) 4) ? )))
                    (setq continue nil)))))))))))

;;;###autoload
(defun haskell-edit-reformat ()
  "Reformat the type signature at point, or fill paragraph if in comment."
  (interactive)
  (if (memq (get-text-property (point) 'face)
            '(font-lock-doc-face font-lock-comment-face))
      (fill-paragraph)
    (pcase (haskell-setup--find-type-signature)
      (`(,beg . ,end)
       (haskell-setup--reformat-type-signature beg end))
      (_ (user-error "No type signature found")))))

;;; Hoogle Integration

;;;###autoload
(defun my-haskell-hoogle (query &optional _arg)
  "Search Hoogle for QUERY.
Starts a local Hoogle server if not already running."
  (interactive
   (let ((def (haskell-ident-at-point)))
     (when (and def (symbolp def))
       (setq def (symbol-name def)))
     (list (read-string (if def
                            (format "Hoogle query (default %s): " def)
                          "Hoogle query: ")
                        nil nil def)
           current-prefix-arg)))
  (let ((pe process-environment)
        (ep exec-path))
    (unless (and haskell-setup--hoogle-server-process
                 (process-live-p haskell-setup--hoogle-server-process))
      (message "Starting local Hoogle server on port %d..."
               haskell-setup-hoogle-port)
      (with-current-buffer (get-buffer-create " *hoogle-web*")
        (cd temporary-file-directory)
        (let ((process-environment pe)
              (exec-path ep))
          (setq haskell-setup--hoogle-server-process
                (start-process "hoogle-web" (current-buffer)
                               (executable-find "hoogle")
                               "server"
                               "--local"
                               (format "--port=%d" haskell-setup-hoogle-port)))))
      (sit-for 1)
      (message "Starting local Hoogle server on port %d...done"
               haskell-setup-hoogle-port)))
  (browse-url
   (format "http://127.0.0.1:%d/?hoogle=%s"
           haskell-setup-hoogle-port
           (replace-regexp-in-string
            " " "+"
            (replace-regexp-in-string "\\+" "%2B" query)))))

;;; Utility Functions

;;;###autoload
(defun my-haskell-insert-undefined ()
  "Insert the word undefined at point."
  (interactive)
  (insert "undefined"))

;;;###autoload
(defun snippet (name)
  "Create or open a Haskell snippet file with NAME."
  (interactive "sName: ")
  (find-file (expand-file-name (concat name ".hs")
                               "~/src/notes/haskell"))
  (haskell-mode)
  (goto-char (point-min))
  (when (eobp)
    (insert "hdr")
    (when (fboundp 'yas-expand)
      (yas-expand))))

;;; Unicode Symbol Prettification

(defconst haskell-setup-prettify-symbols-alist
  '(("::"     . ?∷)
    ("forall" . ?∀)
    ("exists" . ?∃)
    ("->"     . ?→)
    ("<-"     . ?←)
    ("=>"     . ?⇒)
    ("~>"     . ?⇝)
    ("<~"     . ?⇜)
    ("<>"     . ?⨂)
    ("msum"   . ?⨁)
    ("\\"     . ?λ)
    ("not"    . ?¬)
    ("&&"     . ?∧)
    ("||"     . ?∨)
    ("/="     . ?≠)
    ("<="     . ?≤)
    (">="     . ?≥)
    ("<<<"    . ?⋘)
    (">>>"    . ?⋙)
    ("`elem`"             . ?∈)
    ("`notElem`"          . ?∉)
    ("`member`"           . ?∈)
    ("`notMember`"        . ?∉)
    ("`union`"            . ?∪)
    ("`intersection`"     . ?∩)
    ("`isSubsetOf`"       . ?⊆)
    ("`isNotSubsetOf`"    . ?⊄)
    ("`isSubsequenceOf`"  . ?⊆)
    ("`isProperSubsetOf`" . ?⊂)
    ("undefined"          . ?⊥))
  "Alist of Haskell symbols to Unicode characters for prettify-symbols-mode.")

;;; Direnv Integration

(defun haskell-setup--update-cabal-repl (&rest _args)
  "Update CABAL_REPL arguments from environment after direnv update."
  (let ((cabal-repl (getenv "CABAL_REPL")))
    (when cabal-repl
      (let ((args (nthcdr 2 (split-string cabal-repl))))
        (setq-local haskell-process-args-cabal-repl
                    (delete-dups
                     (append haskell-process-args-cabal-repl args)))))))

;;; Ormolu Formatter Integration

(defun haskell-setup--setup-ormolu ()
  "Configure format-all to use ormolu for Haskell."
  (when (and haskell-setup-use-format-all
             (executable-find "ormolu")
             (require 'format-all nil t))
    (with-eval-after-load 'format-all
      (define-format-all-formatter ormolu
        (:executable "ormolu")
        (:install "stack install ormolu")
        (:languages "Haskell" "Literate Haskell")
        (:features)
        (:format
         (format-all--buffer-easy
          executable
          (when (buffer-file-name)
            (list "--stdin-input-file" (buffer-file-name))))))
      (format-all--set-chain "Haskell" '(ormolu)))))

;;; Main Mode Hook

(defun haskell-setup-mode-hook ()
  "Hook function for haskell-mode setup."
  ;; Indentation
  (haskell-indentation-mode 1)

  ;; Bug reference mode for issue tracking
  (bug-reference-prog-mode 1)

  ;; Unicode prettification
  (when haskell-setup-prettify-symbols
    (setq-local prettify-symbols-alist haskell-setup-prettify-symbols-alist)
    (prettify-symbols-mode 1))

  ;; Direnv integration
  (when (fboundp 'direnv-update-directory-environment)
    (advice-add 'direnv-update-directory-environment
                :after #'haskell-setup--update-cabal-repl))

  ;; Ormolu formatting setup
  (haskell-setup--setup-ormolu))

;;; Alignment Rules

(defun haskell-setup--configure-alignment ()
  "Add Haskell-specific alignment rules."
  (dolist (rule '((haskell-types       . "\\(\\s-+\\)\\(::\\|∷\\)\\s-+")
                  (haskell-assignment  . "\\(\\s-+\\)=\\s-+")
                  (haskell-arrows      . "\\(\\s-+\\)\\(->\\|→\\)\\s-+")
                  (haskell-left-arrows . "\\(\\s-+\\)\\(<-\\|←\\)\\s-+")))
    (add-to-list 'align-rules-list
                 `(,(car rule)
                   (regexp . ,(cdr rule))
                   (modes quote (haskell-mode haskell-literate-mode))))))

;;; Eglot Configuration

(defun haskell-setup--configure-eglot ()
  "Configure eglot for Haskell LSP support."
  (when (and haskell-setup-use-eglot
             (require 'eglot nil t))
    ;; Register haskell-language-server with eglot
    (with-eval-after-load 'eglot
      (add-to-list 'eglot-server-programs
                   '(haskell-mode . ("haskell-language-server" "--lsp")))

      ;; Configure eldoc for eglot-managed buffers
      (add-hook 'eglot-managed-mode-hook
                (lambda ()
                  (when (derived-mode-p 'haskell-mode)
                    (setq-local eldoc-documentation-strategy
                                #'eldoc-documentation-default)))
                t))))

;;; Main Configuration

;;;###autoload
(defun haskell-setup-configure ()
  "Configure haskell-mode with all enhancements.
This function is called automatically when haskell-setup is loaded."
  ;; File associations
  (add-to-list 'auto-mode-alist '("\\.hs\\(c\\|-boot\\)?\\'" . haskell-mode))
  (add-to-list 'auto-mode-alist '("\\.lhs\\'" . haskell-literate-mode))
  (add-to-list 'auto-mode-alist '("\\.cabal\\'" . haskell-cabal-mode))

  ;; Custom variables for haskell-mode
  (setq haskell-compile-cabal-build-command
        "cd %s && cabal new-build --ghc-option=-ferror-spans")
  (setq haskell-hasktags-arguments '("-e"))
  (setq haskell-tags-on-save t)
  (setq haskell-hoogle-command nil)
  (setq haskell-indent-spaces 2)
  (setq haskell-indentation-ifte-offset 2)
  (setq haskell-indentation-layout-offset 2)
  (setq haskell-indentation-left-offset 2)
  (setq haskell-indentation-starter-offset 2)
  (setq haskell-indentation-where-post-offset 2)
  (setq haskell-indentation-where-pre-offset 0)
  (setq haskell-process-args-cabal-repl
        '("--ghc-option=-ferror-spans"
          "--repl-options=-Wno-missing-home-modules"
          "--repl-options=-ferror-spans"))
  (setq haskell-process-load-or-reload-prompt t)

  ;; Key bindings
  (define-key haskell-mode-map (kbd "C-c C-h") #'my-haskell-hoogle)
  (define-key haskell-mode-map (kbd "C-c C-,") #'haskell-navigate-imports)
  (define-key haskell-mode-map (kbd "C-c C-.") #'haskell-mode-format-imports)
  (define-key haskell-mode-map (kbd "C-c C-u") #'my-haskell-insert-undefined)
  (define-key haskell-mode-map (kbd "C-c C-z") #'haskell-interactive-switch)
  (define-key haskell-mode-map (kbd "C-c M-q") #'haskell-edit-reformat)

  ;; Unbind keys that conflict with common Emacs bindings
  (define-key haskell-mode-map (kbd "M-s") nil)
  (define-key haskell-mode-map (kbd "M-t") nil)

  ;; Add mode hook
  (add-hook 'haskell-mode-hook #'haskell-setup-mode-hook)

  ;; Configure alignment
  (haskell-setup--configure-alignment)

  ;; Configure eglot
  (haskell-setup--configure-eglot))

;; Run configuration when loaded
;;;###autoload
(haskell-setup-configure)

(provide 'haskell-setup)

;;; haskell-setup.el ends here
