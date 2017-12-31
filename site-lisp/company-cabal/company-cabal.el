;;; company-cabal.el --- company-mode cabal backend -*- lexical-binding: t -*-

;; Copyright (C) 2014-2017 by Iku Iwasa

;; Author:    Iku Iwasa <iku.iwasa@gmail.com>
;; URL:       https://github.com/iquiw/company-cabal
;; Version:   0.3.0
;; Package-Requires: ((cl-lib "0.5") (company "0.8.0") (emacs "24"))
;; Stability: experimental

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; `company-mode' back-end for `haskell-cabal-mode'.
;;
;; Provide completion for section name, field name and some of field values.
;; Add `company-cabal' to `company-mode' back-ends list.
;;
;;     (add-to-list 'company-backends 'company-cabal)

;;; Code:

(require 'cl-lib)
(require 'company)

(require 'company-cabal-fields)

(defgroup company-cabal nil
  "company-mode back-end for haskell-cabal-mode."
  :group 'company)

(defcustom company-cabal-field-value-offset 21
  "Specify column offset filled after field name completion.
Set it to 0 if you want to turn off this behavior."
  :type 'number)

(defcustom company-cabal-version-modifier 'company-cabal-version-major-lower
  "Specify version modifier function for post completion of package name.
The function takes version string and returns modified version string.
Post completion is disabled if it is nil."
  :type '(choice
          (const :tag "Off" nil)
          (const :tag " >= m1.m2" company-cabal-version-major-lower)
          (const :tag " == m1.m2.*" company-cabal-version-major-eq)
          (function :tag "version modifier function")))

(defun company-cabal-version-major-eq (ver)
  "Modify version string VER: 'x.y.z.w' to ' == x.y.*.*'."
  (pcase (version-to-list ver)
    (`(,m1 . (,m2 . ,_)) (format " == %d.%d.*" m1 m2))
    (_ (concat " == " ver))))

(defun company-cabal-version-major-lower (ver)
  "Modify version string VER: 'x.y.z.w' to ' >= x.y'."
  (pcase (version-to-list ver)
    (`(,m1 . (,m2 . ,_)) (format " >= %d.%d" m1 m2))
    (_ (concat " >= " ver))))

(defconst company-cabal--section-regexp
  "^\\([[:space:]]*\\)\\([[:word:]]+\\)\\([[:space:]]\\|$\\)")

(defconst company-cabal--field-regexp
  "^\\([[:space:]]*\\)\\([[:word:]]+\\):")

(defconst company-cabal--conditional-regexp
  "^\\([[:space:]]*\\)\\(if\\|else\\)[[:space:]]+\\(.*\\)")

(defconst company-cabal--simple-field-regexp
  (concat company-cabal--field-regexp "[[:space:]]*\\([^[:space:]]*\\)"))

(defconst company-cabal--list-field-regexp
  (concat company-cabal--field-regexp
          "\\(?:[[:space:]]+[^[:space:]]+,?\\)*?" ; no multi-line
          "[[:space:]]*\\([^[:space:]]*\\)"))

(defvar company-cabal--ghc-options nil)
(defvar company-cabal--ghc-extensions nil)
(defvar company-cabal--packages nil)
(make-variable-buffer-local 'company-cabal--packages)

(defun company-cabal-prefix ()
  "Provide completion prefix at the current point."
  (cond
   ((company-cabal--in-comment-p) nil)
   (t
    (let ((prefix (company-grab-symbol)))
      (pcase (company-cabal--find-context)
        (`(field . ,value)
         (cond
          ((and (or (string= prefix "") (string-match-p "^-" prefix))
                (member value '("ghc-options" "ghc-prof-options"
                                "ghc-shared-options")))
           prefix)
          ((member value '("build-type" "hs-source-dirs" "type"
                           "build-depends"
                           "extensions" "default-extensions"
                           "other-extensions"))
           prefix)))
        (`(sectval . ,_) nil)
        (_ prefix))))))

(defun company-cabal-candidates (prefix)
  "Provide completion candidates for the given PREFIX."
  (pcase (company-cabal--find-context)
    (`(section . ,value)
     (let ((fields
            (cdr (assoc-string value company-cabal--section-field-alist))))
       (all-completions (downcase prefix)
                        (or fields
                            (append company-cabal--sections
                                    company-cabal--pkgdescr-fields)))))
    (`(field . ,value)
     (pcase value
       (`"build-type"
        (all-completions prefix company-cabal--build-type-values))
       (`"hs-source-dirs"
        (all-completions prefix (company-cabal--get-directories)))
       (`"type"
        (pcase (company-cabal--find-current-section)
          (`"benchmark"
           (all-completions prefix company-cabal--benchmark-type-values))
          (`"test-suite"
           (all-completions prefix company-cabal--testsuite-type-values))
          (`"source-repository"
           (all-completions prefix company-cabal--sourcerepo-type-values))))
       (`"build-depends"
        (all-completions prefix (company-cabal--list-packages)))
       ((or `"ghc-options" `"ghc-prof-options" `"ghc-shared-options")
        (all-completions prefix (company-cabal--get-ghc-options)))
       ((or `"extensions" `"default-extensions" `"other-extensions")
        (all-completions prefix (company-cabal--get-ghc-extensions)))))
    (`(top)
      (all-completions (downcase prefix)
                       (append company-cabal--sections
                               company-cabal--pkgdescr-fields)))))

(defun company-cabal-annotation (candidate)
  "Return type property of CANDIDATE as annotation."
  (let ((type (get-text-property 0 :type candidate))
        (ver (get-text-property 0 :version candidate)))
    (cond
     (type (concat " " (symbol-name type)))
     (ver  (concat " " ver)))))

(defun company-cabal-post-completion (candidate)
  "Append something or modify it after completion according to CANDIDATE.
If CANDIDATE is field, capitalize candidate if it starts with uppercase
character.  And append colon and space after field inserted.
If CANDIDATE is package name, append version constraint after that."
  (let ((type (get-text-property 0 :type candidate))
        (ver (get-text-property 0 :version candidate)))
    (cond
     ((eq type 'field)
      (let ((offset (company-cabal--current-offset))
            (end (point))
            start)
        (when (save-excursion
                (backward-char (length candidate))
                (setq start (point))
                (let ((case-fold-search nil))
                  (looking-at-p "[[:upper:]]")))
          (delete-region start end)
          (insert (mapconcat 'capitalize (split-string candidate "-") "-")))
        (insert ": ")
        (let ((col (+ company-cabal-field-value-offset offset)))
          (if (> col (current-column))
              (move-to-column col t)))))
     ((and ver company-cabal-version-modifier)
      (insert (funcall company-cabal-version-modifier ver))))))

(defun company-cabal--find-current-section ()
  "Find the current section name."
  (catch 'result
    (save-excursion
      (while (re-search-backward company-cabal--section-regexp nil t)
        (let ((section (match-string-no-properties 2)))
          (when (member section company-cabal--sections)
            (throw 'result (downcase section))))))))

(defun company-cabal--find-parent (offset)
  "Find the parent field or section.
This returns the first field or section with less than given OFFSET."
  (catch 'result
    (let ((ret (forward-line 0)))
      (while (>= ret 0)
        (when (and
               (looking-at "^\\([[:space:]]*\\)\\([[:word:]]+\\)\\(:\\)?")
               (if (member (match-string-no-properties 2) '("if" "else"))
                   (progn
                     (setq offset (string-width (match-string-no-properties 1)))
                     nil)
                 (< (string-width (match-string-no-properties 1)) offset)))
          (throw 'result
                 (cons (if (match-string 3) 'field 'section)
                       (downcase (match-string-no-properties 2)))))
        (setq ret (forward-line -1))))))

(defun company-cabal--find-context ()
  "Find the completion context at the current point."
  (save-excursion
    (if (looking-back "^\\([[:space:]]*\\)[^[:space:]]*" nil)
        (let ((offset (string-width (match-string-no-properties 1))))
          (if (= offset 0)
              '(top)
            (company-cabal--find-parent offset)))
      (forward-line 0)
      (cond
       ((looking-at company-cabal--section-regexp)
        (cons 'sectval (downcase (match-string-no-properties 2))))
       ((looking-at company-cabal--field-regexp)
        (cons 'field (downcase (match-string-no-properties 2))))
       ((looking-at "^\\([[:space:]]*\\)")
        (company-cabal--find-parent
         (string-width (match-string-no-properties 1))))))))

(defun company-cabal--get-directories ()
  "Get top level directories."
  (let* ((file (buffer-file-name))
         (dir (or (and file (file-name-directory file)) "."))
         result)
    (dolist (f (directory-files dir) result)
      (when (and (file-directory-p f)
                 (not (eq (string-to-char f) ?.)))
        (setq result (cons f result))))))

(defun company-cabal--list-packages ()
  "List installed packages via ghc-pkg."
  (or company-cabal--packages
      (setq company-cabal--packages
            (mapcar
             (lambda (x)
               (when (string-match "^\\(.+\\)-\\([[:digit:].]+\\)$" x)
                 (let ((pkg (match-string 1 x))
                       (ver (match-string 2 x)))
                   (put-text-property 0 1 :version ver pkg)
                   pkg)))
             (company-cabal--get-packages)))))

(defun company-cabal--get-packages ()
  "Get list of packages in the current cabal project."
  (let ((pkgdb (company-cabal--get-package-db)))
    (split-string
     (apply #'company-cabal--get-process-output
      "ghc-pkg"
      "list"
       "--simple-output"
       (when pkgdb (list "-f" pkgdb))))))

(defun company-cabal--get-package-db ()
  "Get sandbox package DB directory if any."
  (when (file-exists-p "cabal.sandbox.config")
    (with-temp-buffer
      (insert-file-contents "cabal.sandbox.config")
      (goto-char (point-min))
      (when (re-search-forward
             "^package-db:[[:space:]]*\\(.*?\\)[[:space:]]*$" nil t)
        (match-string 1)))))

(defun company-cabal--get-ghc-options ()
  "Get list of ghc options by ghc --show-options.
It is supported by ghc version >= 7.8."
  (or company-cabal--ghc-options
      (when (version<= "7.8" (company-cabal--get-ghc-version))
        (setq company-cabal--ghc-options
              (cdr
               (cl-delete-if
                (lambda (x) (string-match-p "^--" x))
                (split-string
                 (company-cabal--get-process-output
                  "ghc" "--show-options"))))))))

(defun company-cabal--get-ghc-extensions ()
  "Get list of supported extensions by ghc --supported-extensions."
  (or company-cabal--ghc-extensions
      (setq company-cabal--ghc-extensions
            (split-string
             (company-cabal--get-process-output
              "ghc" "--supported-extensions")))))

(defun company-cabal--get-ghc-version ()
  "Get version string of ghc command."
  (replace-regexp-in-string
   "[\r\n]*" ""
   (company-cabal--get-process-output "ghc" "--numeric-version")))

(defun company-cabal--get-process-output (cmd &rest args)
  "Return process output of CMD as string.
It takes optional command line arguments, ARGS."
  (with-output-to-string
    (with-current-buffer
      standard-output
      (when (company-cabal--stack-project-p)
        (setq args (cons "exec" (cons "--" (cons cmd args))))
        (setq cmd "stack"))
      (apply #'call-process cmd nil t nil args))))

(defun company-cabal--stack-project-p ()
  "Return non-nil if the project is built with stack.
True if \".stack-work\" directory exists and stack command is in PATH."
  (and (file-directory-p ".stack-work")
       (executable-find "stack")))

(defun company-cabal--in-comment-p ()
  "Return whether the current point is in comment or not."
  (save-excursion
    (forward-line 0)
    (looking-at-p "^[[:space:]]*--")))

(defun company-cabal--current-offset ()
  "Return the offset value of the current line."
  (if (looking-back "^\\([[:space:]]*\\).*" nil)
      (string-width (match-string-no-properties 1))
    0))

;;;###autoload
(defun company-cabal (command &optional arg &rest ignored)
  "`company-mode' completion back-end for `haskell-cabal-mode'.
Provide completion info according to COMMAND and ARG.  IGNORED, not used."
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-cabal))
    (prefix (and (derived-mode-p 'haskell-cabal-mode) (company-cabal-prefix)))
    (candidates (company-cabal-candidates arg))
    (ignore-case 'keep-prefix)
    (annotation (company-cabal-annotation arg))
    (post-completion (company-cabal-post-completion arg))))

(provide 'company-cabal)
;;; company-cabal.el ends here
