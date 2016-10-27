;;; smart-tabs-mode.el --- Intelligently indent with tabs, align with spaces!

;; Copyright © 2011 John Croisant <jacius@gmail.com>
;; Copyright © 2011 Joel C. Salomon <joelcsalomon@gmail.com>
;; Copyright © 2012 Alan Pearce <alan@alanpearce.co.uk>
;; Copyright © 2012 Daniel Dehennin <daniel.dehennin@baby-gnu.org>
;; Copyright © 2013 Matt Renaud <mrenaud92@gmail.com>

;; Author: John Croisant <jacius@gmail.com>
;;         Alan Pearce <alan@alanpearce.co.uk>
;;         Daniel Dehennin <daniel.dehennin@baby-gnu.org>
;;         Matt Renaud <mrenaud92@gmail.com>
;; Maintainer: Joel C. Salomon <joelcsalomon@gmail.com>
;; URL: http://www.emacswiki.org/emacs/SmartTabs
;; Created: 19 Sep 2011
;; Version: 1.0
;; Keywords: languages

;; This file is not part of GNU Emacs.

;;; License:

;; This file is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 2 of the License, or
;; (at your option) any later version.
;;
;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this file.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This package provide a semantic way of using tab characters in
;; source code: tabs for indentation, spaces for alignment.
;;
;; It is derived from <http://www.emacswiki.org/emacs/SmartTabs>
;; with modifications by the various authors listed above.
;;
;; Modification history is at <https://github.com/jcsalomon/smarttabs>.

;;; Installation:

;; The easiest and preferred way to install smart-tabs-mode is to use
;; the package available on MELPA.
;;
;; Manual installation:
;;
;; Save smart-tabs-mode.el to a a directory on your load-path
;; (e.g., ~/.emacs.d/elisp), then add the following to your .emacs file:
;;
;;  (autoload 'smart-tabs-mode "smart-tabs-mode"
;;    "Intelligently indent with tabs, align with spaces!")
;;  (autoload 'smart-tabs-mode-enable "smart-tabs-mode")
;;  (autoload 'smart-tabs-advice "smart-tabs-mode")
;;  (autoload 'smart-tabs-insinuate "smart-tabs-mode")
;;

;;; Enabling smart-tabs-mode within language modes:

;; As of version 1.0 of this package, the easiest and preferred way to
;; enable smart-tabs-mode is with the smart-tabs-insinuate function;
;; for example,
;;
;;  (smart-tabs-insinuate 'c 'c++ 'java 'javascript 'cperl 'python
;;                        'ruby 'nxml)
;;
;; will enable smart-tabs-mode with all supported language modes.
;;
;; (See below for instructions on adding additional language support.)
;;
;; The old method of manually enabling smart-tabs-mode is still
;; available, but is no longer recommended; smart-tabs-insinuate
;; wraps the functionality below in a convenient manner.
;;
;; For reference, the basic manual method looks like this:
;;
;;  (add-hook 'MODE-HOOK 'smart-tabs-mode-enable)
;;  (smart-tabs-advice INDENT-FUNC TAB-WIDTH-VAR)
;;
;; Note that it might be preferable to delay calling smart-tabs-advice
;; until after the major mode is loaded and evaluated, so the lines
;; above would be better written like this:
;;
;;  (add-hook 'MODE-HOOK (lambda ()
;;                         (smart-tabs-mode-enable)
;;                         (smart-tabs-advice INDENT-FUNC TAB-WIDTH-VAR)))
;;
;; Here are some specific examples for a few popular languages:
;;
;;  ;; C
;;  (add-hook 'c-mode-hook 'smart-tabs-mode-enable)
;;  (smart-tabs-advice c-indent-line c-basic-offset)
;;  (smart-tabs-advice c-indent-region c-basic-offset)
;;
;;  ;; JavaScript
;;  (add-hook 'js2-mode-hook 'smart-tabs-mode-enable)
;;  (smart-tabs-advice js2-indent-line js2-basic-offset)
;;
;;  ;; Perl (cperl-mode)
;;  (add-hook 'cperl-mode-hook 'smart-tabs-mode-enable)
;;  (smart-tabs-advice cperl-indent-line cperl-indent-level)
;;
;;  ;; Python
;;  (add-hook 'python-mode-hook 'smart-tabs-mode-enable)
;;  (smart-tabs-advice python-indent-line-1 python-indent)

;;; Adding language support

;; Language support can be added through the use of the macro
;; `smart-tabs-add-language-support'. Pass in the symbol you wish
;; to use to identify the language, the mode hook, and a list
;; of cons cells containing (indent-line-function . offset-variable).
;; For example, if C++ mode was not provided by default it could be
;; added as follows:
;;
;; (smart-tabs-add-language-support c++ c++-mode-hook
;;   ((c-indent-line . c-basic-offset)
;;    (c-indent-region . c-basic-offset)))
;;
;; NOTE: All language support must be added before the call to
;;      `smart-tabs-insinuate'.

;;; Code:

(require 'advice)
(require 'cl-lib)

(defvar smart-tabs-mode nil
  "Define if smart-tabs-mode is enabled")


;;;###autoload
(defmacro smart-tabs-when (condition advice-list)
  (declare (indent 1))
  `(when ,condition
     ,@(smart-tabs-create-advice-list advice-list)))


;;;###autoload
(defmacro smart-tabs-create-advice-list (advice-list)
  `(cl-loop for (func . offset) in ,advice-list
            collect `(smart-tabs-advice ,func ,offset)))


;;;###autoload
(defmacro smart-tabs-create-language-advice (lang mode-hook advice-list &rest body)
  "Create a cons cell containing the actions to take to enable
`smart-tabs-mode' for the language LANG. This usually involved enabling
`smart-tabs-mode' through `smart-tabs-mode-enable' and adding a lambda
function to the MODE-HOOK for the specified language. This macro
simplifies the creation of such a cons cell."
  (declare (indent 2))
  `'(,lang . (lambda ()
               (add-hook ',mode-hook
                         (lambda ()
                           (smart-tabs-mode-enable)
                           ,@(smart-tabs-create-advice-list advice-list)
                           ,@(cl-loop for form in body
                                      collect (macroexpand form)))))))


(defvar smart-tabs-insinuate-alist
  `(,(smart-tabs-create-language-advice c c-mode-hook
       ((c-indent-line . c-basic-offset)
        (c-indent-region . c-basic-offset)))

    ,(smart-tabs-create-language-advice c++ c++-mode-hook
       ((c-indent-line . c-basic-offset)
        (c-indent-region . c-basic-offset)))

    ,(smart-tabs-create-language-advice java java-mode-hook
       ((c-indent-line . c-basic-offset)
        (c-indent-region . c-basic-offset)))

    ,(smart-tabs-create-language-advice javascript js2-mode-hook
       ((js2-indent-line . js2-basic-offset)))

    ,(smart-tabs-create-language-advice cperl cperl-mode-hook
       ((cperl-indent-line . cperl-indent-level)))

    ,(smart-tabs-create-language-advice python python-mode-hook
       ((python-indent-line . python-indent-offset)
        (python-indent-region . python-indent-offset))
       (smart-tabs-when (featurep 'python-mode)
         ((py-indent-line . py-indent-offset)
          (py-newline-and-indent . py-indent-offset)
          (py-indent-region . py-indent-offset))))

    ,(smart-tabs-create-language-advice ruby ruby-mode-hook
       ((ruby-indent-line . ruby-indent-level)))

    ,(smart-tabs-create-language-advice nxml nxml-mode-hook
       ((nxml-indent-line . nxml-child-indent))))

  "Alist of language name and their activation code.
Smarttabs is enabled in mode hook.")



(defmacro smart-tabs-mode/no-tabs-mode-advice (function)
  `(unless (ad-find-advice ',function 'around 'smart-tabs)
     (defadvice ,function (around smart-tabs activate)
       (if smart-tabs-mode
           (let ((indent-tabs-mode nil)) ad-do-it)
         ad-do-it))))

;;;###autoload
(define-minor-mode smart-tabs-mode
  "Intelligently indent with tabs, align with spaces!"

  :init-value nil

  (progn
    (smart-tabs-mode/no-tabs-mode-advice align)
    (smart-tabs-mode/no-tabs-mode-advice align-regexp)
    (smart-tabs-mode/no-tabs-mode-advice indent-relative)
    (smart-tabs-mode/no-tabs-mode-advice comment-dwim)
    (smart-tabs-mode/no-tabs-mode-advice comment-box)
    (smart-tabs-mode/no-tabs-mode-advice comment-indent)

    (unless
        (ad-find-advice 'indent-according-to-mode 'around 'smart-tabs)
      (defadvice indent-according-to-mode (around smart-tabs activate)
        (if smart-tabs-mode
            (let ((indent-tabs-mode indent-tabs-mode))
              (if (memq indent-line-function
                        '(indent-relative
                          indent-relative-maybe))
                  (setq indent-tabs-mode nil))
              ad-do-it)
          ad-do-it)))
    ))

;;;###autoload
(defun smart-tabs-mode-enable ()
  "Enable smart-tabs-mode."
  (smart-tabs-mode t))

;;;###autoload
(defmacro smart-tabs-advice (function offset)
  `(progn
     (defadvice ,function (around smart-tabs activate)
       (cond
        (smart-tabs-mode
         (save-excursion
           (beginning-of-line)
           (while (looking-at "\t*\\( +\\)\t+")
             (replace-match "" nil nil nil 1)))
         (setq tab-width tab-width)
         (let ((indent-tabs-mode t)
               (tab-width fill-column)
               (,offset fill-column))
           (unwind-protect
               (progn ad-do-it))))
        (t
         ad-do-it)))))

;;;###autoload
(defun smart-tabs-insinuate (&rest languages)
  "Enable smart-tabs-mode for LANGUAGES.
LANGUAGES is a list of SYMBOL or NAME as defined in
'smart-tabs-insinuate-alist' alist or a language using standard named
indent function and indent level.
"
  (mapc (lambda (lang)
          (let ((lang-map (assoc lang smart-tabs-insinuate-alist))
                (lang-param (smart-tabs-get-standard-language lang)))
            (cond ((and (null lang-map)
                        (not (null (car lang-param)))
                        (not (null (nth 1 lang-param)))
                        (not (null (nth 2 lang-param))))
                   (smart-tabs-guess-insinuate lang-param))
                  ((null lang-map)
                   (error (format "Unknown smart-tab-mode capable language '%s'" lang)))
                  (t (funcall (cdr lang-map))))))
        languages))


;;;###autoload
(defmacro smart-tabs-add-language-support (lang mode-hook advice-list &rest body)
  "Add support for a language not already in the `smart-tabs-insinuate-alist'."
  (declare (indent 2))
  `(add-to-list
    'smart-tabs-insinuate-alist
    (smart-tabs-create-language-advice ,lang ,mode-hook
      ,advice-list ,@body)))


(defun smart-tabs-guess-insinuate (lang-param)
  "Enable smart-tabs-mode if language respect standard naming.
Several languages define a '<LANGUAGE>-indent-line' function and
'<LANGUAGE>-indent-level' variable to control indentation.
LANG-PARAM is a list of HOOK INDENT-FUNCTION INDENT-LEVEL, if
thoses are defined, we use them."
  (let ((lang-hook (car lang-param))
        (indent-function (nth 1 lang-param))
        (indent-level (nth 2 lang-param)))
    (if (and (not (null lang-hook))
             (and (not (null indent-function))
                  (fboundp indent-function))
             (and (not (null indent-level))
                  (boundp indent-level)))
        (add-hook lang-hook
                  `(lambda ()
                     (smart-tabs-mode-enable)
                     (smart-tabs-advice ,indent-function ,indent-level))))))

(defun smart-tabs-get-standard-language (language)
  "Return a list of HOOK INDENT-FUNCTION INDENT-LEVEL for a language."
  (let ((indent-function (intern-soft (concat (symbol-name language) "-indent-line")))
        (indent-level (intern-soft (concat (symbol-name language) "-indent-level")))
        (lang-hook (intern-soft (concat (symbol-name language) "-mode-hook"))))
    (list lang-hook indent-function indent-level)))

(provide 'smart-tabs-mode)

;;; smart-tabs-mode.el ends here
