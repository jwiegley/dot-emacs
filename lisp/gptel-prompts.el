;;; gptel-prompts --- Extra functions for use with gptel

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 19 May 2025
;; Version: 1.0
;; Keywords: ai gptel tools
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

(require 'cl-lib)
(require 'cl-macs)
(eval-when-compile
  (require 'cl))

(require 'gptel)

(defgroup gptel-prompts nil
  "Helper library for managing GPTel prompts (aka directives)."
  :group 'gptel)

(defcustom gptel-prompts-directory "~/.emacs.d/prompts"
  "*Directory where GPTel prompts are defined, one per file.

Note that files can be of different types, which will cause them
to be represented as directives differently:

  .txt, .md, .org    Purely textual prompts that are used as-is
  .el                Must be a Lisp list represent a conversation:
                       SYSTEM, USER, ASSISTANT, [USER, ASSISTANT, ...]
  .jinja, jinja2     A Jinja template supporting Emacs Lisp sexps"
  :type 'file
  :group 'gptel-prompts)

(defcustom gptel-prompts-file-regexp
  "\\.\\(txt\\|md\\|org\\|el\\|j\\(inja\\)?2?\\)\\'"
  "*Directory where GPTel prompts are defined, one per file.

Note that files can be of different types, which will cause them
to be represented as directives differently:

  .txt, .md, .org    Purely textual prompts that are used as-is
  .el                Must be a Lisp list represent a conversation:
                       SYSTEM, USER, ASSISTANT, [USER, ASSISTANT, ...]
  .jinja, .jinja2    A Jinja template supporting Emacs Lisp sexps
                       (note this requires templatel be installed)"
  :type 'regexp
  :group 'gptel-prompts)

(defcustom gptel-prompts-template-variables nil
  "*A list of names to strings used during template expansion."
  :type '(alist :key-type symbol :value-type string)
  :group 'gptel-prompts)

(defun gptel-prompts-process-file (file)
  (cond ((string-match "\\.el\\'" file)
         (goto-char (point-min))
         (read (current-buffer)))
        ((string-match "\\.j\\(inja\\)?2?\\'" file)
         (require 'templatel)
         (let ((str (buffer-string)))
           (delete-region (point-min) (point-max))
           (insert (templatel-render-string
                    str gptel-prompts-template-variables))
           (string-trim (buffer-string))))
        (t 
         (string-trim (buffer-string)))))

(defun gptel-prompts-read-directory (dir)
  "Read prompts from directory DIR and establish them in `gptel-directives'."
  (cl-loop for file in (directory-files dir t gptel-prompts-file-regexp)
           collect (cons (intern (file-name-sans-extension
                                  (file-name-nondirectory file)))
                         (with-temp-buffer
                           (insert-file-contents file)
                           (if (string-match "\\.el\\'" file)
                               (progn
                                 (goto-char (point-min))
                                 (read (current-buffer)))
                             (string-trim (buffer-string)))))))

(defun gptel-prompts-update ()
  "Update `gptel-directives' from files in `gptel-prompts-directory'."
  (interactive)
  (setq gptel-directives
        (gptel-prompts-read-directory gptel-prompts-directory)))

(provide 'gptel-prompts)
