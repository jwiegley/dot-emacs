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
  "\\.\\(txt\\|md\\|org\\|el\\|j\\(inja\\)?2?\\|poet\\)\\'"
  "*Directory where GPTel prompts are defined, one per file.

Note that files can be of different types, which will cause them
to be represented as directives differently:

  .txt, .md, .org    Purely textual prompts that are used as-is
  .el                Must be a Lisp list represent a conversation:
                       SYSTEM, USER, ASSISTANT, [USER, ASSISTANT, ...]
  .poet              See https://github.com/character-ai/prompt-poet"
  :type 'regexp
  :group 'gptel-prompts)

(defcustom gptel-prompts-template-variables nil
  "*A list of names to strings used during template expansion."
  :type '(alist :key-type symbol :value-type string)
  :group 'gptel-prompts)

(defun gptel-prompts-process-poet (prompts)
  "Convert from a list of PROMPTS in Poet format, to GPTel.

For example:

  (((role . \"system\")
    (content . \"Sample\")
    (name . \"system instructions\"))
   ((role . \"system\")
    (content . \"Sample\")
    (name . \"further system instructions\"))
   ((role . \"user\")
    (content . \"Sample\")
    (name . \"User message\"))
   ((role . \"assistant\")
    (content . \"Sample\")
    (name . \"Model response\"))
   ((role . \"user\")
    (content . \"Sample\")
    (name . \"Second user message\")))

Becomes:

   (\"system instructions\nfurther system instructions\"
    (prompt \"User message\")
    (response \"Model response\")
    (prompt \"Second user message\"))"
  (let ((system "") result)
    (dolist (prompt prompts)
      (let ((content (alist-get 'content prompt))
            (role (alist-get 'role prompt)))
        (cond
         ((string= role "system")
          (setq system (if (string-empty-p system)
                           content
                         (concat "\n" content))))
         ((string= role "user")
          (setq result (cons (list 'prompt content) result)))
         ((string= role "assistant")
          (setq result (cons (list 'response content) result)))
         ((string= role "tool")
          (error "Tools not yet supported in Poet prompts"))
         (otherwise
          (error "Role not recognized in prompt: %s"
                 (pp-to-string prompt))))))
    (cons system (nreverse result))))

(defun gptel-prompts-process-file (file)
  (cond ((string-match "\\.el\\'" file)
         (with-temp-buffer
           (insert-file-contents file)
           (goto-char (point-min))
           (let ((lst (read (current-buffer))))
             (if (listp lst)
                 lst
               (error "Emacs Lisp prompts must evaluate to a list")))))
        ;; jww (2025-05-19): Support .json files directly
        ((string-match "\\.\\(j\\(inja\\)?2?\\|poet\\)\\'" file)
         `(lambda ()
            (require 'templatel)
            (require 'yaml)
            (with-temp-buffer
              (insert-file-contents ,file)
              (let ((str (buffer-string)))
                (delete-region (point-min) (point-max))
                (insert (mapcar #'yaml--hash-table-to-alist
                                (yaml-parse-string
                                 (templatel-render-string
                                  str gptel-prompts-template-variables))))
                (goto-char (point-min))
                (let ((lst (read (current-buffer))))
                  (if (listp lst)
                      (gptel-prompts-process-file lst)
                    (error "Poet prompts must evaluate to a list")))))))
        (t
         (with-temp-buffer
           (insert-file-contents file)
           (string-trim (buffer-string))))))

(defun gptel-prompts-read-directory (dir)
  "Read prompts from directory DIR and establish them in `gptel-directives'."
  (cl-loop for file in (directory-files dir t gptel-prompts-file-regexp)
           collect (cons (intern (file-name-sans-extension
                                  (file-name-nondirectory file)))
                         (gptel-prompts-process-file file))))

(defun gptel-prompts-update ()
  "Update `gptel-directives' from files in `gptel-prompts-directory'."
  (interactive)
  (setq gptel-directives
        (gptel-prompts-read-directory gptel-prompts-directory)))

(provide 'gptel-prompts)
