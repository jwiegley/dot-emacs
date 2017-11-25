;;; dockerfile-mode.el --- Major mode for editing Docker's Dockerfiles -*- lexical-binding: t -*-

;; Copyright (c) 2013 Spotify AB
;; Package-Requires: ((emacs "24") (s "1.12"))
;; Homepage: https://github.com/spotify/dockerfile-mode
;;
;; Licensed under the Apache License, Version 2.0 (the "License"); you may not
;; use this file except in compliance with the License. You may obtain a copy of
;; the License at
;;
;; http://www.apache.org/licenses/LICENSE-2.0
;;
;; Unless required by applicable law or agreed to in writing, software
;; distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
;; WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
;; License for the specific language governing permissions and limitations under
;; the License.

;;; Commentary:

;; Provides a major mode `dockerfile-mode' for use with the standard
;; `Dockerfile' file format.  Additional convenience functions allow
;; images to be built easily.

;;; Code:

(require 'sh-script)
(require 'rx)
(require 's)


(declare-function cygwin-convert-file-name-to-windows "cygw32.c" (file &optional absolute-p))

(defgroup dockerfile nil
  "dockerfile code editing commands for Emacs."
  :link '(custom-group-link :tag "Font Lock Faces group" font-lock-faces)
  :prefix "dockerfile-"
  :group 'languages)

(defcustom dockerfile-mode-hook nil
  "*Hook called by `dockerfile-mode'."
  :type 'hook
  :group 'dockerfile)

(defcustom dockerfile-use-sudo nil
  "Runs docker builder command with sudo."
  :type 'boolean
  :group 'dockerfile)

(defcustom dockerfile-build-args nil
  "List of --build-arg to pass to docker build.

Each element of the list will be passed as a separate
 --build-arg to the docker build command."
  :type '(repeat string)
  :group 'dockerfile)

(defvar dockerfile-font-lock-keywords
  `(,(cons (rx (or line-start "onbuild ")
               (group (or "from" "maintainer" "run" "cmd" "expose" "env" "arg"
                          "add" "copy" "entrypoint" "volume" "user" "workdir" "onbuild"
                          "label" "stopsignal" "shell" "healthcheck"))
               word-boundary)
           font-lock-keyword-face)
    ,@(sh-font-lock-keywords)
    ,@(sh-font-lock-keywords-2)
    ,@(sh-font-lock-keywords-1))
  "Default `font-lock-keywords' for `dockerfile mode'.")

(defvar dockerfile-mode-map
  (let ((map (make-sparse-keymap))
        (menu-map (make-sparse-keymap)))
    (define-key map "\C-c\C-b" 'dockerfile-build-buffer)
    (define-key map "\C-c\M-b" 'dockerfile-build-no-cache-buffer)
    (define-key map "\C-c\C-z" 'dockerfile-test-function)
    (define-key map "\C-c\C-c" 'comment-region)
    (define-key map [menu-bar dockerfile-mode] (cons "Dockerfile" menu-map))
    (define-key menu-map [dfc]
      '(menu-item "Comment Region" comment-region
                  :help "Comment Region"))
    (define-key menu-map [dfb]
      '(menu-item "Build" dockerfile-build-buffer
                  :help "Send the Dockerfile to docker build"))
    (define-key menu-map [dfb]
      '(menu-item "Build without cache" dockerfile-build-no-cache-buffer
                  :help "Send the Dockerfile to docker build without cache"))
    map))

(defvar dockerfile-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?# "<" table)
    (modify-syntax-entry ?\n ">" table)
    (modify-syntax-entry ?' "\"" table)
    (modify-syntax-entry ?= "." table)
    table)
  "Syntax table for `dockerfile-mode'.")

(define-abbrev-table 'dockerfile-mode-abbrev-table nil
  "Abbrev table used while in `dockerfile-mode'.")

(unless dockerfile-mode-abbrev-table
  (define-abbrev-table 'dockerfile-mode-abbrev-table ()))

(defun dockerfile-build-arg-string ()
  "Create a --build-arg string for each element in `dockerfile-build-args'."
  (mapconcat (lambda (arg) (concat "--build-arg " (shell-quote-argument arg)))
             dockerfile-build-args " "))

(defun dockerfile-standard-filename (file)
  "Convert the FILE name to OS standard.
If in Cygwin environment, uses Cygwin specific function to convert the
file name.  Otherwise, uses Emacs' standard conversion function."
  (if (fboundp 'cygwin-convert-file-name-to-windows)
      (s-replace "\\" "\\\\" (cygwin-convert-file-name-to-windows file))
    (convert-standard-filename file)))

(defvar dockerfile-image-name nil
  "Name of the dockerfile currently being used.
This can be set in file or directory-local variables.")
(define-obsolete-variable-alias 'docker-image-name 'dockerfile-image-name)

(defvar dockerfile-image-name-history nil
  "History of image names read by `dockerfile-read-image-name'.")

(defun dockerfile-read-image-name ()
  "Read a docker image name."
  (read-string "Image name: " dockerfile-image-name 'dockerfile-image-name-history))


;;;###autoload
(defun dockerfile-build-buffer (image-name &optional no-cache)
  "Build an image called IMAGE-NAME based upon the buffer.
If prefix arg NO-CACHE is set, don't cache the image."
  (interactive (list (dockerfile-read-image-name) prefix-arg))
  (save-buffer)
  (if (stringp image-name)
      (compilation-start
       (format
        "%sdocker build %s -t %s %s -f %s %s"
        (if dockerfile-use-sudo "sudo " "")
        (if no-cache "--no-cache" "")
        (shell-quote-argument image-name)
        (dockerfile-build-arg-string)
        (shell-quote-argument (dockerfile-standard-filename (buffer-file-name)))
        (shell-quote-argument (dockerfile-standard-filename default-directory)))
       nil
       (lambda (_) (format "*docker-build-output: %s *" image-name)))
    (print "dockerfile-image-name must be a string, consider surrounding it with double quotes")))

;;;###autoload
(defun dockerfile-build-no-cache-buffer (image-name)
  "Build an image called IMAGE-NAME based upon the buffer without cache."
  (interactive (list (dockerfile-read-image-name)))
  (dockerfile-build-buffer image-name t))

;;;###autoload
(define-derived-mode dockerfile-mode prog-mode "Dockerfile"
  "A major mode to edit Dockerfiles.
\\{dockerfile-mode-map}
"
  (set-syntax-table dockerfile-mode-syntax-table)
  (set (make-local-variable 'require-final-newline) mode-require-final-newline)
  (set (make-local-variable 'comment-start) "#")
  (set (make-local-variable 'comment-end) "")
  (set (make-local-variable 'comment-start-skip) "#+ *")
  (set (make-local-variable 'parse-sexp-ignore-comments) t)
  (set (make-local-variable 'font-lock-defaults)
       '(dockerfile-font-lock-keywords nil t))
  (setq local-abbrev-table dockerfile-mode-abbrev-table))

;;;###autoload
(add-to-list 'auto-mode-alist '("Dockerfile\\'" . dockerfile-mode))

(provide 'dockerfile-mode)

;;; dockerfile-mode.el ends here
