;;; ivy-rich.el --- More friendly display transformer for ivy.

;; Copyright (C) 2016 Yevgnen Koh

;; Author: Yevgnen Koh <wherejoystarts@gmail.com>
;; Package-Requires: ((emacs "24.4") (ivy "0.8.0"))
;; Version: 0.0.4
;; Keywords: ivy

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

;; More friendly interface (display transformer) for ivy.
;; Usage:
;; (require 'ivy-rich)
;; (ivy-set-display-transformer 'ivy-switch-buffer 'ivy-rich-switch-buffer-transformer)
;;
;; See documentation on https://github.com/yevgnen/ivy-rich.

;;; Code:

(require 'cl-lib)
(require 'ivy)
(require 'subr-x)

(declare-function projectile-project-name "projectile")
(declare-function projectile-project-p "projectile")
(declare-function projectile-project-root "projectile")

;;; ivy-switch-buffer ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defgroup ivy-rich nil
  "More friendly interface (display transformer) for ivy."
  :group 'ivy)

(defcustom ivy-rich-switch-buffer-name-max-length
  32
  "Max length of buffer name.

For better user experience, the max length should be set to loose to
hold the buffer name."
  :type 'integer)

(defcustom ivy-rich-switch-buffer-mode-max-length
  18
  "Max length of mode name.

For better user experience, the max length should be set to loose to
hold the mode name."
  :type 'integer)
(defcustom ivy-rich-switch-buffer-project-max-length
  15
  "Max length of project name.

For better user experience, the max length should be set to loose
to hold the project name."
  :type 'integer)

(defcustom ivy-rich-switch-buffer-delimiter
  ""
  "Delimiter between columns."
  :type 'string)

(defcustom ivy-rich-switch-buffer-align-virtual-buffer
  nil
  "Whether to align virtual buffers just as true buffers or not."
  :type 'boolean)

(defcustom ivy-rich-path-style
  'relative
  "File path style.

When set to 'full or 'absolute, absolute path will be used.
When set to 'abbrev or 'abbreviate, abbreviated will be used. This
may not affect remote files since `abbreviate-file-name' does not
take care of them.
When set to 'relative or any other value, path relative to project
home will be used."
  :type 'symbol)

(defcustom ivy-rich-parse-remote-file-path
  nil
  "Whether `ivy-rich-path-style' should take care of remote file.

When `nil', always show absolute path of remote files,
otherwise, treat remote files as local files.

Sometimes when you are editing files with same names and same
directory structures in local and remote machines, setting this
option to `nil' would make the candidates easier to be
distinguished."
  :type 'boolean)

(defvar ivy-rich-switch-buffer-buffer-size-length 7)
(defvar ivy-rich-switch-buffer-indicator-length 4)

(defun ivy-rich-empty-p (str)
  (or (null str)
      (string-empty-p (string-trim str))))

(defun ivy-rich-switch-buffer-pad (str len &optional left)
  "Use space to pad STR to LEN of length.

When LEFT is not nil, pad from left side."
  (if (< (length str) len)
      (if left
          (concat (make-string (- len (length str)) ? ) str)
        (concat str (make-string (- len (length str)) ? )))
    str))

(defun ivy-rich-switch-buffer-user-buffer-p (buffer)
  "Check whether BUFFER-NAME is a user buffer."
  (let ((buffer-name
         (if (stringp buffer)
             buffer
           (buffer-name buffer))))
    (not (string-match "^\\*" buffer-name))))

(defun ivy-rich-switch-buffer-excluded-modes-p (modes)
  "Check whether major mode of current buffer is excluded in MODES."
  (not (memq major-mode modes)))

(defun ivy-rich-switch-buffer-shorten-path (file len)
  "Shorten the path of FILE until the length of FILE <= LEN.

For example, a path /a/b/c/d/e/f.el will be shortened to
   /a/…/c/d/e/f.el
or /a/…/d/e/f.el
or /a/…/e/f.el
or /a/…/f.el."
  (if (> (length file) len)
      (let ((new-file (replace-regexp-in-string "\\/?.+?\\/\\(\\(…\\/\\)?.+?\\)\\/.*" "…" file nil nil 1)))
        (if (string= new-file file)
            file
          (ivy-rich-switch-buffer-shorten-path new-file len)))
    file))

(defun ivy-rich-switch-buffer-format (columns)
  "Join all the non-nil column of COLUMNS."
  (mapconcat
   #'identity
   (cl-remove-if #'null columns)
   ivy-rich-switch-buffer-delimiter))

(defun ivy-rich-switch-buffer-indicators ()
  (let ((modified (if (and (buffer-modified-p)
                           (ivy-rich-switch-buffer-excluded-modes-p '(dired-mode shell-mode))
                           (ivy-rich-switch-buffer-user-buffer-p str))
                      "*"
                    ""))
        (readonly (if (and buffer-read-only
                           (ivy-rich-switch-buffer-user-buffer-p str))
                      "!"
                    ""))
        (process (if (get-buffer-process (current-buffer))
                     "&"
                   ""))
        (remote (if (file-remote-p (or (buffer-file-name) default-directory))
                    "@"
                  "")))
    (propertize
     (ivy-rich-switch-buffer-pad (format "%s%s%s%s" remote readonly modified process) ivy-rich-switch-buffer-indicator-length)
     'face
     'error)))

(defun ivy-rich-switch-buffer-size ()
  (let ((size (buffer-size)))
    (ivy-rich-switch-buffer-pad
     (cond
      ((> size 1000000) (format "%.1fM " (/ size 1000000.0)))
      ((> size 1000) (format "%.1fk " (/ size 1000.0)))
      (t (format "%d " size)))
     ivy-rich-switch-buffer-buffer-size-length t)))

(defun ivy-rich-switch-buffer-buffer-name ()
  (propertize
   (ivy-rich-switch-buffer-pad str ivy-rich-switch-buffer-name-max-length)
   'face
   'ivy-modified-buffer))

(defun ivy-rich-switch-buffer-major-mode ()
  (propertize
   (ivy-rich-switch-buffer-pad
    (capitalize
     (replace-regexp-in-string "-" " " (replace-regexp-in-string "-mode" "" (symbol-name major-mode))))
    ivy-rich-switch-buffer-mode-max-length)
   'face
   'warning))

(defun ivy-rich-switch-buffer-project ()
  (if (not (bound-and-true-p projectile-mode))
      nil
    (propertize
     (ivy-rich-switch-buffer-pad
      (if (string= (projectile-project-name) "-")
          ""
        (projectile-project-name))
      ivy-rich-switch-buffer-project-max-length)
     'face
     'success)))

(defun ivy-rich-switch-buffer-path (project)
  (let* ((path-max-length (- (window-width (minibuffer-window))
                             ivy-rich-switch-buffer-name-max-length
                             ivy-rich-switch-buffer-indicator-length
                             ivy-rich-switch-buffer-buffer-size-length
                             ivy-rich-switch-buffer-mode-max-length
                             (if project ivy-rich-switch-buffer-project-max-length 0)
                             (* 4 (length ivy-rich-switch-buffer-delimiter))
                             2))        ; Fixed the unexpected wrapping in terminal
         ;; Find the project root directory or `default-directory'
         (root (file-truename
                (if (or (not project)
                        (not (projectile-project-p)))
                    default-directory
                  (projectile-project-root))))
         ;; Find the file name or `nil'
         (filename
          (if (buffer-file-name)
              (if (and (buffer-file-name)
                       (string-match "^https?:\\/\\/" (buffer-file-name))
                       (not (file-exists-p (buffer-file-name))))
                  nil
                (file-truename (buffer-file-name)))
            (if (eq major-mode 'dired-mode)
                (dired-current-directory)
              nil)))
         (path (cond ((or (memq ivy-rich-path-style '(full absolute))
                          (and (null ivy-rich-parse-remote-file-path)
                               (or (file-remote-p root))))
                      (expand-file-name (or filename root)))
                     ((memq ivy-rich-path-style '(abbreviate abbrev))
                      (abbreviate-file-name (or filename root)))
                     ((or (eq ivy-rich-path-style 'relative)
                          t)            ; make 'relative default
                      (if filename
                          (substring-no-properties filename (length root))
                        "")))))
    (ivy-rich-switch-buffer-pad
     (ivy-rich-switch-buffer-shorten-path path path-max-length)
     path-max-length)))

(defun ivy-rich-switch-buffer-virtual-buffer ()
  (let* ((filename (file-name-nondirectory (expand-file-name str)))
         (filename (ivy-rich-switch-buffer-pad
                    filename
                    (+ ivy-rich-switch-buffer-name-max-length
                       ivy-rich-switch-buffer-indicator-length
                       ivy-rich-switch-buffer-buffer-size-length
                       ivy-rich-switch-buffer-mode-max-length
                       (if (bound-and-true-p projectile-mode) ivy-rich-switch-buffer-project-max-length 0)
                       (* 4 (length ivy-rich-switch-buffer-delimiter)))))
         (filename (propertize filename 'face 'ivy-virtual))
         (path (file-name-directory str))
         (path (ivy-rich-switch-buffer-shorten-path path (- (window-width (minibuffer-window)) (length filename))))
         (path (ivy-rich-switch-buffer-pad path (- (window-width)
                                                   (length filename)
                                                   2)))  ; Fixed the unexpected wrapping in terminal
         (path (propertize path 'face 'ivy-virtual)))
    (ivy-rich-switch-buffer-format `(,filename ,path))))

;;;###autoload
(defun ivy-rich-switch-buffer-transformer (str)
  "Transform STR to more readable format.

Currently the transformed format is

| Buffer name | Buffer indicators | Major mode | Project | Path (Based on project root) |."
  (let ((buf (get-buffer str)))
    (cond (buf (with-current-buffer buf
                 (let* ((indicator  (ivy-rich-switch-buffer-indicators))
                        (size       (ivy-rich-switch-buffer-size))
                        (buf-name   (ivy-rich-switch-buffer-buffer-name))
                        (mode       (ivy-rich-switch-buffer-major-mode))
                        (project    (ivy-rich-switch-buffer-project))
                        (path       (ivy-rich-switch-buffer-path project)))
                   (ivy-rich-switch-buffer-format `(,buf-name ,size ,indicator ,mode ,project ,path)))))
          ((and (eq ivy-virtual-abbreviate 'full)
                ivy-rich-switch-buffer-align-virtual-buffer)
           (ivy-rich-switch-buffer-virtual-buffer))
          (t str))))

(provide 'ivy-rich)

;;; ivy-rich.el ends here
