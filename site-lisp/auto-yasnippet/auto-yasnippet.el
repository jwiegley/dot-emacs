;;; auto-yasnippet.el --- Quickly create disposable yasnippets

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/auto-yasnippet
;; Version: 0.3
;; Package-Requires: ((yasnippet "0.8.0"))

;; This file is not part of GNU Emacs

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Setup:
;;
;; 1. Download yasnippet from https://github.com/capitaomorte/yasnippet
;;    and set it up.
;;
;; 2. Put this file into your elisp folder.
;;
;; 3. In your .emacs file:
;;     (require 'auto-yasnippet)
;;     (global-set-key (kbd "H-w") #'aya-create)
;;     (global-set-key (kbd "H-y") #'aya-expand)

;;; Usage:
;; auto-yasnippet allows you to quickly write verbose code using an
;; example as a template.
;;
;; (1) A basic example
;;
;; Suppose we want to write:
;;
;; count_of_red = get_total("red");
;; count_of_blue = get_total("blue");
;; count_of_green = get_total("green");
;;
;; We write a template, using ~ to represent variables that we want to
;; replace:
;;
;; count_of_~red = get_total("~red");
;;
;; Call `aya-create' with point on this line, and the template is
;; converted to a value we want:
;;
;; count_of_red = get_total("red");
;;
;; Then call `aya-expand' and you can 'paste' additional instances of
;; the template. Yasnippet is active, so you can tab between
;; placeholders as usual.
;;
;; count_of_red = get_total("red");
;; count_of_ = get_total("");
;;
;; (2) Inline text
;;
;; ~ replaces the symbol after it. If you want to replace arbitrary
;; text, use Emacs-style backticks:
;;
;; `red'_total = get_total("`red'_values");
;;
;; (3) Multiple placeholders
;;
;; You can replace multiple values in a template, just like normal
;; yasnippet.
;;
;; In this example, our template has multiple lines, so we need to
;; select the relevant lines before calling `aya-create'.
;;
;; ~FooType get~Foo() {
;;     // Get the ~foo attribute on this.
;;     return this.~foo;
;; }
;;
;; We only fill in three placeholders in this example (the fourth is
;; the same as the third).

;;; Code:
(require 'yasnippet nil t)

(defgroup auto-yasnippet nil
  "Auto YASnippet."
  :group 'yasnippet)

(defcustom aya-persist-snippets-dir
  "~/.emacs.d/snippets"
  "Directory to save auto yasnippets."
  :type 'directory)

(defcustom aya-create-with-newline nil
  "If non-nil `aya-create' creates snippet with trailing newline."
  :type 'boolean)

(defvar aya-current ""
  "Used as snippet body, when `aya-expand' is called.")

(defvar aya-marker "~"
  "Used to mark fields and mirrors.
Another good option is \\$, if you don't care about LaTeX")

(defvar aya-marker-one-line "$"
  "Used to mark one mirror for `aya-create-one-line'.")

(defvar aya-field-regex "\\sw\\|\\s_"
  "Defines how the filed looks like.
With \"\\sw\", Foo_bar will expand to $1_bar.
But \"\\sw\\|\\s_\", Foo_bar will expand to $1.")

;; you can chain `aya-create' with a function of your choosing,
;; e.g. copy current line/region if there's no snippet
;; when `aya-create' is called.
(defvar aya-default-function nil
  "Function to call if no snippet markers were on line / in region.")
(make-variable-buffer-local 'aya-default-function)

(defun aya--maybe-append-newline (str)
  "Append newline to STR if `aya-create-with-newline' is non-nil."
  (if (and aya-create-with-newline
           (not (string= "\n" (substring str -1))))
      (concat str "\n")
    str))

;;;###autoload
(defun aya-create-one-line ()
  "A simplistic `aya-create' to create only one mirror.
You can still have as many instances of this mirror as you want.
It's less flexible than `aya-create', but faster.
It uses a different marker, which is `aya-marker-one-line'.
You can use it to quickly generate one-liners such as
menu.add_item(spamspamspam, \"spamspamspam\")"
  (interactive)
  (when aya-marker-one-line
    (let* ((beg (line-beginning-position))
           (end (line-end-position))
           (line (buffer-substring-no-properties beg (point)))
           (re (regexp-quote aya-marker-one-line)))
      (when (and (not (string-match (regexp-quote aya-marker) line))
                 (string-match re line))
        (setq line
              (aya--maybe-append-newline
               (concat
                (replace-regexp-in-string re "$1" line)
                (if (= (point) end) "" "$1")
                (buffer-substring-no-properties (point) end))))
        (delete-region beg end)
        (when aya-create-with-newline (delete-char 1))
        (setq aya-current line)
        (yas-expand-snippet line)))))

(defun aya--parse (str)
  "Parse STR."
  (let ((start 0)
        (mirror-idx 0)
        (mirror-tbl (make-hash-table :test 'equal))
        (regex (format
                "\\(?:`\\(?1:[^']+\\)'\\|%s\\(?1:\\(?:%s\\)+\\)\\)"
                aya-marker
                aya-field-regex))
        res)
    (while (string-match regex str start)
      (unless (= (match-beginning 0) start)
        (push (substring str start (match-beginning 0)) res))
      (let* ((mirror (match-string 1 str))
             (idx (gethash mirror mirror-tbl)))
        (unless idx
          (setq idx (cl-incf mirror-idx))
          (puthash mirror idx mirror-tbl))
        (push (cons idx mirror) res))
      (setq start (match-end 0)))
    (unless (= start (length str))
      (push (substring str start) res))
    (nreverse res)))

;;;###autoload
(defun aya-create ()
  "Works on either the current line, or, if `mark-active', the current region.
Removes `aya-marker' prefixes,
writes the corresponding snippet to `aya-current',
with words prefixed by `aya-marker' as fields, and mirrors properly set up."
  (interactive)
  (unless (aya-create-one-line)
    (let* ((beg (if (region-active-p)
                    (region-beginning)
                  (line-beginning-position)))
           (end (if (region-active-p)
                    (region-end)
                  (line-end-position)))
           (str (buffer-substring-no-properties beg end))
           (case-fold-search nil)
           (res (aya--parse str)))
      (when (cl-some #'consp res)
        (delete-region beg end)
        (insert (mapconcat
                 (lambda (x) (if (consp x) (cdr x) x))
                 res ""))
        (setq aya-current
              (aya--maybe-append-newline
               (mapconcat
                (lambda (x) (if (consp x) (format "$%d" (car x)) x))
                res "")))
        ;; try some other useful action if it's defined for current buffer
        (and (functionp aya-default-function)
             (funcall aya-default-function))))))

;;;###autoload
(defun aya-expand ()
  "Insert the last yasnippet created by `aya-create'."
  (interactive)
  (unless yas-global-mode
    (yas-global-mode))
  (if (region-active-p)
      (let ((str (buffer-substring-no-properties
                  (region-beginning)
                  (region-end))))
        (yas-expand-snippet (replace-regexp-in-string
                             "\\$1"
                             "$0"
                             aya-current))
        (insert str))
    (yas-expand-snippet aya-current)))

(defvar aya-invokation-buffer nil
  "The buffer where `yas-expand' was called.")

;; here's a use-case for this one:
;;
;; # -*- mode: snippet -*-
;; # name: println
;; # condition: (> aya-invokation-point 10)
;; # key: p
;; # --
;; System.out.println($0);
;;
;; # -*- mode: snippet -*-
;; # name: package
;; # condition: (< aya-invokation-point 10)
;; # key: p
;; # --
;; `(insert (concat "package " (java-package-name (buffer-file-name)) ";\n"))`
;;
;; Both snippets share the same key "p" based on the `aya-invokation-point'.
(defvar aya-invokation-point nil
  "The point in buffer where `yas-expand' was called.")

;; here's a use-case of this one:
;;
;; # -*- mode: snippet -*-
;; # name: short comment
;; # key: sc
;; # --
;; //———$1${1:$(make-string (- 47 aya-tab-position (length text)) ?—)}$0
;;
;; This snippet will produce comment separators of consistent length
;; no matter from which indent position it was called from
(defvar aya-tab-position nil
  "The distance from line beginning where `yas-expand' was called.")

;;;###autoload
(defun aya-open-line ()
  "Call `open-line', unless there are abbrevs or snippets at point.
In that case expand them.  If there's a snippet expansion in progress,
move to the next field.  Call `open-line' if nothing else applies."
  (interactive)
  (cond ((expand-abbrev))
        ((progn
           (unless yas-global-mode
             (yas-global-mode 1))
           (yas--snippets-at-point))
         (yas-next-field-or-maybe-expand))
        ((ignore-errors
           (setq aya-invokation-point (point))
           (setq aya-invokation-buffer (current-buffer))
           (setq aya-tab-position (- (point) (line-beginning-position)))
           (let ((yas-fallback-behavior 'return-nil))
             (yas-expand))))
        ((and (fboundp 'tiny-expand)
              (funcall 'tiny-expand)))
        (t
         (open-line 1))))

;;;###autoload
(defun aya-yank-snippet ()
  "Insert current snippet at point.
To save a snippet permanently, create an empty file and call this."
  (interactive)
  (unless (= 0 (buffer-size))
    (error "Must be called from an empty file"))
  (insert "# -*- mode: snippet -*-\n")
  (insert "# name: \n# key: \n# --\n")
  (insert aya-current))

(defun aya-insert-snippet-function-extra (name)
  "Insert the snippet body based on NAME."
  (let ((key (read-string "Snippet key: ")))
    (insert
     "# -*- mode: snippet -*-"
     "\n# contributor: " user-full-name
     "\n# name: " name
     "\n# key: " key
     "\n# --\n"
     aya-current)
    t))

(defun aya-insert-snippet-function-default (name)
  "Insert the snippet body based on NAME."
  (insert
   "# -*- mode: snippet -*-"
   "\n# contributor: " user-full-name
   "\n# name: " name
   "\n# key: "
   "\n# --\n"
   aya-current)
  nil)

(defvar aya-insert-snippet-function
  #'aya-insert-snippet-function-default
  "The function for inserting a snippet body.
When it returns non-nil, save and close the buffer after inserting.")

(defun aya-persist-snippet (name)
  "Persist the current snippet in file NAME.

The full path is `aya-persist-snippets-dir'/`major-mode'/NAME.

Make sure to configure yasnippet to scan `aya-persist-snippets-dir'
for snippets.

Use `yas/reload-all' after defining a batch of snippets,
or `yas-load-snippet-buffer' for the current one.

Customizing `aya-insert-snippet-function' affects the behavior."
  (interactive
   (if (eq aya-current "")
       (user-error "Aborting: You don't have a current auto-snippet defined")
     (list
      (read-string "Snippet name: "))))
  (let ((default-directory
         (format "%s/%S" aya-persist-snippets-dir major-mode)))
    (unless (file-exists-p default-directory)
      (make-directory default-directory t))
    (if (file-exists-p name)
        (user-error
         "A snippet called \"%s\" already exists in \"%s\""
         name default-directory)
      (with-current-buffer (find-file-noselect name)
        (if (funcall aya-insert-snippet-function name)
            (progn
              (save-buffer)
              (kill-buffer))
          (snippet-mode)
          (goto-char (point-min))
          (search-forward "key: ")
          (pop-to-buffer (current-buffer)))))))

(provide 'auto-yasnippet)

;;; auto-yasnippet.el ends here
