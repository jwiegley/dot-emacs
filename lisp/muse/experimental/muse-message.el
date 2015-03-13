;;; muse-message.el --- publish a file as an email message

;; Copyright (C) 2004, 2005 Free Software Foundation, Inc.

;; This file is part of Emacs Muse.  It is not part of GNU Emacs.

;; Emacs Muse is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; Emacs Muse is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Emacs Muse; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This file is in experimental status due to unimplemented features.
;;
;; To make use of this file, put (require 'muse-message) in your .emacs.
;;
;; By default, the way to mark up an email message is to do the
;; following.
;;
;;  - Enter Message mode.  This is usually done automatically when you
;;    compose an email message using your Emacs mail client of choice.
;;
;;  - Use standard Muse markup instead of plain text for your message.
;;
;;  - When you are ready to see what the email message will look like,
;;    do `M-x muse-message-markup'.  This will make two versions of
;;    your message: plaintext and HTML.
;;
;;  - If you want to do further editing, simply undo your changes,
;;    edit some more, and run `muse-message-markup' when you're ready
;;    to send.
;;
;;  - Send the message.
;;
;; If you wish the markup to be automatic at the time of sending you
;; message (a risky proposition), just add `muse-message-markup' to
;; `message-send-hook'.

;;; Contributors:

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse E-Mail Publishing (via alternative/html)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'message)
(require 'footnote)

(require 'muse-publish)
(require 'muse-html)

(defgroup muse-message nil
  "Options controlling the behavior of Emacs Wiki Mail Markup."
  :group 'hypermedia
  :group 'muse-publish)

(defcustom muse-message-publishing-style "message"
  "Style used for publishing the alternative/text section of a message."
  :type 'string
  :group 'muse-message)

(defcustom muse-message-html-publishing-style "message-html"
  "Style used for publishing the alternative/html section of a message."
  :type 'string
  :group 'muse-message)

(defcustom muse-message-indent "  "
  "String used to pad indentend text."
  :type 'string
  :group 'muse-message)

(defcustom muse-message-style-sheet
  "body {
  background: white; color: black;
  margin-left: 3%; margin-right: 7%;
}

p { margin-top: 1% }
p.verse { margin-left: 3% }

.example { margin-left: 3% }

h2 {
  margin-top: 25px;
  margin-bottom: 0px;
}
h3 { margin-bottom: 0px; }"
  "Text to prepend to a Muse mail message being published.
This text may contain <lisp> markup tags."
  :type 'string
  :group 'muse-message)

(defcustom muse-message-html-header
  "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\">
<html>
  <head>
    <title><lisp>(muse-publishing-directive \"title\")</lisp></title>
    <meta name=\"generator\" content=\"muse-message.el\">
    <link rev=\"made\" href=\"<lisp>user-mail-address</lisp>\">
    <style type=\"text/css\">
      <lisp>muse-message-style-sheet</lisp>
    </style>
  </head>
  <body>
    <!-- Mail published by Emacs Muse begins here -->\n"
  "Text to prepend to a Muse mail message being published.
This text may contain <lisp> markup tags."
  :type 'string
  :group 'muse-message)

(defcustom muse-message-html-footer
  "\n    <!-- Mail published by Emacs Muse ends here -->
  </body>
</html>\n"
  "Text to append to a Muse mail message being published.
This text may contain <lisp> markup tags."
  :type 'string
  :group 'muse-message)

(defcustom muse-message-markup-functions
  '((link . muse-message-markup-link))
  "An alist of style types to custom functions for that kind of text.
For more on the structure of this list, see
`muse-publish-markup-functions'."
  :type '(alist :key-type symbol :value-type function)
  :group 'muse-message)

(defcustom muse-message-markup-strings
  '((rule            . "                               * * * *")
    (begin-verse     . "  ")
    (end-verse-line  . "\n  ")
    (verse-space     . "  ")
    (end-verse       . "")
    (begin-underline . "_")
    (end-underline   . "_")
    (begin-literal   . "`")
    (end-literal     . "'")
    (begin-emph      . "/")
    (end-emph        . "/")
    (begin-more-emph . "*")
    (end-more-emph   . "*")
    (begin-most-emph . "*/")
    (end-most-emph   . "/*"))
  "Strings used for marking up message text."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-message)

(defcustom muse-message-markup-tags
  '(("example"  t   nil muse-message-example-tag)
    ("contents" nil t   muse-message-contents-tag))
  "A list of tag specifications, for specially marking up text.
See the documentation for `muse-publish-markup-tags'."
  :type '(repeat (list (string :tag "Markup tag")
                       (boolean :tag "Expect closing tag" :value t)
                       (boolean :tag "Parse attributes" :value nil)
                       function))
  :group 'muse-message)

(defcustom muse-message-markup-specials nil
  "A table of characters which must be represented specially."
  :type '(alist :key-type character :value-type string)
  :group 'muse-message)

(defun muse-message-markup-link ()
  (let ((desc (match-string 2))
        (url (match-string 1)))
    (save-match-data
      (delete-region (match-beginning 0) (match-end 0))
      (when desc (insert desc))
      (save-excursion
        (Footnote-add-footnote)
        (insert url))
      "")))

(defun muse-message-example-tag (beg end)
  "Mark up example and code by simply indenting them."
  (muse-publish-escape-specials beg end)
  (kill-line 1)
  (goto-char end)
  (kill-line -1)
  (string-rectangle beg (point) muse-message-indent)
  (muse-publish-mark-read-only beg (point)))

;; Copied from `muse-publish-contents-tag'.
;; FIXME: Make this do something worthwhile.
(defun muse-message-contents-tag (beg end attrs)
  (set (make-local-variable 'muse-publish-generate-contents)
       (cons (copy-marker (point) t)
             (let ((depth (cdr (assoc "depth" attrs))))
               (or (and depth (string-to-number depth)) 2)))))

;;;###autoload
(defun muse-message-markup ()
  "Markup a wiki-ish e-mail message as HTML alternative e-mail.
This step is manual by default, to give the author a chance to review
the results and ensure they are appropriate.
If you wish it to be automatic (a risky proposition), just add this
function to `message-send-hook'."
  (interactive)
  (save-excursion
    (message-goto-body)
    (let ((text (buffer-substring-no-properties (point) (point-max)))
          (subject (message-fetch-field "subject"))
          (encoding (muse-html-encoding)))
      (delete-region (point) (point-max))
      (insert
       "<#multipart type=alternative>\n"
       "<#part type=text/plain charset=\"" encoding "\" nofile=yes>\n"
       (with-temp-buffer
         (insert text)
         (muse-publish-markup-buffer
          subject muse-message-publishing-style)
         (buffer-substring-no-properties (point-min) (point-max)))
       "\n<#part type=text/html charset=\"" encoding "\" nofile=yes>\n"
       (with-temp-buffer
         (insert text)
         (muse-publish-markup-buffer
          subject muse-message-html-publishing-style)
         (buffer-substring-no-properties (point-min) (point-max)))
       "<#/multipart>\n"))))

(muse-define-style "message"
                   :functions 'muse-message-markup-functions
                   :strings   'muse-message-markup-strings
                   :tags      'muse-message-markup-tags)

(muse-derive-style "message-html" "html"
                   :header 'muse-message-html-header
                   :footer 'muse-message-html-footer)

(muse-derive-style "message-xhtml" "xhtml"
                   :header 'muse-message-html-header
                   :footer 'muse-message-html-footer)

(provide 'muse-message)

;;; muse-message.el ends here
