;;; message-x.el -- customizable completion in message headers
;; Copyright (C) 1998 Kai Großjohann

;; $Id: message-x.el,v 1.23 2001/05/30 21:04:47 grossjoh Exp $

;; Author: Kai Grossjohann <grossjohann@ls6.informatik.uni-dortmund.de>
;; Keywords: news, mail, compose, completion

;; This file is not part of GNU Emacs.

;; This is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; The most recent version of this can always be fetched from the
;; following FTP site:
;; ls6-ftp.cs.uni-dortmund.de:/pub/src/emacs

;; Installation:
;;
;; You must be using Gnus 5 or higher for this to work.  Installation
;; is simple: just put this file somewhere in your load-path, run M-x
;; byte-compile-file RET, and put the following line in your .gnus file:
;;
;;      (require 'message-x)
;;
;; Customization is possible through the two variables
;; message-x-body-function and message-x-completion-alist, which see.
;;
;; Purpose:
;;
;; This assigns a context-sensitive function to the TAB key in message
;; mode of Gnus.  When in a header line, this performs completion
;; based on which header we're in (for example, newsgroup name
;; completion makes sense in the Newsgroups header whereas mail alias
;; expansion makes sense in the To and Cc headers).  When in the
;; message body, this executes a different function, by default it is
;; indent-relative.
;;
;; To be more precise, the mechanism is as follows.  When point is in
;; a known header (a header mentioned in
;; `message-x-completion-alist'), then the completion function thus
;; specified is executed.  For the To and Cc headers, this could be
;; `bbdb-complete-name', for example.  Then we look if the completion
;; function has done anything.  If the completion function has NOT
;; done anything, then we invoke the function specified by
;; `message-x-unknown-header-function'.
;;
;; When point is in an unknown header (not mentioned in
;; `message-x-completion-alist'), then we invoke the function
;; specified by `message-x-unknown-header-function'.  This function
;; could advance point to the next header, for example.  (In fact,
;; that's the default behavior.)
;;
;; When point is not in a header (but in the body), then we invoke the
;; function specified by `message-x-body-function'.  By default, this
;; is `indent-relative' -- the default indentation function for text
;; mode.

;;; Setup Code:

(defconst message-x-version "$Id: message-x.el,v 1.23 2001/05/30 21:04:47 grossjoh Exp $"
  "Version of message-x.")

(require 'message)

;;; User Customizable Variables:

(defgroup message-x nil
  "Customizable completion in message headers.")

(defcustom message-x-body-function 'indent-relative
  "message-x-tab executes this if point is in the body of a message."
  :type '(function)
  :group 'message-x)

(defcustom message-x-unknown-header-function 'message-position-point
  "message-x-tab executes this if point is in an unknown header.
This function is also executed on known headers if the completion
function didn't find anything to do."
  :type '(function)
  :group 'message-x)

(defcustom message-x-completion-alist
  '(("\\([rR]esent-\\|[rR]eply-\\)?[tT]o:\\|[bB]?[cC][cC]:" .
     message-x-complete-name)
    ((if (boundp 'message-newgroups-header-regexp)
         message-newgroups-header-regexp
       message-newsgroups-header-regexp) . message-expand-group))
  "Table telling which completion function `message-x-tab' should invoke.
Table is a list of pairs (GROUP . FUNC).  GROUP is evaled to produce a
regexp specifying the header names.  See `mail-abbrev-in-expansion-header-p'
for details on the regexp.  If point is in that header, FUNC is invoked
via `message-x-call-completion-function'."
  :type '(repeat (cons string function))
  :group 'message-x)

(defcustom message-x-before-completion-functions nil
  "`message-x-tab' runs these functions before doing the actual
completion.  The functions are called with one argument, a string
specifying the current header name in lower case or nil, which
specifies the message body.  Also see `message-x-after-completion-hook'."
  :type 'hook
  :group 'message-x)

(defcustom message-x-after-completion-functions nil
  "`message-x-tab' runs these functions after doing the actual
completion.  The functions are called with one argument, a string
specifying the current header name in lower case or nil, which
specifies the message body.  Also see `message-x-before-completion-hook'."
  :type 'hook
  :group 'message-x)

;;; Internal variables:

(defvar message-x-displayed-completion-buffer-flag nil
  "Set to `t' from `completion-setup-hook'.
`message-x-call-completion-function' uses this to see if the
completion function has set up the *Completions* buffer.")

;;; Code:

(defun message-x-in-header-p ()
  "Returns t iff point is in the header section."
  (save-excursion
    (let ((p (point)))
      (goto-char (point-min))
      (and (re-search-forward (concat "^"
				      (regexp-quote mail-header-separator)
				      "$")
                              nil t)
	   (progn (beginning-of-line) t)
	   (< p (point))))))

(defun message-x-which-header ()
  "Returns the header we're currently in.  Returns nil if not in a header.
Example: returns \"to\" if we're in the \"to\" header right now."
  (and (message-x-in-header-p)
       (save-excursion
	 (beginning-of-line)
	 (while (looking-at "^[ \t]+") (forward-line -1))
	 (looking-at "\\([^:]+\\):")
	 (downcase (buffer-substring-no-properties (match-beginning 1)
						   (match-end 1))))))

(defun message-x-complete-name ()
  "Does name completion in recipient headers."
  (interactive)
  (unless (when abbrev-mode
            (message-x-call-completion-function 'expand-abbrev))
    (cond ((and (boundp 'eudc-server) eudc-server
                (boundp 'eudc-protocol) eudc-protocol)
           (condition-case nil
               (eudc-expand-inline)
             (error nil)))
          ((and (boundp 'bbdb-hashtable) (fboundp 'bbdb-complete-name))
           (let ((bbdb-complete-name-hooks nil))
             (bbdb-complete-name))))))

(defun message-x-set-displayed-completion-buffer-flag ()
  "Set `message-x-displayed-completion-buffer-flag' to t."
  (setq message-x-displayed-completion-buffer-flag t))
(add-hook 'completion-setup-hook
          'message-x-set-displayed-completion-buffer-flag)

(defun message-x-call-completion-function (func)
  "Calls the given completion function, then checks if completion was done.
When doing completion, the following cases are possible:
  - The current prefix was complete.
  - Some string was inserted.
  - A list of possible completions was displayed or updated.
In the first case, the completion function has not done anything, and
so `message-x-call-completion-function' returns nil.  In all other
cases, `message-x-call-completion-function' returns non-nil."
  (let* ((message-x-displayed-completion-buffer-flag nil)
         (cbuf (get-buffer-create "*Completions*"))
         (cbufcontents (save-excursion
                         (set-buffer cbuf)
                         (buffer-string)))
         (cwin (get-buffer-window cbuf))
         (thisline (buffer-substring
                    (save-excursion
                      (beginning-of-line)
                      (point))
                    (point)))
         (cws (window-start cwin)))
    (funcall func)
    (cond ((not (string= thisline
                         (buffer-substring
                          (save-excursion
                            (beginning-of-line)
                            (point))
                          (point))))
           t)
          (message-x-displayed-completion-buffer-flag
           (cond ((not (equal cwin (get-buffer-window cbuf)))
                  t)
                 ((not (string= cbufcontents
                               (save-excursion
                                 (set-buffer cbuf)
                                 (buffer-string))))
                  t)
                 ((/= cws (window-start (get-buffer-window cbuf)))
                  t)
                 (t nil))))))

(defun message-x-tab (&optional skip-completion)
  "Smart completion or indentation in message buffers.

Looks at the position of point to decide what to do.  If point is in
one of the headers specified by `message-x-completion-alist', then the
completion function specified there is executed.  If point is in
another header (not mentioned there), then the function specified by
`message-x-unknown-header-function' is executed.  If point is in the
body, the function specified by `message-x-body-function' is executed.

Completion is magic: after the completion function is executed, checks
are performed to see if the completion function has actually done
something.  If it has not done anything,
`message-x-unknown-header-function' is executed.  See the function
`message-x-call-completion-function' for details on how to check
whether the completion function has done something.

A non-nil optional arg SKIP-COMPLETION (prefix arg if invoked
interactively) means to not attempt completion.  Instead,
`message-x-unknown-header-function' function is called in all headers,
known or unknown."
  (interactive "P")
  (let* ((alist message-x-completion-alist)
         (which-header (message-x-which-header))
         header)
    (run-hook-with-args 'message-x-before-completion-functions which-header)
    (while (and (not skip-completion)
                alist
                (let ((mail-abbrev-mode-regexp (eval (caar alist))))
                  (not (mail-abbrev-in-expansion-header-p))))
      (setq alist (cdr alist)))
    (cond ((and alist (not skip-completion))
           (let ((p (point))
                 (func (cdar alist)))
             (unless (message-x-call-completion-function func)
               (funcall message-x-unknown-header-function))))
          ((message-x-in-header-p)
           (funcall message-x-unknown-header-function))
          (t
           (funcall message-x-body-function)))
    (run-hook-with-args 'message-x-after-completion-functions which-header)))

(define-key message-mode-map "\t" 'message-x-tab)

(provide 'message-x)
;;; message-x.el ends here
