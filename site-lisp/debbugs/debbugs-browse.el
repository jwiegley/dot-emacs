;; debbugs-browse.el --- browse bug URLs with debbugs-gnu or debbugs-org

;; Copyright (C) 2015-2017 Free Software Foundation, Inc.

;; Author: Michael Albinus <michael.albinus@gmx.de>
;; Keywords: comm, hypermedia, maint
;; Package: debbugs

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This file provides a minor mode for browsing bug URLs with
;; `debbugs-gnu-bugs' or `debbugs-org-bugs'.

;;; Code:

(defcustom debbugs-browse-function 'debbugs-gnu-bugs
  "The debbugs function used for showing bugs.
This can be either `debbugs-gnu-bugs' or `debbugs-org-bugs'."
  :group 'debbugs-gnu
  :type '(choice (const debbugs-gnu-bugs)
		 (const debbugs-org-bugs))
  :version "25.1")

(defun debbugs-browse-url (url &optional _new-window)
  (when (and (stringp url)
	     (string-match
	      (format
	       "^%s\\(%s\\)?\\([[:digit:]]+\\)$"
	       "https?://debbugs\\.gnu\\.org/"
	       (regexp-quote "cgi/bugreport.cgi?bug="))
	      url))
    (funcall debbugs-browse-function (string-to-number (match-string 2 url)))
    ;; Return t for add-function mechanery.
    t))

;;;###autoload
(define-minor-mode debbugs-browse-mode
  "Browse GNU Debbugs bug URLs with debbugs-gnu or debbugs-org.
With a prefix argument ARG, enable Debbugs Browse mode if ARG is
positive, and disable it otherwise.  If called from Lisp, enable
the mode if ARG is omitted or nil.
The customer option `debbugs-browse-function' controls, which of
the two packages is used for showing bugs."
  nil
  ""
  nil
  (if debbugs-browse-mode
      (add-function
       :before-until (local 'browse-url-browser-function) 'debbugs-browse-url)
    (remove-function (local 'browse-url-browser-function) 'debbugs-browse-url)))

(provide 'debbugs-browse)
;;; debbugs-browse.el ends here
