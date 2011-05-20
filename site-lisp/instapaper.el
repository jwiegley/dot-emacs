;; instapaper.el --- add URLs to instapaper from emacs
;; Copyright (C) 2011 Jason F. McBrayer

;; Author: Jason F. McBrayer <jmcbray@carcosa.net>
;; Last update: 2011-02-17
;; Version: 0.8
;; URL: htts://bitbucket.org/jfm/emacs-instapaper
;; Contributors:

;; Instapaper.el is a set of functions to add urls to instapaper, a
;; simple tool to save web pages for reading later. Instapaper is at
;; https://www.instapaper.com/. This is not an official instapaper
;; client.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;; Requirements:
;; url.el, found in Emacs 22 or later.
;; w3m.el is recommended but not required.

;; Installation
;; Put instapaper.el somewhere on your load-path
;; (require 'instapaper)
;; M-x customize-group instapaper
;;
;; Recommended keybindings:
;; (define-key global-map "\C-ci" instapaper-add-at-point)
;; (define-key identica-mode-map "i" 'instapaper-add-at-point)
;; (define-key w3m-mode-map "i" 'instapaper-add-from-w3m)
;;
;; Note that passwords are not required on instapaper. You must have
;; an instapaper account ot use this package; it will not create one
;; for you.
;;

;; Use
;; To save a url to read later, use M-x instapaper-add,
;; instapaper-add-at-point, or instapaper-add-from-w3m.

;; Roadmap
;; 0.8:      Add urls successfully
;; 0.9:      More convenient functions for adding url at point or url of
;;           current buffer.
;; 1.0:      Better error handling
;; post-1.0: Add reading functions, maybe.


(require 'url)
(require 'browse-url)

(defvar instapaper-api-base "https://www.instapaper.com/api/"
  "Base URL for all instapaper API functions")
(defvar instapaper-auth-url (concat instapaper-api-base "authenticate")
  "URL for method for validating an instapaper username and password")
(defvar instapaper-add-url (concat instapaper-api-base "add")
  "URL for method for adding a URL to instapaper")

(defconst instapaper-version "0.9"
  "Version of instapaper.el")

(defcustom instapaper-username ""
  "Username or email address to use for instapaper authentication"
  :type 'string
  :group 'instapaper)

(defcustom instapaper-password ""
  "Password (if any) to use for instapaper authentication"
  :type 'string
  :group 'instapaper)


(defun instapaper-add (url &optional title selection)
  "Add url to instapaper"
  (interactive "sURL: ")
  (let* ((url-request-method "POST")
         (url-request-extra-headers
          '(("Content-Type" . "application/x-www-form-urlencoded")))
         (url-request-data (concat "username=" (url-hexify-string instapaper-username) "&"
                                   "password=" (url-hexify-string instapaper-password) "&"
                                   "url=" (url-hexify-string url) "&"
                                   (if title (concat "title="
                                                     (url-hexify-string title) "&") nil)
                                   (if selection (concat "selection="
                                                         (url-hexify-string selection)) nil))))
    (message "url-request-data: %s" url-request-data)
    (if (>= emacs-major-version 24)
        (url-retrieve instapaper-add-url 'instapaper-add-callback (list url title selection) t)
      (url-retrieve instapaper-add-url 'instapaper-add-callback (list url title selection)))))

(defun instapaper-add-callback (status url &optional title selection)
  "Callback for url-retrieve to add a URL to instapaper."
  (message url)
  (if status
      (message "FIXME: print failure method %s" status)
    (message "Successfully added URL %s to instapaper." url))
  (unless (get-buffer-process (current-buffer))
    (kill-buffer (current-buffer))))

(defun instapaper-add-at-point (&optional title selection)
  "Add url at point to instapaper"
  (interactive)
  (instapaper-add (browse-url-url-at-point) title selection))

(condition-case err
    (progn
      (require 'w3m)
      (defun instapaper-add-from-w3m (url &optional title selection)
        "Prompt, then add the most likely URL from w3m to instapaper.
Most likely URL is defined in order as link at point, url at point, selection,
or url of current page."
        (interactive (list (w3m-input-url
                            nil
                            (or (w3m-anchor)
                                (w3m-active-region-or-url-at-point)
                                w3m-current-url)
                            nil nil 'feeling-lucky)))
        (instapaper-add url title selection)))
  (file-error
   (message "w3m not available; instapaper support for w3m not loaded.")))

(provide 'instapaper)
