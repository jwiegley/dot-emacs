;;; jist.el --- Manage gists from emacs -*- lexical-binding: t; -*-

;; Copyright © 2014 Mario Rodas <marsam@users.noreply.github.com>

;; Author: Mario Rodas <marsam@users.noreply.github.com>
;; URL: https://github.com/emacs-pe/jist.el
;; Keywords: convenience
;; Version: 0.0.1
;; Package-Requires: ((emacs "24") (cl-lib "0.5") (magit "1.2.1") (request "0.2.0") (pkg-info "0.4"))

;; This file is NOT part of GNU Emacs.

;;; License:

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
;; [![Travis build status](https://travis-ci.org/emacs-pe/jist.el.png?branch=master)](https://travis-ci.org/emacs-pe/jist.el)
;;
;; Yet another [gist][] client for Emacs.
;;
;;; Features:
;; + Allows to create gists.
;; + Allows to delete/clone/star/unstar a gist.
;; + List your owned/starred gists.
;; + List public gists.
;; + List public gists from another github user.
;;
;;; Configuration:
;; To create anonymous gists is not necessary any configuration, but
;; if you want to create gists with your github account you need to
;; obtain a `oauth-token` with gist scope in
;; https://github.com/settings/applications, and set it through any of
;; the following methods:
;;
;; + Add `(setq jist-github-token "mytoken")` to your `init.el`.
;; + Add `oauth-token` to your `~/.gitconfig`: `git config github.oauth-token mytoken`
;;
;;; Usage:
;; > **Warning**: By default, the functions `jist-region' and
;; > `jist-buffer' create **anonymous** gists. To create gists with
;; > you configured account use `jist-auth-region' and
;; > `jist-auth-buffer'.
;;
;; + Create a gist from an active region:
;;
;;                             | public | anonymous
;;   ------------------------- | ------ | ---------
;;   `jist-auth-region'        |        |
;;   `jist-auth-region-public' | x      |
;;   `jist-region'             |        | x
;;   `jist-region-public'      | x      | x
;;
;; + Create a gist of the contents of the current buffer:
;;
;;                             | public | anonymous
;;   ------------------------- | ------ | ---------
;;   `jist-auth-buffer'        |        |
;;   `jist-auth-buffer-public' | x      |
;;   `jist-buffer'             |        | x
;;   `jist-buffer-public'      | x      | x
;;
;; You can set the variable `jist-enable-default-authorized' to non nil to
;; always use your configured account when creating gists.
;;
;;; Tips:
;; + In the current gist API the values of `gist_pull_url' and
;;   `git_push_url' use the HTTP protocol, but it's inconvenient to
;;   use the HTTP for pushes. To use the SSH protocol for pushes in
;;   cloned gists you need to add the following to your git-config(1)
;;
;;         [url "git@gist.github.com:/"]
;;             pushInsteadOf = "https://gist.github.com/"
;;
;;; TODO:
;; + [ ] Add pagination support with rfc5988 link headers. See:
;;   - [Github api pagination](https://developer.github.com/v3/#pagination)
;;   - [Traversing with Pagination](https://developer.github.com/guides/traversing-with-pagination/).
;;   - [rfc5988](https://www.rfc-editor.org/rfc/rfc5988.txt)
;;
;;; Related Projects:
;; + [gist.el](https://github.com/defunkt/gist.el)
;; + [yagist.el](https://github.com/mhayashi1120/yagist.el)
;;
;; [gist]: https://gist.github.com/
;; [magit]: https://magit.github.io/

;;; Code:
(declare-function pkg-info-version-info "pkg-info" (library))

(eval-when-compile (require 'cl-lib))

(require 'json)
(require 'url-util)

(require 'magit)
(require 'request)

(defgroup jist nil
  "Another gist integration."
  :prefix "jist-"
  :group 'applications)

(defcustom jist-github-token nil
  "Oauth bearer token to interact with the github api."
  :type 'string
  :group 'jist)

(defcustom jist-gist-directory (expand-file-name "~/.gists")
  "Directory where to the gists will be cloned."
  :type 'directory
  :group 'jist)

(defcustom jist-enable-default-authorized nil
  "Enable gists creation with associated account."
  :type 'boolean
  :group 'jist)

(defcustom jist-anonymous-name nil
  "Enable gists creation without using the buffer name."
  :type 'boolean
  :group 'jist)

;; We currently use per_page=100 (max value allowed), until we
;; implement pagination with rfc5988.
(defcustom jist-default-per-page 100
  "Default `per_page' argument used in list requests."
  :type 'integer
  :group 'jist)

(defcustom jist-disable-asking nil
  "Disable asking before destructive operations."
  :type 'boolean
  :group 'jist)

(defconst jist-github-api-baseurl "https://api.github.com"
  "Base url for the github api.")

(defvar jist-buffer-name "*Jist*"
  "Buffer name used for api responses.")

(defvar jist-debug-buffer-name "*Jist-Response*"
  "Buffer name used for api responses.")

(defvar-local jist-gists nil
  "An alist which holds items of the form `(id . jist-gist)`")
(put 'jist-gists 'permanent-local t)

(defvar-local jist-gists-user nil)
(put 'jist-gists-user 'permanent-local t)

(defvar-local jist-gists-public nil)
(put 'jist-gists-public 'permanent-local t)

(defvar-local jist-gists-starred nil)
(put 'jist-gists-starred 'permanent-local t)

(defvar-local jist-gists-already-fetched nil)
(put 'jist-gists-already-fetched 'permanent-local t)

(cl-defstruct (jist-gist (:constructor jist-gist--create))
  "A structure holding all the information of a gist."
  history forks owner comments_url user comments description updated_at
  created_at public files html_url git_push_url git_pull_url id commits_url
  forks_url url fork_of)

(defun jist--gist-create (data)
  "Create a `jist-gist' struct from an api response DATA."
  (apply 'jist-gist--create (cl-loop for (key . value)
                                     in data
                                     append (list (intern (format ":%s" key)) value))))

;; http://developer.github.com/v3/oauth/
(defun jist--oauth-token ()
  "Return the configured github token."
  (or jist-github-token
      (magit-get "github" "oauth-token")
      (error "You need to generate a personal access token.  https://github.com/settings/applications")))

(defun jist--github-endpoint (endpoint)
  "Return a github absolure url of an ENDPOINT."
  (let ((urlobj (url-generic-parse-url jist-github-api-baseurl)))
    (setf (url-filename urlobj) endpoint)
    (url-recreate-url urlobj)))

(defconst jist-default-headers
  `(("Accept" . "application/vnd.github.v3+json")
    ("User-Agent" . ,(format "jist.el/%s" (pkg-info-version-info 'jist)))))

(cl-defun jist-github-request (endpoint
                               &key
                               (type "GET")
                               (params nil)
                               (data nil)
                               (files nil)
                               (parser 'buffer-string)
                               (error 'jist-default-callback)
                               (success 'jist-default-callback)
                               (headers jist-default-headers)
                               (timeout nil)
                               (sync nil)
                               (status-code nil)
                               (authorized nil))
  "Process a request to a github api endpoint."
  (when authorized
    (setq headers (append headers
                          `(("Authorization". ,(format "Bearer %s" (jist--oauth-token)))))))
  (request (jist--github-endpoint endpoint)
           :type type
           :data data
           :params params
           :headers headers
           :data data
           :parser parser
           :success success
           :error error
           :timeout timeout
           :status-code status-code
           :files files
           :sync sync))

(cl-defun jist-default-callback (&key data response error-thrown &allow-other-keys)
  (with-current-buffer (get-buffer-create jist-debug-buffer-name)
    (erase-buffer)
    (when error-thrown
      (message "Error: %s" error-thrown))
    (when (stringp data)
      (insert data))
    (let ((hstart (point))
          (raw-header (request-response--raw-header response))
          (comment-start (or comment-start "//")))
      (unless (string= "" raw-header)
        (insert "\n" raw-header)
        (comment-region hstart (point))))))

(defun jist--create-gist-data (files &optional description public)
  "Create a json for payload for gist from FILES alist."
  (let ((public (or public json-false))
        (files (cl-loop for (name . content) in files
                        collect `(,name . (("content" . ,content))))))
    (json-encode `(("description" . ,(or description ""))
                   ("files" . ,files)
                   ("public" . ,public)))))

(defun jist--file-name (&optional buffer)
  "Create a gist name based in BUFFER name."
  (let* ((filename (file-name-nondirectory (or (buffer-file-name buffer)
                                               (buffer-name buffer))))
         (extension (file-name-extension filename t)))
    (if jist-anonymous-name (concat "gistfile" extension) filename)))

;;;###autoload
(cl-defun jist-region (&key
                       (beg (and (use-region-p) (region-beginning)))
                       (end (and (use-region-p) (region-end)))
                       (public nil)
                       (authorized nil))
  "Create a private gist from BEG and END region.

When PUBLIC is not nil creates a public gist."
  (interactive)
  (unless (and beg end)
    (error "No region selected"))
  (let* ((description (read-string "Description: "))
         (files `((,(jist--file-name) . ,(buffer-substring-no-properties beg end))))
         (data (jist--create-gist-data files description public)))
    (jist-github-request "/gists"
                         :type "POST"
                         :data data
                         :parser 'json-read
                         :authorized (or authorized jist-enable-default-authorized)
                         :success (cl-function
                                   (lambda (&key data  &allow-other-keys)
                                     (let ((gist-url (assoc-default 'html_url data)))
                                       (kill-new gist-url)
                                       (message "Gist '%s' created" gist-url)))))))

;;;###autoload
(defun jist-auth-region ()
  "Create an authorized gist from an active region."
  (interactive)
  (jist-region :authorized t))

;;;###autoload
(defun jist-region-public ()
  "Create a public gist from an active region."
  (interactive)
  (jist-region :public t))

;;;###autoload
(defun jist-auth-region-public ()
  "Create a public and authorized gist from an active region."
  (interactive)
  (jist-region :public t :authorized t))

;;;###autoload
(defun jist-buffer ()
  "Create a gist from the contents of the current buffer."
  (interactive)
  (jist-region :beg (point-min) :end (point-max)))

;;;###autoload
(defun jist-auth-buffer ()
  "Create an authorized gist from the contents of the current buffer."
  (interactive)
  (jist-region :beg (point-min) :end (point-max) :authorized t))

;;;###autoload
(defun jist-buffer-public ()
  "Create a public gist from the contents of the current buffer."
  (interactive)
  (jist-region :beg (point-min) :end (point-max) :public t))

;;;###autoload
(defun jist-auth-buffer-public ()
  "Create an authorized and public gist from the contents of the current buffer."
  (interactive)
  (jist-region :beg (point-min) :end (point-max) :public t :authorized t))

(defun jist--read-gist-id ()
  "Read gist id."
  (list (if (and (eq major-mode 'jist-gist-list-mode) (tabulated-list-get-id))
            (tabulated-list-get-id)
          (completing-read "Gist id: "
                           jist-gists
                           nil nil nil nil
                           (tabulated-list-get-id)))))

;;;###autoload
(defun jist-delete-gist (id)
  "Delete gist with ID."
  (interactive (jist--read-gist-id))
  (let* ((gist (assoc-default id jist-gists))
         (desc (and gist (jist-gist-description gist))))
    (when (or jist-disable-asking
              (y-or-n-p (format "Do you really want to delete gist %s: \"%s\"? " id (or desc ""))))
      (jist-github-request (format "/gists/%s" id)
                           :type "DELETE"
                           :authorized t
                           :status-code '((204 . (lambda (&rest _) (message "Gist deleted"))))
                           :success nil
                           :error (cl-function
                                   (lambda (&key error-thrown &allow-other-keys)
                                     (message "Error: %s" error-thrown)))))))

;;;###autoload
(defun jist-browse-gist (id)
  "Show a gist with ID in a browser."
  (interactive (jist--read-gist-id))
  (browse-url (format "https://gist.github.com/%s" id)))

;;;###autoload
(defun jist-star-gist (id)
  "Star a gist ID."
  (interactive (jist--read-gist-id))
  (jist-github-request (format "/gists/%s/star" id)
                       :type "PUT"
                       :authorized t
                       :status-code '((204 . (lambda (&rest _) (message "Gist starred"))))
                       :headers '(("Content-Length" . "0"))
                       :success nil
                       :error (cl-function
                               (lambda (&key error-thrown &allow-other-keys)
                                 (message "Error: %s" error-thrown)))))

;;;###autoload
(defun jist-unstar-gist (id)
  "Unstar a gist ID."
  (interactive (jist--read-gist-id))
  (jist-github-request (format "/gists/%s/star" id)
                       :type "DELETE"
                       :authorized t
                       :status-code '((204 . (lambda (&rest _) (message "Gist unstarred"))))
                       :success nil
                       :error (cl-function
                               (lambda (&key error-thrown &allow-other-keys)
                                 (message "Error: %s" error-thrown)))))

;;;###autoload
(defun jist-clone-gist (id)
  "Close gist ID."
  (interactive (jist--read-gist-id))
  (jist-github-request (format "/gists/%s" id)
                       :type "GET"
                       :parser 'json-read
                       :authorized t
                       :success (cl-function
                                 (lambda (&key data &allow-other-keys)
                                   (let* ((id (assoc-default 'id data))
                                          (pull-url (assoc-default 'git_pull_url data))
                                          (directory (expand-file-name id jist-gist-directory)))
                                     (message "Cloning %s in %s" pull-url directory)
                                     (magit-call-git "clone" pull-url directory)
                                     (find-file directory))))))

(defun jist--generate-table-entries (buffer)
  "Generate tabulated mode entries of a BUFFER."
  (mapcar #'jist--generate-table-entry (jist-gists buffer)))

(defun jist--item-from-response (data)
  "Given a api reponse DATA of a single gist return an item."
  (cons (assoc-default 'id data)
        (jist--gist-create data)))

(defun jist--generate-table-entry (item)
  "Return a table entry from a ITEM.

Where ITEM is a cons cell `(id . jist-gist)`."
  (cl-destructuring-bind (id . gist) item
    (list id (vector (jist-gist-id gist)
                     (if (eq (jist-gist-public gist) json-false) "" "●")
                     (or (jist-gist-description gist) "")
                     (jist-gist-html_url gist)))))

(defvar jist-gist-list-mode-map
  (let ((map (make-keymap)))
    (define-key map (kbd "O") #'jist-browse-gist)
    (define-key map (kbd "C") #'jist-clone-gist)
    (define-key map (kbd "S") #'jist-star-gist)
    (define-key map (kbd "U") #'jist-unstar-gist)
    (define-key map (kbd "D") #'jist-delete-gist)
    map)
  "Keymap for jist-gist-list-mode.")

(define-derived-mode jist-gist-list-mode tabulated-list-mode "Jist List"
  "List gists.

\\{jist-gist-list-mode-map}"
  (setq tabulated-list-format [("id" 20 nil)
                               ("public" 6 nil)
                               ("description" 60 nil)
                               ("http_url" 60 nil)])
  (add-hook 'tabulated-list-revert-hook #'jist-refetch-gists nil t)
  (tabulated-list-init-header))

;;;###autoload
(defun jist-refetch-gists ()
  "Refetch the gists of a jist-list-mode buffer."
  (interactive)
  (when (eq major-mode 'jist-gist-list-mode)
    (setq jist-gists-already-fetched nil)
    (jist-gists (current-buffer)
                :user jist-gists-user
                :public jist-gists-public
                :starred jist-gists-starred)))

(cl-defun jist-gists (buffer
                      &key
                      (user nil)
                      (public nil)
                      (starred nil)
                      (since nil)
                      (page nil)
                      (per-page jist-default-per-page))
  "Fetch a `jist-gists' list of gists."
  (with-current-buffer buffer
    (if jist-gists-already-fetched
        jist-gists
      (let* ((authorized (not (or user public)))
             (endpoint (cond (user (format "/users/%s/gists" user))
                             (public "/gists/public")
                             (starred "/gists/starred")
                             (t "/gists")))
             (params (append (and page `((page . ,(number-to-string page))))
                             (and since `((since . ,since)))
                             (and per-page `((per_page . ,(number-to-string per-page)))))))
        (jist-github-request endpoint
                             :type "GET"
                             :parser 'json-read
                             :params params
                             :authorized authorized
                             :success (cl-function
                                       (lambda (&key data &allow-other-keys)
                                         (message "jist request complete")
                                         (with-current-buffer buffer
                                           (setq jist-gists-already-fetched t
                                                 jist-gists (mapcar #'jist--item-from-response data)
                                                 tabulated-list-entries (jist--generate-table-entries buffer))
                                           (tabulated-list-print t)))))))))

;;;###autoload
(cl-defun jist-list (&key
                     (user nil)
                     (public nil)
                     (starred nil))
  "Show the list of gists."
  (interactive)
  (let* ((bufname (cond (user (format "*%s-gists*" user))
                        (public "*Jist-Public*")
                        (starred "*Jist-Starred*")
                        (t jist-buffer-name)))
         (buffer (get-buffer-create bufname)))
    (with-current-buffer buffer
      (jist-gist-list-mode)
      (setq jist-gists-user user
            jist-gists-public public
            jist-gists-starred starred)
      (jist-gists buffer :user user :public public :starred starred)
      (pop-to-buffer (current-buffer)))))

;;;###autoload
(defun jist-list-user (user)
  "Show a list of gist of a github USER."
  (interactive (list (read-string "username: ")))
  (jist-list :user user))

;;;###autoload
(defun jist-list-public ()
  "Show a list of public gists."
  (interactive)
  (jist-list :public t))

;;;###autoload
(defun jist-list-starred ()
  "Show a list of starred gists of the configured user."
  (interactive)
  (jist-list :starred t))

(provide 'jist)

;;; jist.el ends here
