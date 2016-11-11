;;; jist.el --- Gist integration                     -*- lexical-binding: t; -*-

;; Copyright © 2014 Mario Rodas <marsam@users.noreply.github.com>

;; Author: Mario Rodas <marsam@users.noreply.github.com>
;; URL: https://github.com/emacs-pe/jist.el
;; Keywords: convenience
;; Version: 0.0.1
;; Package-Requires: ((emacs "24.4") (pkg-info "0.4") (dash "2.12.0") (let-alist "1.0.4") (magit "2.1.0") (request "0.2.0"))

;; This file is NOT part of GNU Emacs.

;;; License:

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

;;; Commentary:
;;
;; Yet another [Gist][] client for Emacs.
;;
;; ### Features:
;;
;; + Allows to create gists.
;; + Allows to delete/clone/star/unstar a gist.
;; + List your owned/starred gists.
;; + List public gists.
;; + List public gists from another github user.
;;
;; ### Configuration:
;;
;; To create anonymous gists is not necessary any configuration, but if you want
;; to create gists with your github account you need to obtain a `oauth-token`
;; with gist scope in https://github.com/settings/applications, and set it
;; through any of the following methods:
;;
;; + Add `(setq jist-github-token "TOKEN")` to your `init.el`.
;; + Add `oauth-token` to your `~/.gitconfig`: `git config --global github.oauth-token MYTOKEN`
;;
;; ### Usage:
;;
;; > **Warning**: By default, the functions `jist-region' and `jist-buffer'
;; > create **anonymous** gists.  To create gists with you configured account
;; > use `jist-auth-region' and `jist-auth-buffer'.
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
;; #### Tips:
;;
;; + In the current gist API the values of `gist_pull_url' and `git_push_url'
;;   use the HTTP protocol, but it's inconvenient to use the HTTP for pushes.
;;   To use the SSH protocol for pushes in cloned gists you need to add the
;;   following to your git-config(1):
;;
;;         [url "git@gist.github.com:/"]
;;             pushInsteadOf = "https://gist.github.com/"
;;
;; #### Related Projects:
;;
;; + [gist.el](https://github.com/defunkt/gist.el)
;; + [yagist.el](https://github.com/mhayashi1120/yagist.el)
;;
;; ### TODO:
;;
;; + [ ] List Gist forks.
;; + [ ] Allow gist edition with `org-mode'.
;; + [ ] Handle nicely 422 errors.  See: https://developer.github.com/v3/#client-errors
;; + [ ] Add pagination support with rfc5988 link headers.  See:
;;   - [Github api pagination](https://developer.github.com/v3/#pagination)
;;   - [Traversing with Pagination](https://developer.github.com/guides/traversing-with-pagination/).
;;   - [rfc5988](https://www.rfc-editor.org/rfc/rfc5988.txt)
;;
;; [Gist]: https://gist.github.com/

;;; Code:
(declare-function pkg-info-version-info "pkg-info" (library))

(eval-when-compile
  (require 'cl-lib)
  (require 'subr-x)
  (require 'let-alist))

(require 'json)
(require 'magit)
(require 'request)
(require 'url-expand)

(defgroup jist nil
  "Another Gist integration."
  :prefix "jist-"
  :group 'applications)

(defcustom jist-github-token nil
  "Oauth bearer token to interact with the Github API."
  :type 'string
  :safe #'stringp
  :group 'jist)

(defcustom jist-gist-directory (expand-file-name "~/.gists")
  "Directory where to the gists will be cloned."
  :type 'directory
  :group 'jist)

(defcustom jist-enable-default-authorized nil
  "Enable gists creation with associated account."
  :type 'boolean
  :safe #'booleanp
  :group 'jist)

(defcustom jist-anonymous-name nil
  "Enable gists creation without using the buffer name."
  :type 'boolean
  :safe #'booleanp
  :group 'jist)

;; We currently use per_page=100 (max value allowed), until we implement
;; pagination with RFC5988.
(defcustom jist-default-per-page 100
  "Default `per_page' argument used in list requests."
  :type 'integer
  :safe #'integerp
  :group 'jist)

(defcustom jist-disable-asking nil
  "Disable asking before destructive operations."
  :type 'boolean
  :safe #'booleanp
  :group 'jist)

(defcustom jist-use-descriptions nil
  "Whether to use gist descriptions for completions."
  :type 'boolean
  :safe #'booleanp
  :group 'jist)

(defconst jist-github-api-baseurl "https://api.github.com"
  "Base url for the github api.")

(defvar jist-gist-after-fork-hook nil)
(defvar jist-gist-after-create-hook nil)

(defvar jist-buffer-name "*Jist*"
  "Buffer name used for api responses.")

(defvar jist-debug-buffer-name "*Jist-Response*"
  "Buffer name used for api responses.")

(defvar jist-id-history nil)

(defvar-local jist-page nil
  "Current page number of the Gist API.")
(put 'jist-page 'permanent-local t)

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

(cl-defstruct (jist-gist (:constructor jist-gist-new))
  "A structure holding the information of a gist."
  id public description html-url git-pull-url)

(defun jist--gist-create (data)
  "Create a `jist-gist' struct from an api response DATA."
  (let-alist data
    (jist-gist-new :id .id
                   :public .public
                   :description .description
                   :html-url .html_url
                   :git-pull-url .git_pull_url)))

;; http://developer.github.com/v3/oauth/
(defun jist--oauth-token ()
  "Return the configured github token."
  (or jist-github-token
      (magit-get "github" "oauth-token")
      (user-error "You need to generate a personal access token.  https://github.com/settings/applications")))

;; XXX: https://developer.github.com/v3/#current-version
(defconst jist-default-headers
  `(("Accept" . "application/vnd.github.v3+json")
    ("User-Agent" . ,(format "jist.el/%s" (pkg-info-version-info 'jist)))))

(cl-defun jist--github-request (endpoint
                                &key
                                (type "GET")
                                (params nil)
                                (data nil)
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
  (request (url-expand-file-name endpoint jist-github-api-baseurl)
           :type type
           :data data
           :params params
           :headers headers
           :parser parser
           :success success
           :error error
           :timeout timeout
           :status-code status-code
           :sync sync))

(cl-defun jist-default-callback (&key data response error-thrown &allow-other-keys)
  (with-current-buffer (get-buffer-create jist-debug-buffer-name)
    (and error-thrown (message (error-message-string error-thrown)))
    (let ((inhibit-read-only t))
      (erase-buffer)
      (and (stringp data) (insert data))
      (let ((raw-header (request-response--raw-header response)))
        (unless (or (null raw-header) (string-empty-p raw-header))
          (insert "\n" raw-header))))))

(cl-defun jist--create-gist-data (&key
                                  files
                                  public
                                  (description (read-string "Description: ")))
  "Create a json for payload for gist from FILES alist.

DESCRIPTION and PUBLIC."
  (let ((public (if public t json-false))
        (files (cl-loop for (name . content) in files
                        collect `(,name . (("content" . ,content))))))
    (json-encode `(("files" . ,files)
                   ("public" . ,public)
                   ("description" . ,description)))))

(defun jist--file-name (&optional buffer)
  "Create a gist name based in BUFFER name."
  (let* ((filename (file-name-nondirectory (or (buffer-file-name buffer)
                                               (buffer-name buffer))))
         (extension (file-name-extension filename t)))
    (if jist-anonymous-name (concat "gistfile" extension) filename)))

;; TODO: Maybe download user gists in background
(defun jist--jist-items ()
  "Return gist from configured default user."
  (or jist-gists
      (-if-let (buffer (get-buffer jist-buffer-name))
          (buffer-local-value 'jist-gists buffer)
        (message "Not gist buffer found, be sure to call `jist-list' first")
        nil)))

(defun jist--read-gist-description (items)
  "Return an gist id from description from jist ITEMS."
  (let* ((gists (mapcar 'cdr-safe items))
         (description (completing-read "Gist description: " (mapcar 'jist-gist-description gists) nil t)))
    (-if-let (gist (seq-find (lambda (g)
                               (string= (jist-gist-description g) description))
                             gists))
        (jist-gist-id gist)
      (user-error "Not found gist with description: \"%s\"" description))))

(defun jist--read-gist-id ()
  "Read gist id."
  (let ((gist-id (and (derived-mode-p 'jist-gist-list-mode) (tabulated-list-get-id))))
    (list (or (and (not current-prefix-arg) gist-id)
              (let ((items (jist--jist-items)))
                (if (and jist-use-descriptions (> (length items) 0) (> (prefix-numeric-value current-prefix-arg) 0))
                    (jist--read-gist-description items)
                  (completing-read "Gist id: " items nil nil nil 'jist-id-history gist-id)))))))

(defun jist--kill-gist-html-url (data)
  "Given a Gist DATA api response, kill its html url."
  (let-alist data
    (kill-new (message .html_url))))

(defun jist--collect-file (file)
  "Return a cons cell \(file-name . contents\) from FILE."
  (let* ((visiting (find-buffer-visiting file))
         (buffer (or visiting (find-file-noselect file))))
    (with-current-buffer buffer
      (prog1
          (cons (file-name-nondirectory file) (buffer-substring-no-properties (point-min) (point-max)))
        (unless visiting (kill-buffer buffer))))))

(cl-defun jist--create-internal (data
                                 &key
                                 (authorized nil))
  "Internal gist creation."
  (jist--github-request "/gists"
                        :type "POST"
                        :data data
                        :parser #'json-read
                        :authorized (or authorized jist-enable-default-authorized)
                        :success (cl-function
                                  (lambda (&key data &allow-other-keys)
                                    (run-hook-with-args 'jist-gist-after-create-hook data)))))

(add-hook 'jist-gist-after-create-hook #'jist--kill-gist-html-url)

;;;###autoload
(cl-defun jist-dired (arg
                      &key
                      (public nil)
                      (authorized nil))
  "Create a gist from marked files(s) in dired.

With prefix ARG create a gist from file at point."
  (interactive "P")
  (let (files)
    (if arg
        (setq files (list (dired-get-filename)))
      (setq files (dired-get-marked-files)))
    (let ((data (jist--create-gist-data :files (mapcar #'jist--collect-file files)
                                        :public public)))
      (jist--create-internal data :authorized authorized))))

;;;###autoload
(defun jist-dired-auth (arg)
  "Create a authenticated gist from marked files(s) in dired.

With prefix ARG create a gist from file at point."
  (interactive "P")
  (jist-dired arg :authorized t))

;;;###autoload
(defun jist-dired-auth-public (arg)
  "Create a public gist from marked files(s) in dired.

With prefix ARG create a gist from file at point."
  (interactive "P")
  (jist-dired arg :authorized t :public t))

;;;###autoload
(cl-defun jist-region (&key
                       (beg (and (use-region-p) (region-beginning)))
                       (end (and (use-region-p) (region-end)))
                       (public nil)
                       (authorized nil))
  "Create a private gist from BEG and END region.

When PUBLIC is not nil creates a public gist."
  (interactive)
  (cl-assert (and beg end) t "No region selected")
  (let* ((files `((,(jist--file-name) . ,(buffer-substring-no-properties beg end))))
         (data (jist--create-gist-data :files files :public public)))
    (jist--create-internal data :authorized authorized)))

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

;;;###autoload
(defun jist-delete-gist (id)
  "Delete gist identified by ID."
  (interactive (jist--read-gist-id))
  (let ((gist (assoc-default id (jist--jist-items))))
    (when (or jist-disable-asking
              (y-or-n-p (if gist
                            (format "Do you really want to delete gist %s: \"%s\"? " id (jist-gist-description gist))
                          (format "Do you really want to delete gist %s? " id))))
      (jist--github-request (format "/gists/%s" id)
                            :type "DELETE"
                            :authorized t
                            :status-code '((204 . (lambda (&rest _) (message "Gist deleted"))))))))

;;;###autoload
(defun jist-print-gist (id)
  "Show a gist identified by ID and put into `kill-ring'."
  (interactive (jist--read-gist-id))
  (-if-let (gist (assoc-default id (jist--jist-items)))
      (kill-new (message (jist-gist-html-url gist)))
    (jist--github-request (format "/gists/%s" id)
                          :type "GET"
                          :parser #'json-read
                          :success (cl-function
                                    (lambda (&key data &allow-other-keys)
                                      (let-alist data
                                        (kill-new (message .html_url))))))))

;;;###autoload
(defun jist-browse-gist (id)
  "Show a gist identified by ID in a browser using `browse-url'."
  (interactive (jist--read-gist-id))
  (-if-let (gist (assoc-default id (jist--jist-items)))
      (browse-url (jist-gist-html-url gist))
    (jist--github-request (format "/gists/%s" id)
                          :type "GET"
                          :parser #'json-read
                          :success (cl-function
                                    (lambda (&key data &allow-other-keys)
                                      (let-alist data
                                        (browse-url .html_url)))))))

;;;###autoload
(defun jist-star-gist (id)
  "Star a gist identified by ID."
  (interactive (jist--read-gist-id))
  (jist--github-request (format "/gists/%s/star" id)
                        :type "PUT"
                        :authorized t
                        :headers '(("Content-Length" . "0"))
                        :status-code '((204 . (lambda (&rest _) (message "Gist starred"))))))

;;;###autoload
(defun jist-fork-gist (id)
  "Fork a gist identified by ID."
  (interactive (jist--read-gist-id))
  (jist--github-request (format "/gists/%s/forks" id)
                        :type "POST"
                        :authorized t
                        :status-code '((201 . (cl-function
                                               (lambda (&key data &allow-other-keys)
                                                 (run-hook-with-args 'jist-gist-after-fork-hook data)))))))

(add-hook 'jist-gist-after-fork-hook #'jist--kill-gist-html-url)

;;;###autoload
(defun jist-unstar-gist (id)
  "Unstar a gist identified by ID."
  (interactive (jist--read-gist-id))
  (jist--github-request (format "/gists/%s/star" id)
                        :type "DELETE"
                        :authorized t
                        :status-code '((204 . (lambda (&rest _) (message "Gist unstarred"))))))

;;;###autoload
(defun jist-clone-gist (id)
  "Clone gist identified by ID."
  (interactive (jist--read-gist-id))
  (let ((directory (expand-file-name id jist-gist-directory)))
    (if (magit-git-repo-p directory)
        (magit-status-internal directory)
      (-if-let (gist (assoc-default id (jist--jist-items)))
          (magit-clone (jist-gist-git-pull-url gist) directory)
        (jist--github-request (format "/gists/%s" id)
                              :type "GET"
                              :parser #'json-read
                              :authorized t
                              :success (cl-function
                                        (lambda (&key data &allow-other-keys)
                                          (let-alist data
                                            (magit-clone .git_pull_url directory)))))))))

;;;###autoload
(defun jist-edit-description (id)
  "Set description to a gist identified by ID."
  (interactive (jist--read-gist-id))
  (let* ((gist (assoc-default id (jist--jist-items)))
         (description (read-string "Description: " (and gist (jist-gist-description gist)))))
    (jist--github-request (format "/gists/%s" id)
                          :type "PATCH"
                          :authorized t
                          :parser #'json-read
                          :data (json-encode `(("description" . ,description))))))

(defun jist--menu-mark-delete (&optional _num)
  "Mark a gist for deletion and move to the next line."
  (interactive "p")
  (tabulated-list-put-tag "D" t))

(defun jist--menu-mark-clone (&optional _num)
  "Mark a gist for clone and move to the next line."
  (interactive "p")
  (tabulated-list-put-tag "C" t))

(defun jist--menu-mark-unmark (&optional _num)
  "Clear any mark on a gist and move to the next line."
  (interactive "p")
  (tabulated-list-put-tag " " t))

(defun jist--menu-execute ()
  "Perform marked gist list actions."
  (interactive)
  (unless (derived-mode-p 'jist-gist-list-mode)
    (error "The current buffer is not in Jist list mode"))
  (let (clone-list delete-list cmd gist-id)
    (save-excursion
      (goto-char (point-min))
      (while (not (eobp))
        (setq cmd (char-after))
        (unless (eq cmd ?\s)
          (setq gist-id (tabulated-list-get-id))
          (cond ((eq cmd ?D)
                 (push gist-id delete-list))
                ((eq cmd ?C)
                 (push gist-id clone-list))))
        (forward-line)))
    (unless (or delete-list clone-list)
      (user-error "No operations specified"))
    (mapc 'jist-clone-gist clone-list)
    (mapc 'jist-delete-gist delete-list)))

(defun jist--generate-table-entries (items)
  "Generate tabulated mode entries from jist ITEMS."
  (mapcar #'jist--generate-table-entry items))

(defun jist--item-from-response (data)
  "Given a api response DATA of a single gist return an tabulated-mode entry."
  (cons (assoc-default 'id data)
        (jist--gist-create data)))

(defun jist--generate-table-entry (item)
  "Return a table entry from a ITEM.

Where ITEM is a cons cell `(id . jist-gist)`."
  (cl-destructuring-bind (id . gist) item
    (list id (vector (jist-gist-id gist)
                     (if (eq (jist-gist-public gist) json-false) "" "●")
                     (or (jist-gist-description gist) "")
                     (jist-gist-html-url gist)))))

(defvar jist-gist-list-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map tabulated-list-mode-map)
    (define-key map "i" 'jist--menu-mark-clone)
    (define-key map "d" 'jist--menu-mark-delete)
    (define-key map "u" 'jist--menu-mark-unmark)
    (define-key map "x" 'jist--menu-execute)
    (define-key map "f" 'jist-fork-gist)
    (define-key map "c" 'jist-clone-gist)
    (define-key map "y" 'jist-print-gist)
    (define-key map "b" 'jist-browse-gist)
    (define-key map "k" 'jist-delete-gist)
    (define-key map "e" 'jist-edit-description)
    (define-key map "*" 'jist-star-gist)
    (define-key map "^" 'jist-unstar-gist)
    (define-key map "+" 'jist-fetch-next-page)
    map)
  "Keymap for `jist-gist-list-mode' buffers.")

(define-derived-mode jist-gist-list-mode tabulated-list-mode "Jist List"
  "List gists.

\\{jist-gist-list-mode-map}"
  (setq tabulated-list-format [("id" 20 t)
                               ("public" 6 t)
                               ("description" 60 t)
                               ("http_url" 60 nil)])
  (setq tabulated-list-padding 2)
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

;;;###autoload
(defun jist-fetch-next-page ()
  "Fetch the next page of the gists of a jist-list-mode buffer."
  (interactive)
  (when (eq major-mode 'jist-gist-list-mode)
    (setq jist-gists-already-fetched nil)
    (jist-gists (current-buffer)
                :user jist-gists-user
                :public jist-gists-public
                :starred jist-gists-starred
                :page (1+ (or jist-page 1)))))

(cl-defun jist-gists (buffer
                      &key
                      (user nil)
                      (public nil)
                      (starred nil)
                      (since nil)
                      (page jist-page)
                      (per-page jist-default-per-page))
  "Fetch a `jist-gists' list of gists."
  (or (buffer-local-value 'jist-gists-already-fetched buffer)
      (let* ((authorized (not (or user public)))
             (endpoint (cond (user (format "/users/%s/gists" user))
                             (public "/gists/public")
                             (starred "/gists/starred")
                             (t "/gists")))
             (params (append (and page `((page . ,(number-to-string page))))
                             (and since `((since . ,since)))
                             (and per-page `((per_page . ,(number-to-string per-page)))))))
        (jist--github-request endpoint
                              :type "GET"
                              :parser 'json-read
                              :params params
                              :authorized authorized
                              :success (cl-function
                                        (lambda (&key data &allow-other-keys)
                                          (message "jist request complete")
                                          (with-current-buffer buffer
                                            (setq jist-page page
                                                  jist-gists-already-fetched t)
                                            (let ((gists (mapcar #'jist--item-from-response data)))
                                              (setq jist-gists (if jist-page
                                                                   (append jist-gists gists)
                                                                 gists)))
                                            (setq tabulated-list-entries (jist--generate-table-entries jist-gists))
                                            (tabulated-list-print t))))))))

;;;###autoload
(cl-defun jist-list (&key
                     (page nil)
                     (user nil)
                     (public nil)
                     (starred nil))
  "Show the list of gists."
  (interactive)
  (let ((bufname (cond
                  (user (format "*%s-gists*" user))
                  (public "*Jist-Public*")
                  (starred "*Jist-Starred*")
                  (t jist-buffer-name))))
    (with-current-buffer (get-buffer-create bufname)
      (jist-gist-list-mode)
      (setq jist-gists-user user
            jist-gists-public public
            jist-gists-starred starred)
      (jist-gists (current-buffer) :user user :public public :starred starred :page page)
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
