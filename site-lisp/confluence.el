;;; confluence.el --- Emacs mode for interacting with confluence wikis

;; Copyright (C) 2008  Free Software Foundation, Inc.

;; Author: James Ahlborn
;; Author: Kyle Burton <kyle.burton@gmail.com>
;; URL: http://code.google.com/p/confluence-el/
;; Keywords: confluence, wiki, xmlrpc
;; Version: 1.4
;; Package-Requires: ((xml-rpc "1.6.4"))

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

;;
;; DOWNLOADING
;;
;; This module is available at Google Code:
;;
;;   http://code.google.com/p/confluence-el/
;;
;; INSTALLATION 
;;
;; You must set confluence-url in your .emacs file before using the
;; functions in this module.  It's best to place confluence.el and
;; xml-rpc.el on your load path; often ~/.emacs.d or ~/elisp.
;;
;; Some examples:
;;
;;   ;; loading xml-rpc.el may not be necessary, it depends on your
;;   ;; installed version of Emacs, it was necessary on 22.1.1.
;;   ;; Both xml-rpc.el and confluence.el should be on your load-path.
;;
;;   (require 'confluence)
;;   (setq confluence-url "http://intranet/confluence/rpc/xmlrpc")
;;
;; USING CONFLUENCE MODE
;;
;; To open a page, M-x confluence-get-page and enter the path to the
;; page, for example, to open a page in your home space: ~username/Tasks
;;
;; It is often convienient to bind this to a global key \C-xwf in your .emacs file:
;;   
;;    (global-set-key "\C-xwf" 'confluence-get-page)
;;
;; Once you have opened a page, made changes, simply saving the page
;; ("\C-x\C-s") will push the changes back to the wiki.
;;
;; To view the changes in your page versus what is in the wiki, type
;; \C-xw=, or run M-x confluence-ediff-current-page.
;;
;; Also, if you want keybindings for confluence-mode, you can put the
;; following in your .emacs file:
;;
;; (add-hook 'confluence-mode-hook
;;   (local-set-key "\C-xw" confluence-prefix-map)
;;   (local-set-key "\M-j" 'confluence-newline-and-indent)
;;   (local-set-key "\M-;" 'confluence-list-indent-dwim))
;;
;; LONGLINES
;;
;;   http://www.emacswiki.org/emacs-en/LongLines
;;
;; Confluence uses a wiki-markup that treats linebreask as <p> HTML
;; tags.  Since this is the case, it is very common for paragraphs in
;; the Confluence markup to wrap around your buffer multiple times.
;; The LongLines mode allows those lines to be viewed within Emacs
;; with 'soft' linebreaks - which are inserted automatically, or via
;; M-q.  This makes it much more pleasant to work with large
;; paragraphs of text in the Confluence markup without introducing
;; unwanted paragraphs.
;;
;; See below for more advice on using LongLines and confluence-mode.
;;
;;
;; EXAMPLE .emacs CONFIGURATION
;;
;; (require 'confluence)
;;
;; ;; note, all customization must be in *one* custom-set-variables block
;; (custom-set-variables
;;  ;; ... other custimization
;;
;;  ;; confluence customization
;;  '(confluence-url "http://intranet/confluence/rpc/xmlrpc")
;;  '(confluence-default-space-alist (list (cons confluence-url "your-default-space-name"))))
;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;; confluence editing support (with longlines mode)
;;
;; (autoload 'confluence-get-page "confluence" nil t)
;;
;; (eval-after-load "confluence"
;;   '(progn
;;      (require 'longlines)
;;      (progn
;;        (add-hook 'confluence-mode-hook 'longlines-mode)
;;        (add-hook 'confluence-before-save-hook 'longlines-before-revert-hook)
;;        (add-hook 'confluence-before-revert-hook 'longlines-before-revert-hook)
;;        (add-hook 'confluence-mode-hook '(lambda () (local-set-key "\C-j" 'confluence-newline-and-indent))))))
;;
;; ;; LongLines mode: http://www.emacswiki.org/emacs-en/LongLines
;; (autoload 'longlines-mode "longlines" "LongLines Mode." t)
;;
;; (eval-after-load "longlines"
;;   '(progn
;;      (defvar longlines-mode-was-active nil)
;;      (make-variable-buffer-local 'longlines-mode-was-active)
;;
;;      (defun longlines-suspend ()
;;        (if longlines-mode
;;            (progn
;;              (setq longlines-mode-was-active t)
;;              (longlines-mode 0))))
;;
;;      (defun longlines-restore ()
;;        (if longlines-mode-was-active
;;            (progn
;;              (setq longlines-mode-was-active nil)
;;              (longlines-mode 1))))
;;
;;      ;; longlines doesn't play well with ediff, so suspend it during diffs
;;      (defadvice ediff-make-temp-file (before make-temp-file-suspend-ll
;;                                              activate compile preactivate)
;;        "Suspend longlines when running ediff."
;;        (with-current-buffer (ad-get-arg 0)
;;          (longlines-suspend)))
;;
;;     
;;      (add-hook 'ediff-cleanup-hook 
;;                '(lambda ()
;;                   (dolist (tmp-buf (list ediff-buffer-A
;;                                          ediff-buffer-B
;;                                          ediff-buffer-C))
;;                     (if (buffer-live-p tmp-buf)
;;                         (with-current-buffer tmp-buf
;;                           (longlines-restore))))))))
;;
;; 

;;; Code:

(require 'xml-rpc)
(require 'url-http)
(require 'ediff)
(require 'thingatpt)
(require 'browse-url)
(require 'image-file)

(defgroup confluence nil
  "Support for editing confluence wikis."
  :prefix "confluence-")

(defcustom confluence-url nil
  "Url of the confluence service to interact with.  This must
point to the XML-RPC api URL for your confluence installation.

If your confluence installation is at http://intranet/confluence,
then the XML-RPC URL is probably
http://intranet/confluence/rpc/xmlrpc.  Setting this in your
.emacs is necessary before interacting with the Wiki."
  :group 'confluence
  :type 'string)

(defcustom confluence-default-space-alist nil
  "AList of default confluence spaces to use ('url' -> 'space')."
  :group 'confluence
  :type '(alist :key-type string :value-type string))

(defcustom confluence-search-max-results 20
  "Maximum number of results to return from a search."
  :group 'confluence
  :type 'integer)

(defcustom confluence-prompt-page-function 'cf-prompt-page-by-component
  "The function to used to prompt for pages when opening new pages."
  :group 'confluence
  :type 'function)

(defcustom confluence-min-page-completion-length 3
  "The minimum number of characters at which to attempt page completion.  Set to -1 to disable page completion."
  :group 'confluence
  :type 'integer)

(defcustom confluence-min-page-repeat-completion-length 3
  "The minimum number of new characters at which to re-attempt page completion."
  :group 'confluence
  :type 'integer)

(defcustom confluence-max-completion-results 30
  "The maximum number of results to find when attempting completion."
  :group 'confluence
  :type 'integer)

(defcustom confluence-coding-alist nil
  "Obsolete variable, no longer necessary."
  :group 'confluence
  :type '(alist  :key-type string :value-type coding-system))

(defcustom confluence-show-attachment-images window-system
  "If not nil, attachments which are images will be displayed as such (if
possible), otherwise images will be treated the same as other attachments."
  :group 'confluence
  :type 'boolean)

(defcustom confluence-save-credentials nil
  "If not nil, username and password will be saved after entry for subsequent re-login (in memory only).  This is
useful for long running emacs sessions."
  :group 'confluence
  :type 'boolean)

(defcustom confluence-save-page-minor-edits 'ask
  "Whether a page save should be considered a 'minor edit' (no notifications
sent).  Note, this feature is only enabled if the confluence server is version
2.10 or higher.
Possible values:
 `t'   -- Always save pages as minor edits.
 `ask' -- Ask on every page save.
 `nil' -- Never save pages as minor edits."
  :group 'confluence
  :type '(choice (const :tag "Always" t)
                 (const :tag "Ask" ask)
                 (const :tag "Never" nil)))

(defcustom confluence-save-page-comments 'major
  "Whether a version comment should be included with a page save.  Note, this
feature is only enabled if the confluence server is version 2.10 or higher.
Possible values:
 `t'     -- Always ask for a comment.
 `major' -- Only ask for comments for major edits.
 `nil'   -- Never ask for a comment."
  :group 'confluence
  :type '(choice (const :tag "Always" t)
                 (const :tag "Major Only" major)
                 (const :tag "Never" nil)))

(defvar confluence-before-save-hook nil
  "List of functions to be called before saving a confluence page.")

(defvar confluence-before-revert-hook nil
  "List of functions to be called before reverting a confluence page.")

(defvar confluence-login-token-alist nil
  "AList of 'url' -> 'token' login information.")

(defvar confluence-login-credential-alist nil
  "AList of 'url' -> ('username' . 'password') login information, if
`confluence-save-credentials' is t.")

(defvar confluence-server-info-alist nil
  "AList of 'url' -> 'server-info' information.")

(defvar confluence-path-history nil
  "History list of paths accessed.")

(defvar confluence-space-history nil
  "History list of spaces accessed.")

(defvar confluence-page-history nil
  "History list of pages accessed.")

(defvar confluence-search-history nil
  "History list of queries.")

(defvar confluence-label-history nil
  "History labels used.")

(defvar confluence-attachment-history nil
  "History labels used.")

(defvar confluence-page-url nil
  "The url used to load the current buffer.")
(make-variable-buffer-local 'confluence-page-url)
(put 'confluence-page-url 'permanent-local t)

(defvar confluence-page-struct nil
  "The full metadata about the page in the current buffer.")
(make-variable-buffer-local 'confluence-page-struct)
(put 'confluence-page-struct 'permanent-local t)

(defvar confluence-page-id nil
  "The id of the page in the current buffer.")
(make-variable-buffer-local 'confluence-page-id)
(put 'confluence-page-id 'permanent-local t)

(defvar confluence-browse-function nil
  "The function to use for browsing links in the current buffer.")
(make-variable-buffer-local 'confluence-browse-function)
(put 'confluence-browse-function 'permanent-local t)

(defvar confluence-load-info nil
  "The information necessary to reload the page.")
(make-variable-buffer-local 'confluence-load-info)
(put 'confluence-load-info 'permanent-local t)

(defvar confluence-tag-stack nil
  "TAGs style stack support for push (\\C-xw.) and pop (\\C-xw*)")

(defconst confluence-search-types (list (cons "content" t) (cons "title" t) (cons "label" t))
  "Supported search types.")

(defconst confluence-xml-substitute-special (fboundp 'xml-substitute-special)
  "Whether or not confluence can override `xml-substitute-special'.")

(defconst confluence-xml-escape-string (fboundp 'xml-escape-string)
  "Whether or not confluence can override `xml-escape-string'.")

(defconst confluence-xml-entity-alist
  '(("quot" . "\"")
    ("amp" . "&")
    ("lt" . "<")
    ("gt" . ">")
    ("apos" . "'"))
  "Basic xml entities.")

;; these are never set directly, only defined here to make the compiler happy
(defvar confluence-do-coding nil)
(defvar confluence-input-url nil)
(defvar confluence-switch-url nil)
(defvar confluence-completing-read nil)
(defvar confluence-no-push nil)

(defmacro with-quiet-rpc (&rest body)
  "Execute the forms in BODY with `url-show-status' set to nil."
  `(let ((url-show-status nil))
     ,@body))
  
(defun confluence-login (&optional arg)
  "Logs into the current confluence url, if necessary.  With ARG, forces
re-login to the current url."
  (interactive "P")
  (let ((confluence-input-url (cf-get-url)))
    (if arg
        (cf-set-struct-value 'confluence-login-token-alist
                             confluence-input-url nil))
    ;; we may need to prompt for a password while already at the minibuffer
    ;; prompt, so enable recursive minibuffers
    (let ((enable-recursive-minibuffers t)
          (credentials (and confluence-save-credentials
                            (cf-get-struct-value confluence-login-credential-alist confluence-input-url)))
          (cur-token (cf-get-struct-value confluence-login-token-alist
                                          confluence-input-url))
          (username nil)
          (password nil))
      (while (not cur-token)
        (condition-case err
            (progn
              (setq cur-token
                    (cf-rpc-execute-internal 
                     'confluence1.login
                     (setq username
                           (or (car-safe credentials)
                               (read-string (format "Confluence Username [%s]: " user-login-name)
                                            nil nil user-login-name t)))
                     (setq password
                           (or (cdr-safe credentials)
                               (read-passwd "Confluence Password: ")))))
              (cf-set-struct-value 'confluence-login-token-alist
                                   confluence-input-url cur-token)
              (if confluence-save-credentials 
                  (cf-set-struct-value 'confluence-login-credential-alist
                                       confluence-input-url (cons username password))))
          (error
           (progn
             (message "Failed logging in: %s" (error-message-string err))
             ;; clear any saved credentials (so re-attempts prompt for new info)
             (setq credentials nil)))))
      cur-token)))

;;;###autoload
(defun confluence-get-page (&optional page-name space-name anchor-name)
  "Loads a confluence page for the given SPACE-NAME and PAGE-NAME
into a buffer (if not already loaded) and switches to it.
Analogous to `find-file'.  Every time you navitage to a page with
this function (or M-. `confluence-get-page-at-point'), it is
saved off into a stack (`confluence-tag-stack') that you can then
pop back out of to return back through your navigation path (with
M-* `confluence-pop-tag-stack')."
  (interactive)
  (cf-prompt-page-info nil 'page-name 'space-name)
  (cf-show-page (cf-rpc-get-page-by-name space-name page-name) 
                anchor-name))

(defun confluence-get-page-with-url (&optional arg)
  "With ARG, prompts for the confluence url to use for the get
page call (based on `confluence-default-space-alist')."
  (interactive "P")
  (let ((confluence-switch-url arg)
        (confluence-input-url nil))
    (confluence-get-page)))

(defun confluence-get-page-at-point (&optional arg)
  "Opens the confluence page at the current point.  If the link is a url,
opens the page using `browse-url', otherwise attempts to load it as a
confluence page.  Analogous to M-. (`find-tag').  Any ARG is passed to
`confluence-get-page-with-url' if nothing is found at point."
  (interactive "P")
  (let ((url nil)
        (is-embedded-content nil))
    ;; look for normal links, image/embedded content links, or raw links
    (cond
     ((thing-at-point-looking-at "{include:[ \t]*\\([^|\n}]+\\)}")
      (setq url (match-string 1)))
     ((thing-at-point-looking-at "\\[\\(\\([^|\n]*\\)[|]\\)?\\([^]\n]+\\)\\]")
      (setq url (match-string 3)))
     ((thing-at-point-looking-at "[!]\\([^]|\n]+\\)\\([|]\\([^]\n]*\\)\\)?[!]")
      (setq url (match-string 1))
      (setq is-embedded-content t))
     ((thing-at-point-looking-at thing-at-point-url-regexp)
      (setq url (match-string 0))))
    ;; determine how to handle the link (may be straight-up url)
    (if url
        (progn
          (set-text-properties 0 (length url) nil url)
          (if (string-match thing-at-point-url-regexp url)
              (browse-url url)
            (progn
              (if (and is-embedded-content (not (string-match "\\^" url)))
                  ;; embedded content links are really just attachments
                  (setq url (concat "^" url)))
              (if confluence-browse-function
                  (funcall confluence-browse-function url)
                (cf-simple-browse-function url)))))
      (confluence-get-page-with-url arg))))

(defun confluence-get-parent-page ()
  "Loads a confluence page for the parent of the current
confluence page into a buffer (if not already loaded) and
switches to it."
  (interactive)
  (let ((parent-page-id (cf-get-struct-value confluence-page-struct "parentId" "0")))
    (if (equal parent-page-id "0")
        (message "Current page has no parent page")
      (cf-show-page (cf-rpc-get-page-by-id parent-page-id)))))

(defun confluence-get-attachment (&optional page-name space-name file-name 
                                            page-id)
  "Gets the attachment with the given info and optionally displaying it in a
buffer for viewing or downloading it to a local file."
  (interactive)
  ;; get page and space names if not given
  (cf-prompt-page-info "Attachment " 'page-name 'space-name
                       (cf-get-struct-value confluence-page-struct "title"))
  ;; find page-id if not given
  (if (not page-id)
      (with-quiet-rpc
        (setq page-id (cf-get-struct-value (cf-rpc-get-page-by-name
                                            space-name page-name) "id"))))
  ;; get file name if not given
  (if (not file-name)
      (let ((cur-attachments (with-quiet-rpc
                              (cf-result-to-completion-list
                               (cf-rpc-get-attachments page-id) "fileName"))))
        (if (= (length cur-attachments) 0)
            (message "Current page has no attachments...")
          (setq file-name (cf-read-string-simple "Confluence attachment file name: " 'confluence-attachment-history cur-attachments t)))))

  (if (and (cf-string-notempty page-id)
           (cf-string-notempty file-name))
      (let ((save-only-file-name nil))
        ;; determine if caller wants to view the file or merely download it
        (if (equal "d"
                   (cf-read-char "(v)iew confluence attachment or (d)ownload only [v]: " "[vd]" "v"))
            (setq save-only-file-name (expand-file-name 
                                       (read-file-name "Download file name: " 
                                                       nil file-name))))
        (cf-show-attachment page-name space-name file-name page-id 
                           save-only-file-name))))

(defun confluence-get-attachment-with-url (&optional arg)
  "With ARG, prompts for the confluence url to use for the get
attachment call (based on `confluence-default-space-alist')."
  (interactive "P")
  (let ((confluence-switch-url arg)
        (confluence-input-url nil))
    (confluence-get-attachment)))

(defun confluence-goto-anchor (&optional anchor-name)
  "Moves to the given ANCHOR-NAME in the current confluence buffer."
  (interactive)
  (if (not anchor-name)
      (let ((cur-anchors (cf-get-page-anchors)))
            (if (= (length cur-anchors) 0)
                (message "Current page has no anchors...")
              (setq anchor-name (cf-read-string-simple "Confluence Anchor Name: " 
                                                       nil cur-anchors t)))))
  (if (cf-string-notempty anchor-name)
      (let ((anchor-position nil))
        (save-excursion
          (goto-char (point-min))
          (setq anchor-position
                (search-forward (concat "{anchor:" anchor-name "}") nil t))
          ;; headings are also implicit anchors
          (if (not anchor-position)
              (setq anchor-position
                    (re-search-forward (concat "^h[1-9][.]\\s-+" (regexp-quote anchor-name)) nil t)))
          ;; 'top' and 'bottom' can be used as anchors in some situations
          (if (and (not anchor-position)
                   (string= "top" anchor-name))
              (setq anchor-position (point-min)))
          (if (and (not anchor-position)
                   (string= "bottom" anchor-name))
              (setq anchor-position (point-max))))
        (if anchor-position
            (goto-char anchor-position)
          (message "Could not find anchor %s in page..." anchor-name)))))

(defun confluence-create-page (&optional page-name space-name)
  "Creates a new confluence page for the given SPACE-NAME and
PAGE-NAME and loads it into a new buffer."
  (interactive)
  (cf-prompt-page-info "New " 'page-name 'space-name)
  (let ((new-page (list (cons "content" "")))
        (parent-page-id (cf-get-parent-page-id t space-name)))
    (cf-set-struct-value 'new-page "title" page-name)
    (cf-set-struct-value 'new-page "space" space-name)
    (if parent-page-id
        (cf-set-struct-value 'new-page "parentId" parent-page-id))
    (cf-show-page (cf-rpc-save-page new-page))))

(defun confluence-create-page-with-url (&optional arg)
  "With ARG, prompts for the confluence url to use for the create page call
(based on `confluence-default-space-alist')."
  (interactive "P")
  (let ((confluence-switch-url arg)
        (confluence-input-url nil))
    (confluence-create-page)))

(defun confluence-get-related-page (&optional rel-type arg)
  "Gets a page related to the current page.  Prompts for type, one of
(ancestor, child, descendent, attachment, parent)."
  (interactive "i\nP")
  (if (not rel-type)
      (setq rel-type (intern
                      (cf-read-string-simple
                       (format "Confluence Relation Type [%s]: "
                               (if arg "ancestor" "child")) 
                       nil
                       '(("attachment" t) ("ancestor" t) ("child" t)
                         ("parent" t) ("descendent" t)) 
                       t nil
                       (if arg "ancestor" "child")))))
  (let ((space-name (cf-get-struct-value confluence-page-struct "space"))
        (page-name (cf-get-struct-value confluence-page-struct "title"))
        (page-id confluence-page-id)
        (rel-page-names nil))
    (if (and (cf-string-notempty space-name)
             (cf-string-notempty page-name)
             page-id)
        (cond
         ;; show page attachment
         ((eq rel-type 'attachment)
          (confluence-get-attachment page-name space-name nil page-id))
         ;; show page parent
         ((eq rel-type 'parent)
          (confluence-get-parent-page))
         (t
          (setq rel-page-names
                (with-quiet-rpc
                 (cf-result-to-completion-list
                  (cond
                   ;; retrieve available ancestors
                   ((eq rel-type 'ancestor)
                    (cf-rpc-get-page-ancestors page-id))
                   ;; retrieve available children
                   ((eq rel-type 'child)
                    (cf-rpc-get-page-children page-id))
                   ;; retrieve available descendents
                   ((eq rel-type 'descendent)
                    (cf-rpc-get-page-descendents page-id))
                   (t 
                    (error "Unknown relationship type %s" rel-type)))
                  "title")))
          (if (= (length rel-page-names) 0)
              (message "Current page has no relations of type %s"
                       rel-type)
            ;; prompt for actual related page to load
            (confluence-get-page
             (cf-read-string nil
                             "Confluence Page Name: "
                             'confluence-page-history 
                             (cons space-name (cf-get-url))
                             rel-page-names t)
             space-name)))))))

(defun confluence-browse-page ()
  "Runs `browse-url' with the url of the current confluence page."
  (interactive)
  (let ((url (cf-get-struct-value confluence-page-struct "url")))
    (if (cf-string-notempty url)
        (browse-url url))))

(defmacro cf-destructure-tags-stack-entry (entry &rest body)
  "Destructure a tags-stack tuple.  NB this is not a hygenic
macro, it intentionally binds named variables that match the
structure of the stack entry.  The structure and the variable
bindings are:

  ((page-type confluence-input-url page-id-or-query &optional 
    space-name  page-name file-name) old-point)

old-point is the point on the page which was pushed.  The 
preceding list of info is the laod-info described in 
`cf-destructure-load-info'.
"
  `(destructuring-bind
       ((page-type confluence-input-url page-id-or-query 
         &optional space-name  page-name file-name) 
        old-point)
       ,entry
     ,@body))

(defmacro cf-destructure-load-info (load-info &rest body)
  "Destructure a load-info tuple.  NB this is not a hygenic
macro, it intentionally binds named variables that match the
structure of the stack entry.  The structure and the variable
bindings are:

  (page-type confluence-input-url page-id-or-query &optional 
   space-name page-name file-name)

Each load-info can be either the result of a search query (in
which case page-type will be the symbol 'search, a page
visitation (and page-type will be 'page), or an attachment 
download (and page-type will be 'attachment). page-id-or-query 
will be either a page-id or a query - depending on 
the type of stack entry (page or query).  space-name will be 
populated when page-type is 'search or 'attachment.  page-name 
and file-name will be populated when page-type is 'attachment.
"
  `(destructuring-bind
       (page-type confluence-input-url page-id-or-query 
                  &optional space-name page-name file-name)
       ,load-info
     ,@body))

(defun confluence-pop-tag-stack ()
  "Returns to the last previously visited space/page by popping
the tags stack."
  (interactive)
  (if (null confluence-tag-stack)
      (message "Stack is empty...")
    (let ((confluence-no-push t))
      (cf-destructure-tags-stack-entry
       (pop confluence-tag-stack)
       (cond 
        ;; load a normal page by id
        ((eq page-type 'page)
         (cf-show-page (cf-rpc-get-page-by-id page-id-or-query)))
        ;; run a previous search query
        ((eq page-type 'search)
         (cf-show-search-results 
          (cf-rpc-search page-id-or-query space-name)
          load-info))
        ;; load an attachment
        ((eq page-type 'attachment)
         (cf-show-attachment page-name space-name file-name page-id-or-query nil))
        (t
         (error "Invalid stack info")))
       (goto-char old-point)))))

(defun confluence-push-tag-stack ()
  "Pushes the current page onto the visited stack if it is a confluence page."
  (interactive)
  (if (and (not confluence-no-push) confluence-load-info)
      (push (list confluence-load-info (point)) confluence-tag-stack)))

(defun confluence-ediff-merge-current-page ()
  "Starts an ediff session diffing the current confluence page against the
latest version of that page saved in confluence with intent of saving the
result as the latest version of the page."
  (interactive)
  (cf-ediff-current-page t))

(defun confluence-ediff-current-page ()
  "Starts an ediff session diffing the current confluence page against the
latest version of that page saved in confluence."
  (interactive)
  (cf-ediff-current-page nil))

(defun confluence-reparent-page ()
  "Changes the parent of the current confluence page."
  (interactive)
  (let ((parent-page-id (cf-get-parent-page-id nil)))
    (if (and parent-page-id
             (not (equal parent-page-id (cf-get-struct-value confluence-page-struct "parentId"))))
        (progn
          (cf-set-struct-value 'confluence-page-struct "parentId" parent-page-id)
          (set-buffer-modified-p t)))))

(defun confluence-rename-page ()
  "Changes the name (title) of the current confluence page."
  (interactive)
  (let ((page-name (cf-prompt-page-name 
                    (cf-get-struct-value confluence-page-struct "space") 
                    "New ")))
    (if (and (cf-string-notempty page-name)
             (not (equal page-name (cf-get-struct-value confluence-page-struct "title"))))
        (progn
          (cf-set-struct-value 'confluence-page-struct "title" page-name)
          (cf-update-buffer-name)
          (set-buffer-modified-p t)))))

(defun confluence-add-label (&optional label-name)
  "Adds the label with the given name to the current confluence page."
  (interactive)
  (if confluence-page-id
      (progn
        (if (not label-name)
            (setq label-name
                  (cf-read-string-simple "New Confluence Label: " 'confluence-label-history 'cf-complete-recent-label-name)))
        (if (cf-string-notempty label-name)
            (cf-rpc-add-label label-name confluence-page-id)))))

(defun confluence-remove-label (&optional label-name)
  "Removes the label with the given name to the current confluence page."
  (interactive)
  (if confluence-page-id
      (progn
        (if (not label-name)
          (let ((cur-labels (with-quiet-rpc
                             (cf-result-to-completion-list (cf-rpc-get-labels confluence-page-id) "name"))))
            (if (= (length cur-labels) 0)
                (message "Current page has no labels...")
              (progn
                (or label-name
                    (setq label-name (cf-read-string-simple "Old Confluence Label: " 'confluence-label-history cur-labels t)))))))
        (if (cf-string-notempty label-name)
            (cf-rpc-remove-label label-name confluence-page-id)))))

(defun confluence-get-labels ()
  "Shows the labels of the current page."
  (interactive)
  (if confluence-page-id
      (let ((cur-labels (mapcar
                         '(lambda (el)
                            (cf-get-struct-value el "name"))
                         (cf-rpc-get-labels confluence-page-id))))
        (if (= (length cur-labels) 0)
            (message "Current page has no labels...")
          (message "Current Confluence Labels: %s" cur-labels)))))
  
(defun confluence-delete-page (&optional arg)
  "Deletes the current confluence page.  Asks first, unless ARG is given."
  (interactive "P")
  (if (or arg
          (yes-or-no-p  "Really delete confluence page? "))
      (progn
        (if (not confluence-page-id)
            (error "Could not delete Confluence page %s, missing page id"
                   (buffer-name)))
        (cf-rpc-execute 'confluence1.removePage confluence-page-id)
        ;; remove this page from the tag stack
        (while (assoc confluence-load-info confluence-tag-stack)
          (setq confluence-tag-stack
                (remove (assoc confluence-load-info confluence-tag-stack)
                        confluence-tag-stack)))
        (kill-buffer (current-buffer)))))

;;;###autoload
(defun confluence-search (&optional query space-name)
  "Runs a confluence search for QUERY, optionally restricting the results to
the given SPACE-NAME."
  (interactive)
  (confluence-search-by-type 'content query space-name))

(defun confluence-search-in-space (&optional query)
  "Runs a confluence search for QUERY, restricting the results to the space of
the current buffer."
  (interactive)
  (confluence-search-by-type-in-space 'content query))

(defun confluence-search-with-url (&optional arg)
  "With ARG, prompts for the confluence url to use for the search call (based
on `confluence-default-space-alist')."
  (interactive "P")
  (confluence-search-by-type-with-url arg 'content))

(defun confluence-search-by-type (&optional query-type query space-name)
  "Runs a confluence search by type (content, title, label) for QUERY, optionally restricting the results to
the given SPACE-NAME."
  (interactive)
  (or query-type
      (setq query-type (cf-read-string-simple "Confluence Search Type [content]: "
                                        nil confluence-search-types
                                        t nil "content")))
  (if (stringp query-type)
      (setq query-type (intern query-type)))
  (let ((query-prompt-prefix "")
        (query-prefix ""))
    (cond
     ((eq query-type 'title)
      (setq query-prompt-prefix "Title ")
      (setq query-prefix "title: "))
     ((eq query-type 'label)
      (setq query-prompt-prefix "Label ")
      (setq query-prefix "labelText: ")))
    (or query
        (setq query (read-string (concat "Confluence " query-prompt-prefix "Query: ") nil 
                                 'confluence-search-history nil t)))
    (setq query (concat query-prefix query))
    (cf-show-search-results (cf-rpc-search query space-name)
                            (list 'search (cf-get-url) query space-name))))

(defun confluence-search-by-type-in-space (&optional query-type query)
  "Runs a confluence search by type (content, title, label) for QUERY, restricting the results to the space of
the current buffer."
  (interactive)
  (confluence-search-by-type query-type query (cf-get-struct-value confluence-page-struct "space")))

(defun confluence-search-by-type-with-url (&optional arg query-type)
  "With ARG, prompts for the confluence url to use for the search call (based
on `confluence-default-space-alist')."
  (interactive "P")
  (let ((confluence-input-url (and arg (cf-prompt-url nil))))
    (confluence-search-by-type query-type)))

(defun confluence-preview ()
  "Preview the content in the current confluence buffer."
  (interactive)
  (if (and confluence-page-id
           confluence-page-struct)
      (let ((source-content "")
            (rendered-content nil)
            (render-buf (get-buffer-create " *Confluence-preview*")))
        ;; if the local content is modified, submit the content
        (if (buffer-modified-p)
            (progn
              (setq source-content (buffer-string))
              ;; if there are save hooks, copy the content into a temp buf and run them on the content before
              ;; submitting it
              (if confluence-before-save-hook
                  (with-current-buffer (get-buffer-create " *Confluence-decode*")
                    (erase-buffer)
                    (insert source-content)
                    (run-hooks 'confluence-before-save-hook)
                    (setq source-content (buffer-string))))))
        ;; render the current page, optionally with locally modified content
        (setq rendered-content (cf-rpc-render-page (cf-get-struct-value confluence-page-struct "space")
                                                   confluence-page-id source-content))
        ;; shove the html into a temp buffer
        (with-current-buffer render-buf
          (widen)
          (erase-buffer)
          (fundamental-mode)
          (insert rendered-content)
          ;; fix bug in stylesheet
          (goto-char (point-min))
          (if (re-search-forward "^\\s-*body\\s-*{[^}]*}" nil t)
              (progn
                (goto-char (match-beginning 0))
                (if (re-search-forward "text-align:\\s-*\\(center\\)" (match-end 0) t)
                    (replace-match "left" t t nil 1))))
          (set-buffer-modified-p nil))
        ;; launch browser with rendered content
        (message "Launching browser with preview content...")
        (browse-url-of-buffer render-buf))))

(defun confluence-get-info ()
  "Gets information on confluence."
  (interactive)
  (message "Confluence Server Info: %s" (cf-get-server-info)))

(defun confluence-get-info-with-url (&optional arg)
  "With ARG, prompts for the confluence url to use for the get
info call (based on `confluence-default-space-alist')."
  (interactive "P")
  (let ((confluence-switch-url arg)
        (confluence-input-url nil))
    (confluence-get-info)))

(defun cf-rpc-execute (method-name &rest params)
  "Executes a confluence rpc call, managing the login token and logging in if
necessary."
  (apply 'cf-rpc-execute-async nil method-name params))

(defun cf-rpc-execute-async (async-callback method-name &rest params)
  "Executes a confluence rpc call, managing the login token and logging in if
necessary."
  (condition-case err
      (apply 'cf-rpc-execute-internal-async async-callback method-name (confluence-login) params)
    (error
     ;; if we get a fault with the given keywords, try the call again after a
     ;; re-login (we force re-login), otherwise, just rethrow the error
     (if (and xml-rpc-fault-string
              (string-match "\\<authenticated\\>\\|\\<expired\\>" xml-rpc-fault-string))
         (apply 'cf-rpc-execute-internal-async async-callback method-name (confluence-login t) params)
       (error (error-message-string err))))))

(defun cf-rpc-execute-internal (method-name &rest params)
  "Executes a raw confluence rpc call.  Handles all necessary encoding/decoding of strings."
  (apply 'cf-rpc-execute-internal-async nil method-name params))

(defun cf-rpc-execute-internal-async (async-callback method-name &rest params)
  "Executes a raw confluence rpc call.  Handles all necessary encoding/decoding of strings."
  (setq xml-rpc-fault-string nil)
  (setq xml-rpc-fault-code   nil)
  (let* ((url-http-version "1.0")  ;; this make the xml-rpc parser happy
         (url-http-attempt-keepalives nil)
         (page-url (cf-get-url))   ;; figure out which url to use
         (confluence-do-coding t))
    (if (not page-url)
        (error "No confluence url configured"))
    (condition-case err
        (let ((rpc-result 
               (if async-callback
                   (apply 'xml-rpc-method-call-async async-callback page-url method-name params)
               (cf-maybe-url-decode-entities-in-value (apply 'xml-rpc-method-call page-url method-name params)))
               ))
          ;; clear any url messages before returning
          (message nil)
          rpc-result)
      (error
       ;; decode the fault string and the error message (often includes the
       ;; fault string) and then rethrow the error
       (if xml-rpc-fault-string
           (setq xml-rpc-fault-string (cf-maybe-url-decode-entities-in-value 
                                       xml-rpc-fault-string)))
       (error (cf-maybe-url-decode-entities-in-value (error-message-string err)))))))

(defun cf-rpc-get-page-by-name (space-name page-name)
  "Executes a confluence 'getPage' rpc call with space and page names."
  (cf-rpc-execute 'confluence1.getPage space-name page-name))

(defun cf-rpc-get-page-by-id (page-id)
  "Executes a confluence 'getPage' rpc call with a page id."
  (cf-rpc-execute 'confluence1.getPage page-id))

(defun cf-rpc-search (query space-name &optional max-results)
  "Executes a confluence 'search' rpc call, optionally restricted by the given
SPACE-NAME."
  (let ((params (list (cons "type" "page"))))
    (if (cf-string-notempty space-name)
        (cf-set-struct-value 'params "spaceKey" space-name))
    (cf-rpc-execute 'confluence1.search query
                    params (or max-results confluence-search-max-results))))

(defun cf-rpc-save-page (page-struct &optional comment minor-edit)
  "Executes a confluence 'storePage' rpc call with a page struct (or
'updatePage' if comment or minorEdit flag are specified)."
  (if (or (cf-string-notempty comment) minor-edit)
      (let ((page-options (list (cons "versionComment" comment) 
                                (cons "minorEdit" minor-edit))))
        (cf-rpc-execute 'confluence1.updatePage page-struct page-options))
    (cf-rpc-execute 'confluence1.storePage page-struct)))

(defun cf-rpc-get-spaces ()
  "Executes a confluence 'getSpaces' rpc call."
  (cf-rpc-execute 'confluence1.getSpaces))

(defun cf-rpc-get-space (space-name)
  "Executes a confluence 'getSpace' rpc call with space name."
  (cf-rpc-execute 'confluence1.getSpace space-name))

(defun cf-rpc-get-labels (obj-id)
  "Executes a confluence 'getLabelsById' rpc call with object id."
  (cf-rpc-execute 'confluence1.getLabelsById obj-id))

(defun cf-rpc-get-recent-labels (max-results)
  "Executes a confluence 'getRecentlyUsedLabels' rpc call with the given max results."
  (cf-rpc-execute 'confluence1.getRecentlyUsedLabels max-results))

(defun cf-rpc-add-label (label-name obj-id)
  "Executes a confluence 'addLabelByName' rpc call with label name and object id."
  (cf-rpc-execute 'confluence1.addLabelByName label-name obj-id))

(defun cf-rpc-remove-label (label-name obj-id)
  "Executes a confluence 'removeLabelByName' rpc call with label name and object id."
  (cf-rpc-execute 'confluence1.removeLabelByName label-name obj-id))

(defun cf-rpc-render-page (space-name page-id &optional content)
  "Executes a confluence 'renderContent' rpc call with space and page id and optional content."
  (cf-rpc-execute 'confluence1.renderContent space-name page-id (or content "")))

(defun cf-rpc-get-attachments (page-id)
  "Executes a confluence 'getAttachments' rpc call with page id."
  (cf-rpc-execute 'confluence1.getAttachments page-id))

(defun cf-rpc-get-attachment (page-id file-name &optional version)
  "Executes a confluence 'getAttachment' rpc call with page id, file name and
optional version number."
  ;; "0" gets the latest version
  (cf-rpc-execute 'confluence1.getAttachment page-id file-name 
                  (or version "0")))

(defun cf-rpc-get-page-children (page-id)
  "Executes a confluence 'getChildren' rpc call with page id."
  (cf-rpc-execute 'confluence1.getChildren page-id))

(defun cf-rpc-get-page-ancestors (page-id)
  "Executes a confluence 'getAncestors' rpc call with page id."
  (cf-rpc-execute 'confluence1.getAncestors page-id))

(defun cf-rpc-get-page-descendents (page-id)
  "Executes a confluence 'getDescendents' rpc call with page id."
  (cf-rpc-execute 'confluence1.getDescendents page-id))

(defun cf-rpc-get-server-info ()
  "Executes a confluence 'getServerInfo' rpc call."
  (cf-rpc-execute 'confluence1.getServerInfo))

(defun cf-ediff-current-page (update-cur-version)
  "Starts an ediff session for the current confluence page, optionally
updating the saved metadata to the latest version."
  (if (not confluence-page-id)
      (error "Could not diff Confluence page %s, missing page id"
             (buffer-name)))
  (let ((rev-buf)
        (cur-buf (current-buffer))
        (rev-page (cf-rpc-get-page-by-id confluence-page-id)))
    (setq rev-buf
          (get-buffer-create (format "%s.~%s~" (buffer-name cur-buf) (cf-get-struct-value rev-page "version" 0))))
    ;; create read-only temp buffer w/ the latest page data
    (with-current-buffer rev-buf
      (cf-insert-page rev-page)
      (toggle-read-only 1))
    ;; optionally update the metadata in the current buffer (and update the
    ;; buffer name in case the page title changed)
    (if update-cur-version
        (progn
          (setq confluence-page-struct 
                (cf-set-struct-value-copy rev-page "content" ""))
          (cf-update-buffer-name)))
    (ediff-buffers cur-buf rev-buf nil 'confluence-diff)))

(defun cf-save-page ()
  "Saves the current confluence page and updates the buffer with the latest
page."
  (if (not confluence-page-id)
      (error "Could not save Confluence page %s, missing page id"
             (buffer-name)))
  (let* ((minor-edit nil)
         (comment nil))
    (if (cf-is-version-at-least 2 10)
        (progn
          ;; only ask for these values if the server API supports sending them
          (setq minor-edit (cf-save-is-minor-edit))
          (setq comment (cf-save-get-comment minor-edit))))
    (widen)
    (run-hooks 'confluence-before-save-hook)
    (cf-insert-page (cf-rpc-save-page 
                     (cf-set-struct-value-copy confluence-page-struct 
                                               "content" (buffer-string))
                     comment minor-edit) 
                    nil nil t))
  t)

(defun cf-save-is-minor-edit ()
  (and confluence-save-page-minor-edits
       (or (not (eq confluence-save-page-minor-edits 'ask))
           (not (y-or-n-p "Major edit? ")))))

(defun cf-save-get-comment (minor-edit)
  (if (and confluence-save-page-comments
           (or (not (eq confluence-save-page-comments 'major))
               (not minor-edit)))
      (read-string "Modification comment: " nil nil nil t)
    nil))

(defun cf-revert-page (&optional arg noconfirm)
  "Reverts the current buffer to the latest version of the current confluence
page."
  (if (and confluence-load-info
           (or noconfirm
               (yes-or-no-p "Revert confluence page? ")))
      (let ((confluence-no-push t)
            (inhibit-read-only t))
        ;; use the load-info to reload the page, so we can reload normal pages
        ;; and search pages
        (cf-destructure-load-info confluence-load-info
          (cond 
           ;; reload normal page data
           ((eq page-type 'page)
            (cf-insert-page (cf-rpc-get-page-by-id page-id-or-query) confluence-load-info)
            (cf-update-buffer-name))
           ;; reload search page data
           ((eq page-type 'search)
            (cf-insert-search-results 
             (cf-rpc-search page-id-or-query space-name)
             confluence-load-info))
           ;; reload attachment data
           ((eq page-type 'attachment)
            (if (or (not (file-exists-p buffer-file-name))
                    (equal "d"
                           (cf-read-char "Revert attachment from Confluence (d)ownload or local (f)ile [d]: " 
                            "[df]" "d")))
                (cf-insert-attachment page-name space-name file-name 
                                      page-id-or-query (current-buffer) nil
                                      confluence-load-info)
              (let ((revert-buffer-function nil))
                (revert-buffer arg t))))
           (t
            (error "Invalid load info")))))))

(defun cf-show-page (full-page &optional anchor-name)
  "Does the work of finding or creating a buffer for the given confluence page
and loading the data if necessary."
  (confluence-push-tag-stack)
  ;; note, we save the current url as confluence-input-url in case the buffer
  ;; has a different value locally from a previous search (this value will
  ;; override it)
  (let* ((confluence-input-url (cf-get-url))
         (load-info (list 'page confluence-input-url (cf-get-struct-value full-page "id")))
         (page-buffer (get-buffer-create (cf-format-buffer-name
                                          (cf-get-struct-value full-page "title")
                                          (cf-get-struct-value full-page "space")))))
    ;; only insert the data if the buffer is new, otherwise just show current
    ;; data
    (with-current-buffer page-buffer
      (if (not (equal confluence-load-info load-info))
          (progn
            (cf-insert-page full-page load-info)
            (goto-char (point-min))))
      (if anchor-name
          (confluence-goto-anchor anchor-name)))
    (switch-to-buffer page-buffer)))

(defun cf-insert-page (full-page &optional load-info browse-function keep-undo page-mode)
  "Does the work of loading confluence page data into the current buffer.  If
KEEP-UNDO, the current undo state will not be erased.  The LOAD-INFO is the 
information necessary to reload the page (if nil, normal page info is used)."
  ;; if this is an old buffer (already has confluence-mode), run
  ;; revert hooks before writing new data
  (if (not page-mode)
      (setq page-mode 'confluence-mode))
  (if (eq major-mode page-mode)
      (run-hooks 'confluence-before-revert-hook))
  (let ((old-point (point))
        (was-read-only buffer-read-only))
    (if was-read-only
        (toggle-read-only))
    ;; save/update various page metadata
    (setq confluence-page-struct full-page)
    (setq confluence-page-url (cf-get-url))
    (setq confluence-page-id (cf-get-struct-value confluence-page-struct "id"))
    (setq confluence-load-info 
          (or load-info
              (list 'page confluence-page-url confluence-page-id)))
    (if browse-function
        (setq confluence-browse-function browse-function))
    ;; don't save the buffer edits on the undo list (we might keep it)
    (let ((buffer-undo-list t)
          (inhibit-read-only t))
      (widen)
      (erase-buffer)
      ;; actually insert the new page contents
      (insert (cf-get-struct-value confluence-page-struct "content" ""))
      (goto-char old-point))
    ;; remove the contents from the page metadata
    (cf-set-struct-value 'confluence-page-struct "content" "")
    ;; restore/setup buffer state
    (set-buffer-modified-p nil)
    (or keep-undo
        (eq buffer-undo-list t)
        (setq buffer-undo-list nil))
    (funcall page-mode)
    (if was-read-only
        (toggle-read-only 1))))

(defun cf-show-search-results (search-results load-info)
  "Does the work of finding or creating a buffer for the given confluence
search results and loading the data into that page."
  (confluence-push-tag-stack)
  ;; note, we save the current url as confluence-input-url in case the buffer
  ;; has a different value locally from a previous searcg (this value will
  ;; override it)
  (let ((confluence-input-url (cf-get-url))
        (search-buffer (get-buffer-create "*Confluence Search Results*")))
    (with-current-buffer search-buffer
      ;; only reload the page if this is a new search, otherwise keep current
      ;; data
      (if (not (equal confluence-load-info load-info))
          (progn
            (cf-insert-search-results search-results load-info)
            (goto-char (point-min))
            (toggle-read-only 1))))  ;; always make search results read-only
    (switch-to-buffer search-buffer)))

(defun cf-insert-search-results (search-results load-info)
  "Does the work of loading confluence search data into the current buffer."
  (let ((search-page (list (cons "title" "Confluence Search Results"))))
    ;; turn the search results into a wiki-like page
    (with-temp-buffer
      (insert "h1. Confluence Search Results for '" (nth 2 load-info) "'\n\n")
      (dolist (search-result search-results)
        (insert (format "[%s|%s]\n"
                        (cf-get-struct-value search-result "title")
                        (cf-get-struct-value search-result "id")))
        (let ((excerpt (cf-get-struct-value search-result "excerpt")))
          (if (cf-string-notempty excerpt)
              (insert excerpt "\n")))
        (insert "\n"))
      (cf-set-struct-value 'search-page "content" (buffer-string)))
    ;; install a special browse-function for loading the search urls (which
    ;; use page ids)
    (cf-insert-page search-page load-info 'cf-search-browse-function nil 'confluence-search-mode)))

(defun cf-search-browse-function (url)
  "Browse function used in search buffers (the links are page ids)."
  (cf-show-page (cf-rpc-get-page-by-id url)))

(defun cf-simple-browse-function (url)
  "Simple browse function used in page buffers."
  (let ((space-name (cf-get-struct-value confluence-page-struct "space"))
        (page-name url)
        (anchor-name nil)
        (attachment-name nil)
        (explicit-space nil)
        (page-id nil))
    ;; split "space:page" links
    (if (string-match "^\\([^:\n]*\\)[:]\\(.*\\)$" page-name)
        (progn
          (setq explicit-space t)
          (setq space-name (match-string 1 page-name))
          (setq page-name (match-string 2 page-name))))
    ;; strip off any trailing "|link tip"
    (if (string-match "^\\([^|\n]*\\)[|]\\(.*\\)$" page-name)
        (setq page-name (match-string 1 page-name)))
    ;; get '^' (attachment) or '#' (anchor)
    (if (string-match "^\\(.*?\\)\\([#^]\\)\\(.*\\)$" page-name)
        (progn
          (if (equal (match-string 2 page-name) "^")
              (setq attachment-name (match-string 3 page-name))
            (setq anchor-name (match-string 3 page-name)))
          (setq page-name (match-string 1 page-name))))
    (cond
     ;; open an attachment
     ((cf-string-notempty attachment-name)
      (if (cf-string-empty page-name)
          (progn
            (setq page-name (cf-get-struct-value 
                             confluence-page-struct "title"))
            (setq page-id confluence-page-id)))
      (confluence-get-attachment page-name space-name attachment-name page-id))
     ;; goto anchor in this page
     ((and (cf-string-notempty anchor-name)
           (cf-string-empty page-name))
      (confluence-goto-anchor anchor-name))
     ;; goto space "home" page
     ((and explicit-space
           (cf-string-notempty space-name)
           (cf-string-empty page-name))
      (cf-show-page
       (cf-rpc-get-page-by-id (cf-get-struct-value 
                               (cf-rpc-get-space space-name) "homePage"))))
     ;; goto user profile page (load like space "home" page)
     ((and (not explicit-space)
           (string-match "^[~].+$" page-name))
      (cf-show-page
       (cf-rpc-get-page-by-id (cf-get-struct-value 
                               (cf-rpc-get-space page-name) "homePage"))))
     (t
      (confluence-get-page page-name space-name anchor-name)))))

(defun cf-get-parent-page-id (try-current-page &optional space-name)
  "Gets a confluence parent page id, optionally using the one in the current
buffer."
  ;; if current page is a confluence page and try-current-page, ask if use
  ;; wants to use it as the parent page
  (if (and try-current-page
           confluence-page-id
           (yes-or-no-p "Use current confluence page for parent? "))
      confluence-page-id
    ;; otherwise, prompt for parent page
    (let ((parent-space-name (or space-name (cf-get-struct-value confluence-page-struct "space")))
          (parent-page-name nil))
      (cf-prompt-page-info "Parent " 'parent-page-name 'parent-space-name)
      (if (and (cf-string-notempty parent-space-name)
               (cf-string-notempty parent-page-name))
          (cf-get-struct-value (cf-rpc-get-page-by-name parent-space-name parent-page-name) "id")
        nil))))

(defun cf-show-attachment (page-name space-name file-name page-id 
                           save-only-file-name)
  "Does the work of finding or creating a buffer for the given confluence
attachment and loading the data if necessary."
  (confluence-push-tag-stack)
  ;; note, we save the current url as confluence-input-url in case the buffer
  ;; has a different value locally
  (let* ((confluence-input-url (cf-get-url))
         (load-info (list 'attachment confluence-input-url page-id
                          space-name page-name file-name))
         (result-buffer (get-buffer-create 
                         (cf-format-attachment-buffer-name 
                          file-name page-name space-name))))
    ;; only insert the data if the buffer is new, otherwise just show current
    ;; data
    (unwind-protect
        (if (or save-only-file-name
                (not (equal
                      (with-current-buffer result-buffer
                        confluence-load-info)
                      load-info)))
            (cf-insert-attachment page-name space-name file-name
                                  page-id result-buffer save-only-file-name
                                  load-info))
      ;; on save only, kill temp buf
      (if save-only-file-name
          (kill-buffer result-buffer)))
    ;; finish up
    (if save-only-file-name
        (message "File successfully downloaded to %s" save-only-file-name)
      (switch-to-buffer result-buffer))))

(defun cf-insert-attachment (page-name space-name file-name page-id 
                             result-buffer save-only-file-name load-info)
  "Downloads and inserts the attachment with the given info into the given
RESULT-BUFFER for viewing.  If the image is a supported image type and
`confluence-show-attachment-images' is enabled, the data will be viewed as an
image.  If SAVE-ONLY-FILE-NAME is non-nil, the attachment will instead be
saved to this file name and not viewed."
  ;; we use lexical-let so the lambda form below can easily interact with the
  ;; variables defined here
  (lexical-let ((retrieval-done nil)
		(asynch-buffer nil)
                (download-error nil)
                (attachment-struct nil))

    ;; grab attachment struct
    (setq attachment-struct (with-quiet-rpc (cf-rpc-get-attachment page-id file-name)))
    
    ;; prep result buffer
    (with-current-buffer result-buffer
      (widen)
      (erase-buffer)
      (fundamental-mode)
      ;; save load-info so we can revert the buffer using our custom
      ;; revert-buffer-function and push/pop
      (setq confluence-load-info load-info)
      ;; set page-struct w/ url only, so confluence-browse-page will work
      (setq confluence-page-struct (list (cons "url" (cf-get-struct-value attachment-struct "url"))))
      (make-local-variable 'revert-buffer-function)
      (setq revert-buffer-function 'cf-revert-page)
      (if (not buffer-file-name)
          (setq buffer-file-name 
                (or save-only-file-name
                    (cf-create-temp-attachment-file file-name)))))

    ;; start async attachment download
    (setq asynch-buffer
          (cf-rpc-execute-async 
           (lambda ()
             (unwind-protect
                 (condition-case err
                     (cf-attachment-download-callback result-buffer)
                   (error
                    (setq download-error (error-message-string err))))
               (setq retrieval-done t
                     asynch-buffer (current-buffer))))
           'confluence1.getAttachmentData 
           page-id file-name "0")) ;; "0" gets the latest version

    ;; wait for download to finish (this logic ripped from
    ;; url-retrieve-synchronously)
    (let ((proc (and asynch-buffer (get-buffer-process asynch-buffer))))
      (if (null proc)
	  nil
	(while (not retrieval-done)
	  (if (memq (process-status proc) '(closed exit signal failed))
              (setq retrieval-done t)
            (unless (accept-process-output proc)
              (setq proc (get-buffer-process asynch-buffer)))))))

    ;; just bailout if the download failed
    (if download-error
        (error download-error))

    (with-current-buffer result-buffer
      (if save-only-file-name
          ;; if we are not viewing the file, just save the result buffer
          (let ((save-buffer-coding-system 'no-conversion)
                (buffer-file-coding-system 'no-conversion)
                (coding-system-for-write 'no-conversion)
                (file-coding-system-alist nil))
            (write-region (point-min) (point-max) buffer-file-name nil 'quiet))
        ;; otherwise, prep the buffer for viewing
        (if (or (not confluence-show-attachment-images)
                (not (cf-insert-image file-name)))
          (set-auto-mode))
        (set-buffer-modified-p nil)
        (goto-char (point-min))))))

(defun cf-insert-image (attachment-file-name)
  "Determines if the attachment data in the current buffer with
ATTACHMENT-FILE-NAME is supported image data and, if so, displays the image
data.  Returns t if the data was successfully displayed as an image, nil
otherwise."
  (let ((buf-is-multibyte enable-multibyte-characters))
    (if (not
         (catch 'inserted-image
           
           ;; convert bmps to tifs (emacs does not seem to handle bmps)
           (if (let ((case-fold-search t))
                 (string-match "\\.bmp\\'" attachment-file-name))
               (progn
                 (cf-bmp-to-tif)
                 (setq attachment-file-name (concat attachment-file-name ".tif"))))
           
           ;; don't even bother if the file name does not match supported
           ;; image types
           (if (not (string-match (image-file-name-regexp) 
                                  attachment-file-name))
               (throw 'inserted-image nil))
           ;; switch buffer to "binary" mode and grab image data
           (set-buffer-multibyte nil)
           (let ((img-data (string-make-unibyte
                            (buffer-substring-no-properties 
                             (point-min) (point-max))))
                 (img-type nil)
                 (image nil))
             ;; attempt to determine image type
             (setq img-type (image-type-from-data img-data))
             (if (not img-type)
                 (progn
                   (setq img-type (file-name-extension attachment-file-name))
                   (if (cf-string-notempty img-type)
                       (setq img-type (intern (downcase img-type)))
                     (setq img-type nil))))
             (if (not img-type)
                 (throw 'inserted-image nil))
             ;; attempt to create image data
             (setq image (create-image img-data img-type t))
             (if (not image)
                 (throw 'inserted-image nil))
             ;; insert the image data, this logic borrowed from
             ;; insert-image-file
             (add-text-properties 
              (point-min) (point-max)
              `(display ,image
                        intangible ,image
                        rear-nonsticky (display intangible)
                        read-only t
                        front-sticky (read-only)))
             ;; indicate the buffer contents are "binary"
             (setq buffer-file-coding-system 'no-conversion)
             (make-local-variable 'find-file-literally)
             (setq find-file-literally t)
             (buffer-disable-undo))
           t))
        (progn
          ;; restore previous buffer state
          (set-buffer-multibyte buf-is-multibyte)
          (message "Unsupported image type %s" attachment-file-name)
          nil)
      t)))

(defun cf-attachment-download-callback (result-buffer)
  "Handles an attachment xml-rpc download result buffer.  Copies the
attachment data to the given RESULT-BUFFER (base64 decoding or entity decoding
if necessary)."
  (url-mark-buffer-as-dead (current-buffer))
  (if (not (numberp url-http-response-status))
      (error "Why? url-http-response-status is %s"
             url-http-response-status))
  (if (> url-http-response-status 299)
      (error "Error during request: %s"
             url-http-response-status))
  (goto-char (point-min))
  (let ((value-start nil)
        (value-end nil)
        (base64-encoded nil)
        (case-fold-search t))
    (if (re-search-forward "<value>\\(<base64>\\)?" nil t)
        (progn
          (if (match-string 1)
              (setq base64-encoded t))
          (setq value-start (match-end 0)))
      (error "Could not find (start) attachment data"))
    (if (re-search-forward "\\(</base64>\\)</value>" nil t)
        (setq value-end (match-beginning 0))
      (error "Could not find (end) attachment data"))
    (copy-to-buffer result-buffer value-start value-end)
    (with-current-buffer result-buffer
      (if base64-encoded
          ;; if result was base64 encoded, just decode that
          (let ((save-buffer-coding-system 'no-conversion)
                (buffer-file-coding-system 'no-conversion)
                (coding-system-for-write 'no-conversion)
                (coding-system-for-read 'no-conversion)
                (file-coding-system-alist nil)
                (buf-is-multibyte enable-multibyte-characters))
            (if buf-is-multibyte
                (set-buffer-multibyte nil))
            (base64-decode-region (point-min) (point-max))
            (if buf-is-multibyte
                (set-buffer-multibyte t)))
        ;; otherwise, we need to do entity decoding
        (let ((confluence-do-coding t))
          (cf-url-decode-entities-in-buffer result-buffer)))
      (set-buffer-modified-p nil))))

(defun cf-bmp-to-tif ()
  "Converts a bmp to a tif in the current buffer."
  (let ((tmp-src-file (make-temp-file "bmp"))
        (tmp-dst-file (make-temp-file "tif")))

    ;; save bmp data to temp file
    (let ((save-buffer-coding-system 'no-conversion)
          (buffer-file-coding-system 'no-conversion)
          (coding-system-for-write 'no-conversion)
          (file-coding-system-alist nil))
      (write-region (point-min) (point-max) tmp-src-file nil 'quiet))

    ;; convert bmp to tiff
    (if (/= (call-process "bmp2tiff" nil nil nil tmp-src-file tmp-dst-file) 0)
        (progn
          (message "Failed executing bmp2tiff")
          (throw 'inserted-image nil)))

    ;; replace bmp data w/ tif data
    (insert-file-contents-literally tmp-dst-file nil 0 (nth 7 (file-attributes tmp-dst-file)) t)

    ;; ditch tmp files
    (delete-file tmp-src-file)
    (delete-file tmp-dst-file)))

(defun cf-format-attachment-buffer-name (file-name page-name space-name)
  "Creates a buffer name for an attachment with the given info."
  (if (and (cf-string-notempty page-name)
           (cf-string-notempty space-name))
      (format "%s<%s/%s>" file-name space-name page-name)
    file-name))

(defun cf-create-temp-attachment-file (file-name)
  "Creates a temporary file name for an attachment with the given info with
the pattern '<temp-dir>/<file-prefix>-<temp-id>.<file-ext>'."
  (save-match-data
  (let ((prefix file-name)
        (suffix ""))
    (if (string-match "^\\([^.]+\\)\\([.].*\\)$" file-name)
        (progn
          (setq prefix (match-string 1 file-name))
          (setq suffix (match-string 2 file-name))))
    (concat (make-temp-name
             (expand-file-name (concat prefix "-") temporary-file-directory))
            suffix))))

(defun cf-get-server-info ()
  "Gets the (possibly cached) server info."
  (let ((server-info (cf-get-struct-value confluence-server-info-alist (cf-get-url))))
    (if (not server-info)
        (progn
          (setq server-info (cf-rpc-get-server-info))
          (cf-set-struct-value 'confluence-server-info-alist (cf-get-url) server-info)))
    server-info))

(defun cf-is-version-at-least (major-version minor-version)
  "Return t if the server version is at least the given version, nil otherwise."
  (let* ((server-info (cf-get-server-info))
         (cur-major-version (string-to-number (cf-get-struct-value server-info "majorVersion" "0")))
         (cur-minor-version (string-to-number (cf-get-struct-value server-info "minorVersion" "0"))))
    (or (> cur-major-version major-version)
        (and (= cur-major-version major-version)
             (>= cur-minor-version minor-version)))))

(defun cf-prompt-page-info (prompt-prefix page-name-var space-name-var &optional def-page-name)
  "Prompts for page info using the appropriate input function and sets the given vars appropriately."
  (let ((result-list
         (funcall confluence-prompt-page-function prompt-prefix
                  (symbol-value page-name-var) (symbol-value space-name-var) def-page-name)))
    (set page-name-var (nth 0 result-list))
    (set space-name-var (nth 1 result-list))))

(defun cf-prompt-page-by-component (prompt-prefix page-name space-name def-page-name)
  "Builds a list of (page-name space-name <url>) by prompting the user for each.  Suitable for use with
`confluence-prompt-page-function'."
  (let ((result-list nil))
    ;; prompt for url if confluence-switch-url is specified
    (if (and confluence-switch-url (not confluence-input-url))
        (setq confluence-input-url (cf-prompt-url prompt-prefix)))
    ;; now, prompt for space and page if not already defined by caller
    (if (not space-name)
        (setq space-name (cf-prompt-space-name prompt-prefix)))
    (push space-name result-list)
    (push (or page-name
              (cf-prompt-page-name space-name prompt-prefix def-page-name)) result-list)
    result-list))

(defun cf-prompt-page-by-path (prompt-prefix page-name space-name def-page-name)
  "Builds a list of (page-name space-name <url>) by prompting the user for each (where page and space name are
specified as one path).  Suitable for use with `confluence-prompt-page-function'."
  (let ((result-list nil)
        (page-path nil))
    ;; prompt for url if confluence-switch-url is specified
    (if (and confluence-switch-url (not confluence-input-url))
        (setq confluence-input-url (cf-prompt-url prompt-prefix)))
    ;; now, prompt for space/page if both are not already defined by caller
    (if (and page-name space-name)
        (setq result-list (cons page-name (cons space-name result-list)))
      (progn
        (setq page-path (cf-prompt-path prompt-prefix page-name space-name def-page-name))
        ;; split path into space and page
        (push (cf-get-space-name-from-path page-path) result-list)
        (push (cf-get-page-name-from-path page-path) result-list)))
    result-list))

(defun cf-prompt-url (&optional prompt-prefix)
  "Prompts for a confluence url."
  (let ((temp-url-hist (and confluence-default-space-alist
                            (mapcar 'car confluence-default-space-alist))))
    (read-string (concat (or prompt-prefix "") "Confluence Url: ") nil 'temp-url-hist (cf-get-url) t)))

(defun cf-prompt-space-name (&optional prompt-prefix)
  "Prompts for a confluence space name."
  (let* ((def-space-name (cf-get-default-space))
         (init-space-name (cf-get-struct-value confluence-page-struct "space"))
         (space-prompt (if def-space-name
                           (format "Confluence Space [%s]: " def-space-name)
                         "Confluence Space: ")))
    (cf-read-string prompt-prefix space-prompt 'confluence-space-history
                    (cf-get-url)
                    'cf-complete-space-name t
                    (if (not (equal init-space-name def-space-name))
                        init-space-name
                      nil)
                    def-space-name)))

(defun cf-prompt-page-name (space-name &optional prompt-prefix def-page-name)
  "Prompts for a confluence page name."
  (let ((page-prompt (if def-page-name
                         (format "Confluence Page Name [%s]: " def-page-name)
                       "Confluence Page Name: ")))
    (cf-read-string prompt-prefix page-prompt
                    'confluence-page-history (cons space-name (cf-get-url))
                    'cf-complete-page-name nil nil def-page-name)))

(defun cf-prompt-path (prompt-prefix page-name space-name def-page-name)
  "Prompts for a confluence page path."
  (cf-read-string prompt-prefix "Confluence Space/PageName: "
                  'confluence-path-history (cf-get-url)
                  'cf-complete-page-path nil
                  (if space-name
                      (concat space-name "/" (or def-page-name ""))
                    nil)))

(defun cf-read-string (prompt-prefix prompt hist-alist-var hist-key 
                       comp-func-or-table &optional
                       require-match init-val def-val)
  "Prompt for a string using the given prompt info and history alist."
  ;; we actually use the history var as an alist of history vars so we can
  ;; have different histories in different contexts (e.g. separate space
  ;; histories for each url and separate page histories for each space)
  (let ((hist-list (cf-get-struct-value (symbol-value hist-alist-var) 
                                        hist-key))
        (result-string nil))
    (setq result-string
          (cf-read-string-simple (concat (or prompt-prefix "") prompt)
                                 'hist-list comp-func-or-table
                                 require-match init-val def-val))
    ;; put the new history list back into the alist
    (cf-set-struct-value hist-alist-var hist-key hist-list)
    result-string))

(defun cf-read-string-simple (prompt hist-list-var comp-func-or-table
                              &optional require-match init-val def-val)
  "Prompt for a string using the given prompt info and history list."
  (let ((current-completions nil)
        (current-other-completions nil)
        (last-comp-str nil)
        (completion-buffer (or (and (boundp 'completion-buffer)
                                    completion-buffer)
                               (current-buffer)))
        (confluence-completing-read t))
    (with-quiet-rpc
     ;; prefer ido-completing-read if available
     (if (and (fboundp 'ido-completing-read)
              (listp comp-func-or-table))
         (ido-completing-read prompt (mapcar 'car comp-func-or-table) nil require-match init-val hist-list-var def-val)
       (completing-read prompt comp-func-or-table
                        nil require-match init-val hist-list-var def-val t)))))

(defun cf-read-char (prompt allowed-chars-regex &optional def-char)
  "Prompt for a character using the given PROMPT and ALLOWED-CHARS-REGEX.
If DEF-CHAR is given it will be returned if user hits the <enter> key."
  (let ((the-char nil))
    (while (not the-char)
      (setq the-char (char-to-string (read-char-exclusive prompt)))
      (if (not (string-match allowed-chars-regex the-char))
          (if (and def-char (string-equal (char-to-string ?\r) the-char))
              (setq the-char def-char)
            (setq the-char nil))))
    the-char))
  
(defun cf-minibuffer-setup ()
  "Minibuffer setup hook which changes some keybindings for confluence completion."
  (if confluence-completing-read
      ;; don't do completion when spaces are entered (just confusing)
      (local-set-key " " 'self-insert-command)))

(add-hook 'minibuffer-setup-hook 'cf-minibuffer-setup t)

(defun cf-get-space-name-from-path (page-path)
  "Parses the space name from the given PAGE-PATH."
  (if (string-match "\\([^/]+\\)[/]\\(.*\\)" page-path)
      (match-string 1 page-path)
    (cf-get-default-space)))

(defun cf-get-page-name-from-path (page-path)
  "Parses the page name from the given PAGE-PATH."
  (if (string-match "\\([^/]+\\)[/]\\(.*\\)" page-path)
      (match-string 2 page-path)
    page-path))

(defun cf-get-struct-value (struct key &optional default-value)
  "Gets a STRUCT value for the given KEY from the given struct, returning the
given DEFAULT-VALUE if not found."
  (or (and struct
           (cdr (assoc key struct)))
      default-value))

(defun cf-set-struct-value-copy (struct key value)
  "Copies the given STRUCT, sets the given KEY to the given VALUE and returns
the new STRUCT."
  (let ((temp-struct (copy-alist struct)))
    (cf-set-struct-value 'temp-struct key value)
    temp-struct))

(defun cf-set-struct-value (struct-var key value)
  "Sets (or adds) the given KEY to the given VALUE in the struct named by the
given STRUCT-VAR."
  (let ((cur-assoc (assoc key (symbol-value struct-var))))
    (if cur-assoc
        (setcdr cur-assoc value)
      (add-to-list struct-var (cons key value) t))))

(defun cf-result-to-completion-list (result-list key)
  "Translates the rpc result list into a list suitable for completion."
  (mapcar
   '(lambda (el)
      (cons (cf-get-struct-value el key) t))
   result-list))

(defun cf-get-page-anchors ()
  "Gets the anchors in the current page."
  (let ((anchors nil))
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward "{anchor:\\([^{}\n]+\\)}" nil t)
        (push (cons (match-string 1) t) anchors))
      ;; headings are also implicit anchors
      (goto-char (point-min))
      (while (re-search-forward "^h[1-9][.]\\s-+\\(.+?\\)\\s-*$" nil t)
        (push (cons (match-string 1) t) anchors)))
    anchors))

(defun cf-complete-space-name (comp-str pred comp-flag)
  "Completion function for confluence spaces."
  (if (not current-other-completions)
      (with-current-buffer completion-buffer
        (setq current-other-completions (cf-result-to-completion-list (cf-rpc-get-spaces) "key"))))
  (cf-complete comp-str pred comp-flag current-other-completions))

(defun cf-complete-page-name (comp-str pred comp-flag)
  "Completion function for confluence pages."

  ;; clear previous completion info if beginning of current string does not match previous string
  (let ((tmp-comp-str (replace-regexp-in-string "^\\(\\s-\\|\\W\\)*\\(.*?\\)\\(\\s-\\|\\W\\)*$"
                                                "\\2" comp-str t))
        (old-current-completions nil))
    (if (and last-comp-str
             (not (eq t (compare-strings last-comp-str 0 (length last-comp-str)
                                         tmp-comp-str 0 (length last-comp-str) t))))
        (progn
          (setq last-comp-str nil)
          (setq current-completions nil))
      ;; if the new string is over the repeat search threshold, clear previous search results
      (if (and last-comp-str
               (<= (+ (length last-comp-str) confluence-min-page-repeat-completion-length)
                   (length tmp-comp-str)))
          (progn
            (setq old-current-completions current-completions)
            (setq current-completions nil))))
    
  ;; retrieve page completions if necessary
  (if (and (>= confluence-min-page-completion-length 0)
           (not current-completions)
           (>= (length tmp-comp-str) confluence-min-page-completion-length))
      (let ((title-query
             (replace-regexp-in-string "\\(\\W\\)" "\\\\\\&" tmp-comp-str t)))
        ;; the search syntax is a little flaky, sometimes quotes are good, sometimes not...
        (setq title-query
              (concat "title: "
                      (if (string-match "\\s-" title-query)
                          (concat title-query "*")
                        (concat "\"" title-query "*\""))))
        (setq last-comp-str tmp-comp-str)
        (with-current-buffer completion-buffer
          (setq current-completions (cf-result-to-completion-list
                                     (cf-rpc-search title-query space-name confluence-max-completion-results)
                                     "title")))
        ;; the query results are flaky, if we had results before and none now, reuse the old list
        (if (and (= (length current-completions) 0)
                 old-current-completions)
            (setq current-completions old-current-completions))
        )))
  
  (cf-complete comp-str pred comp-flag current-completions))

(defun cf-complete-page-path (comp-str pred comp-flag)
  "Completion function for confluence page paths."
  (let ((space-name comp-str)
        (page-name nil))
    (if (string-match "\\([^/]+\\)[/]\\(.*\\)" comp-str)
        (progn
          (setq space-name (match-string 1 comp-str))
          (setq page-name (match-string 2 comp-str))))
    (if (not page-name)
        (cf-complete-space-name comp-str pred comp-flag)
      (let ((page-comp-result (cf-complete-page-name page-name pred comp-flag)))
        (cond
         ((stringp page-comp-result)
          (concat space-name "/" page-comp-result))
         ((listp page-comp-result)
          (mapcar
           '(lambda (el)
              (concat space-name "/" el)) page-comp-result))
         (t page-comp-result))))))

(defun cf-complete-recent-label-name (comp-str pred comp-flag)
  "Completion function for confluence labels."
  (if (not current-completions)
      (with-current-buffer completion-buffer
        (setq current-completions (cf-result-to-completion-list (cf-rpc-get-recent-labels
                                                                 confluence-max-completion-results) "name"))))
  (cf-complete comp-str pred comp-flag current-completions))

(defun cf-complete (comp-str pred comp-flag comp-table)
  "Executes completion for the given args and COMP-TABLE."
  (cond
   ((not comp-flag)
    (or (try-completion comp-str comp-table pred) comp-str))
   ((eq comp-flag t)
    (or (all-completions comp-str comp-table pred) (list comp-str)))
   ((eq comp-flag 'lambda)
    (and (assoc comp-str comp-table) t))))

(defun cf-update-buffer-name ()
  "Sets the buffer name based on the buffer info if it is a page buffer."
  (let ((page-name (cf-get-struct-value confluence-page-struct "title"))
        (space-name (cf-get-struct-value confluence-page-struct "space")))
    ;; only update if the current buffer has title and space (this method will
    ;; do nothing on search pages)
    (if (and (cf-string-notempty page-name)
             (cf-string-notempty space-name))
        (rename-buffer (cf-format-buffer-name page-name space-name)))))

(defun cf-format-buffer-name (page-name space-name)
  "Formats the name of the buffer given the page and space name."
  (format "%s<%s>" page-name space-name))

(defun cf-get-url ()
  "Gets the confluence url to use for the current operation."
  ;; get the relevant url, by precedence:
  ;; - input url - optionally defined by current operation
  ;; - page url - if current buffer is confluence buffer, this will be the url
  ;;              from which it was loaded
  ;; - confluence-url user configured default
  (or confluence-input-url confluence-page-url confluence-url))

(defun cf-get-default-space ()
  "Gets the default confluence space to use for the current operation."
  (cf-get-struct-value confluence-default-space-alist (cf-get-url)))

(defun cf-string-notempty (str)
  "Returns t if the given string is not empty."
  (> (length str) 0))

(defun cf-string-empty (str)
  "Returns t if the given string is empty."
  (= (length str) 0))

(defun cf-maybe-url-decode-entities-in-value (value)
  "Decodes XML entities in the given value, which may be a struct, list or
something else.  This is only done if the xml-substitute-special
function was not successfully overridden."
  (if (not confluence-xml-substitute-special)
      (cond 
       ((listp value)
        (dolist (struct-val value)
          (setcdr struct-val 
                  (cf-maybe-url-decode-entities-in-value (cdr struct-val)))))
       ((stringp value)
        (setq value (cf-url-decode-entities-in-string value)))))
  value)

(defun cf-url-decode-entities-in-string (string)
  "Convert XML entities to string values:
    &amp;    ==>  &
    &lt;     ==>  <
    &gt;     ==>  >
    &quot;   ==>  \"
    &apos;   ==>  '
    &#[0-9]+ ==>  <appropriate char>"
  (if (and (stringp string)
           (string-match "[&\r]" string))
      (save-excursion
	(set-buffer (get-buffer-create " *Confluence-decode*"))
	(erase-buffer)
	(buffer-disable-undo (current-buffer))
	(insert string)
        (cf-url-decode-entities-in-buffer (current-buffer))

        ;; always convert to unix newlines
	(goto-char (point-min))
        (while (re-search-forward "\r\n" nil t)
          (replace-match "\n" t t))
	(buffer-string))
    string))

(defun cf-url-decode-entities-in-buffer (decode-buffer)
  "Convert XML entities to string values:
    &amp;    ==>  &
    &lt;     ==>  <
    &gt;     ==>  >
    &quot;   ==>  \"
    &apos;   ==>  '
    &#[0-9]+ ==>  <appropriate char>"
  (save-excursion
    (set-buffer decode-buffer)
    (goto-char (point-min))
    (while (re-search-forward "&\\([^;\n]+\\);" nil t)
      (let ((ent-str (match-string-no-properties 1))
            (ent-point (match-beginning 1)))
        (replace-match 
         (cond
          ;; simple xml entities
          ((cdr-safe (assoc ent-str confluence-xml-entity-alist)))
          ;; decimal number character entities
          ((save-match-data
             (and (string-match "^#\\([0-9]+\\)$" ent-str)
                  (cf-number-entity-to-string (string-to-number (match-string-no-properties 1 ent-str))))))
          ;; hexidecimal number character entities
          ((save-match-data
             (and (string-match "^#x\\([0-9A-Fa-f]+\\)$" ent-str)
                  (cf-number-entity-to-string (string-to-number (match-string-no-properties 1 ent-str) 16)))))
          ;; unknown entity
          (t (concat "&" ent-str ";")))
         t t)
        (goto-char ent-point)))))

(defun cf-number-entity-to-string (num)
  "Convert an xml number entity value to the appropriate character string."
  (string (decode-char 'ucs num)))

(defun cf-string-to-number-entity (str)
  "Convert a single character string to the appropriate xml number entity value"
  (encode-char (string-to-char str) 'ucs))

(defun cf-url-encode-nonascii-entities-in-string (value)
  "Entity encodes any non-ascii values in the given string."
  (if (string-match "[^[:ascii:]]" value)
      (with-temp-buffer
        (insert value)
        (goto-char (point-min))
        (while (re-search-forward "[^[:ascii:]]" nil t)
          (let ((encoded-char (cf-string-to-number-entity (match-string 0))))
            (replace-match (concat "&#" (number-to-string encoded-char) ";") t t)))
        (setq value (buffer-string))))
  value)

(if confluence-xml-substitute-special 
    (defadvice xml-substitute-special (around xml-substitute-special-fixed
                                              activate compile preactivate)
      "Fix (possibly) broken entity decoding in `xml-substitute-special'."
      (if confluence-do-coding
          (let ((decoded-string (cf-url-decode-entities-in-string (ad-get-arg 0))))
            ;; if xml-rpc is expecting utf-8, re-encode this string
            (if xml-rpc-allow-unicode-string
                (setq decoded-string (encode-coding-string decoded-string 'utf-8 t)))
            (setq ad-return-value decoded-string))
        ad-do-it)))

(if confluence-xml-escape-string 
    (defadvice xml-escape-string (around xml-escape-string-fixed
                                         activate compile preactivate)
      "Fix double entity encoding caused by `xml-escape-string'."
      (if confluence-do-coding
          (setq ad-return-value (ad-get-arg 0))
        ad-do-it)))

(defadvice url-insert-entities-in-string (around url-insert-entities-in-string-nonascii
                                          activate compile preactivate)
  "Encode any non-ascii characters in the xml string after encoding the
basic entities."
  ad-do-it
  (if confluence-do-coding
      (setq ad-return-value 
            (cf-url-encode-nonascii-entities-in-string ad-return-value))))

(defadvice url-display-percentage (around url-display-percentage-quiet
                                          activate compile preactivate)
  "Make `url-display-percentage' respect `url-show-status'."
  (if url-show-status
      ad-do-it))

;;;;;;;;;;;;;;;;;;;
;;; Confluence mode

(defvar confluence-code-face 'confluence-code-face)

(defface confluence-code-face
  '((((class color) (background dark))
     (:foreground "dim gray" :bold t))
    (((class color) (background light))
     (:foreground "dim gray"))
    (t (:bold t)))
  "Font Lock Mode face used for code in confluence pages.")

(defvar confluence-panel-face 'confluence-panel-face)

(defface confluence-panel-face
  '((((class color) (background dark))
     (:background "LightGray"))
    (((class color) (background light))
     (:background "LightGray"))
    (t nil))
  "Font Lock Mode face used for panel in confluence pages.")


(defconst confluence-font-lock-keywords-1
  (list
  
   '("{\\([^{}:\n]+:?\\)[^{}\n]*}"
     (1 'font-lock-constant-face))
  
   '("{[^{}\n]+[:|]title=\\([^}|\n]+\\)[^{}\n]*}"
     (1 'bold append))
  
   '("{warning\\(?:[:][^}\n]*\\)?}\\(\\(.\\|[\n]\\)*?\\){warning}"
     (1 'font-lock-warning-face prepend))
   '("{note\\(?:[:][^}\n]*\\)?}\\(\\(.\\|[\n]\\)*?\\){note}"
     (1 'font-lock-minor-warning-face prepend))
   '("{info\\(?:[:][^}\n]*\\)?}\\(\\(.\\|[\n]\\)*?\\){info}"
     (1 'font-lock-doc-face prepend))
   '("{tip\\(?:[:][^}\n]*\\)?}\\(\\(.\\|[\n]\\)*?\\){tip}"
     (1 'font-lock-comment-face prepend))
  
   ;; bold
   '("[^[:word:]\\*][*]\\([^*\n]+\\)[*]\\W"
     (1 'bold))
   
   ;; code
   '("{{\\([^}\n]+\\)}}"
     (1 'confluence-code-face t))
   
   ;; italics/emphasised
   '("[^[:word:]\\]_\\([^_\n]+\\)_\\W"
     (1 'italic prepend))
   '("[^[:word:]\\][?]\\{2\\}\\([^?\n]+\\)[?]\\{2\\}\\W"
     (1 'italic prepend))

   ;; underline
   '("[^[:word:]\\][+]\\([^+\n]+\\)[+]\\W"
     (1 'underline prepend))

   ;; strike-through
   '("[^[:word:]\\][-]\\([^-\n]+\\)[-]\\W"
     (1 '(:strike-through t) prepend))

   ;; headings
   '("^h1[.] \\(.*?\\)\\s-*$"
     (1 '(bold underline) prepend))
   '("^h2[.] \\(.*?\\)\\s-*$"
     (1 '(bold italic underline) prepend))
   '("^h3[.] \\(.*?\\)\\s-*$"
     (1 '(italic underline) prepend))
   '("^h[4-9][.] \\(.*?\\)\\s-*$"
     (1 'underline prepend))

   ;; bullet points
   '("^\\([*#]+\\)\\s-"
     (1 'font-lock-constant-face))
   
   ;; links
   '("\\(\\[\\)\\([^]|\n]*\\)[|]\\([^]\n]+\\)\\(\\]\\)"
     (1 'font-lock-constant-face)
     (2 'font-lock-string-face)
     (3 'underline)
     (4 'font-lock-constant-face))
   '("\\(\\[\\)\\([^]|\n]+\\)\\(\\]\\)"
     (1 'font-lock-constant-face)
     (2 '(font-lock-string-face underline))
     (3 'font-lock-constant-face))
   '("{anchor:\\([^{}\n]+\\)}"
     (1 'font-lock-string-face))

   ;; images, embedded content
   '("\\([!]\\)\\([^|\n]+\\)[|]\\(?:[^!\n]*\\)\\([!]\\)"
     (1 'font-lock-constant-face)
     (2 '(font-lock-reference-face underline))
     (3 'font-lock-constant-face))
   '("\\([!]\\)\\([^!|\n]+\\)\\([!]\\)"
     (1 'font-lock-constant-face)
     (2 '(font-lock-reference-face underline))
     (3 'font-lock-constant-face))
   
   ;; tables
   '("[|]\\{2\\}\\([^|\n]+\\)"
     (1 'bold))
   '("\\([|]\\{1,2\\}\\)"
     (1 'font-lock-constant-face))
   )
  
  "Basic level highlighting for confluence mode.")

(defconst confluence-font-lock-keywords-2
  (append confluence-font-lock-keywords-1
          (list
  
           ;; code/preformatted blocks
           '("{noformat\\(?:[:][^}\n]*\\)?}\\(\\(.\\|[\n]\\)*?\\){noformat}"
             (1 'confluence-code-face t))
           '("{code\\(?:[:][^}\n]*\\)?}\\(\\(.\\|[\n]\\)*?\\){code}"
             (1 'confluence-code-face t))

           ;; panels
           '("{panel\\(?:[:][^}\n]*\\)?}\\(?:\\s-*[\r]?[\n]\\)?\\(\\(.\\|[\n]\\)*?\\){panel}"
             (1 'confluence-panel-face append))
           ))
  "Gaudy level highlighting for confluence mode.")

(defvar confluence-font-lock-keywords confluence-font-lock-keywords-1
  "Default expressions to highlight in Confluence modes.")


(defun confluence-newline-and-indent ()
  "Inserts a newline and indents using the previous indentation.
Supports lists, tables, and headers."
  (interactive)
  (let ((indentation nil)
        (limit nil))
    ;; find the beginning of the previous line, skipping "soft" newlines if
    ;; "hard" newlines are being used (like in longlines mode)
    (save-excursion
      (while (and (search-backward "\n" nil 'silent)
                  use-hard-newlines
                  (not (get-text-property (match-beginning 0) 'hard))))
      (setq limit (point)))
    ;; find the indentation of the previous line
    (save-excursion
      (if (re-search-backward "^\\(?:\\(?:\\(?:[*#]+\\|h[0-9][.]\\)[ \t]+\\)\\|[|]+\\)" limit t)
          (setq indentation (match-string 0))))
    (newline)
    (if indentation
        (insert indentation))))

(defun confluence-list-indent-dwim (&optional arg)
  "Increases the list indentationn on the current line by 1 bullet.  With ARG decreases by 1 bullet."
  (interactive "P")
  (let ((indent-arg (if arg -1 1)))
    (if (and mark-active transient-mark-mode)
        (let ((beg (min (point) (mark)))
              (end (max (point) (mark)))
              (tmp-point nil))
          (save-excursion
            (goto-char end)
            (if (bolp)
                (forward-line -1))
            (setq tmp-point (line-beginning-position))
            (confluence-modify-list-indent indent-arg)
            (while (and (forward-line -1)
                        (not (equal (line-beginning-position) tmp-point))
                        (>= (line-end-position) beg))
              (setq tmp-point (line-beginning-position))
              (confluence-modify-list-indent indent-arg))
          ))
    (confluence-modify-list-indent indent-arg))))

(defun confluence-modify-list-indent (depth)
  "Updates the list indentation on the current line, adding DEPTH bullets if DEPTH is positive or removing DEPTH
bullets if DEPTH is negative (does nothing if DEPTH is 0)."
  (interactive "nList Depth Change: ")
  (save-excursion
    (beginning-of-line)
    (cond
     ((> depth 0)
      (let ((indent-str (concat (make-string depth ?*) " ")))
        (if (re-search-forward "\\=\\([*#]+\\)" (line-end-position) t)
            (setq indent-str (make-string depth (elt (substring (match-string 1) -1) 0))))
        (insert-before-markers indent-str)))
     ((< depth 0)
      (let ((tmp-point (point))
            (indent-str ""))
        (if (re-search-forward "\\=\\([*#]+\\)" (line-end-position) t)
            (progn 
              (setq indent-str (match-string 1))
              (setq indent-str
                    (if (< (abs depth) (length indent-str))
                        (substring indent-str 0 depth)
                      ""))))
        (delete-region tmp-point (point))
        (insert-before-markers indent-str))))))

(defsubst cf-region-is-active ()
  "Return t when the region is active."
  ;; The determination of region activeness is different in both Emacs and
  ;; XEmacs.
  (cond
   ;; Emacs
   ((boundp 'mark-active) mark-active)
   ;; XEmacs
   ((and (fboundp 'region-active-p)
         (boundp 'zmacs-regions)
         zmacs-regions)
    (region-active-p))
   ;; fallback; shouldn't get here
   (t (mark t))))

(defsubst cf-hard-newline ()
  "Return newline string, including hard property if hard newlines are being
used."
  (if use-hard-newlines
      (propertize "\n" 'hard 't)
    "\n"))

(defun cf-format-block-tag (tag-text tag-point)
  "Formats a block tag with appropriate newlines based on the insertion
point."
  (concat
   (if (equal (char-before tag-point) ?\n)
       ""
     (cf-hard-newline))
   tag-text
   (if (equal (char-after tag-point) ?\n)
       ""
     (cf-hard-newline))))

(defun cf-wrap-text (pre-wrap-str &optional post-wrap-str are-block-tags)
  "Wraps the current region (if active) or current word with PRE-WRAP-STR and
POST-WRAP-STR.  If POST-WRAP-STR is nil, PRE-WRAP-STR is reused.  If
ARE-BLOCK-TAGS is not nil, the wrap strings will be formatted using
`cf-format-block-tag' before insertion."
  (save-excursion
    (let ((beg nil)
          (end nil)
          (wrap-str nil)
          (end-marker (make-marker)))
      (if (cf-region-is-active)
          (progn
            (setq beg (region-beginning))
            (setq end (region-end))
            (deactivate-mark))
        (progn
          (backward-word 1)
          (setq beg (point))
          (forward-word 1)
          (setq end (point))))
      (if are-block-tags
          (setq pre-wrap-str (cf-format-block-tag pre-wrap-str beg)
                post-wrap-str (cf-format-block-tag (or post-wrap-str 
                                                       pre-wrap-str) end)))
      (set-marker end-marker end)
      (goto-char beg)
      (insert-before-markers pre-wrap-str)
      (goto-char end-marker)
      (insert-before-markers (or post-wrap-str pre-wrap-str))
      (set-marker end-marker nil))))

(defun confluence-boldify-text ()
  "Wraps the current region/word with *bold* marks."
  (interactive)
  (cf-wrap-text "*"))

(defun confluence-italicize-text ()
  "Wraps the current region/word with _italics_ marks."
  (interactive)
  (cf-wrap-text "_"))

(defun confluence-strike-text ()
  "Wraps the current region/word with -strikethrough- marks."
  (interactive)
  (cf-wrap-text "-"))

(defun confluence-underline-text ()
  "Wraps the current region/word with +underline+ marks."
  (interactive)
  (cf-wrap-text "+"))

(defun confluence-superscript-text ()
  "Wraps the current region/word with ^superscript^ marks."
  (interactive)
  (cf-wrap-text "^"))

(defun confluence-subscript-text ()
  "Wraps the current region/word with ~subscript~ marks."
  (interactive)
  (cf-wrap-text "~"))

(defun confluence-cite-text ()
  "Wraps the current region/word with ??citation?? marks."
  (interactive)
  (cf-wrap-text "??"))

(defun confluence-linkify-text (&optional link-url)
  "Wraps the current region/word as a [link]."
  (interactive "MURL: ")
  (cf-wrap-text "[" (concat (if (cf-string-notempty link-url)
                                (concat "|" link-url)
                              "") "]")))

(defun confluence-codify-text (&optional arg)
  "Wraps the current region/word as {{monospace}} if single-line, otherwise
as a {code}code block{code}."
  (interactive "P")
  (let ((pre-str "{{")
        (post-str "}}")
        (are-block-tags nil))
    (if (or arg
            (and (cf-region-is-active)
                 (save-excursion
                   (let ((beg (region-beginning))
                         (end (region-end))
                         (found-newline nil))
                     (goto-char beg)
                     ;; search for a non-soft newline in the current region
                     (while (and (search-forward "\n" end 'silent)
                                 (setq found-newline t)
                                 use-hard-newlines
                                 (not (get-text-property (match-beginning 0)
                                                         'hard))
                                 (setq found-newline 'soft)))
                     (eq found-newline t)))))
        (setq pre-str "{code:}"
              post-str "{code}"
              are-block-tags t))
    (cf-wrap-text pre-str post-str are-block-tags)))

(defun confluence-linkify-anchor-text (&optional anchor-name)
  "Wraps the current region/word as an anchor [link|#ANCHOR-NAME]."
  (interactive)
  (if (not anchor-name)
      (let ((cur-anchors (cf-get-page-anchors)))
        (setq anchor-name (cf-read-string-simple "Confluence Anchor Name: " 
                                                 nil cur-anchors))))
  (cf-wrap-text "[" (concat "|#" (or anchor-name "") "]")))

(defun confluence-linkify-attachment-text (&optional file-name)
  "Wraps the current region/word as an attachment [link|#FILE-NAME]."
  (interactive)
  (if (not file-name)
      (let ((cur-attachments 
             (if confluence-page-id
                 (with-quiet-rpc
                  (cf-result-to-completion-list
                   (cf-rpc-get-attachments confluence-page-id) "fileName"))
               nil)))
        (setq file-name (cf-read-string-simple "Confluence attachment file name: " 'confluence-attachment-history cur-attachments))))
  (cf-wrap-text "[" (concat "|^" (or file-name "") "]")))

(defun confluence-embed-text ()
  "Wraps the current region/word as an embedded content !link!."
  (interactive)
  (cf-wrap-text "!"))

(defun confluence-insert-anchor (anchor-name)
  "Inserts an {anchor}."
  (interactive "MNew AnchorName: ")
  (insert "{anchor:" anchor-name "}"))

(defun confluence-insert-horizontal-rule ()
  "Inserts horizontal rule."
  (interactive)
  (insert (cf-format-block-tag 
           (concat (cf-hard-newline) "----" (cf-hard-newline)) 
           (point))))

(defvar confluence-format-prefix-map
  (let ((map (make-sparse-keymap)))
    (define-key map "i" 'confluence-italicize-text)
    (define-key map "c" 'confluence-codify-text)
    (define-key map "b" 'confluence-boldify-text)
    (define-key map "l" 'confluence-linkify-text)
    (define-key map "u" 'confluence-underline-text)
    (define-key map "a" 'confluence-linkify-anchor-text)
    (define-key map "t" 'confluence-linkify-attachment-text)
    (define-key map "A" 'confluence-insert-anchor)
    (define-key map "e" 'confluence-embed-text)
    (define-key map "h" 'confluence-insert-horizontal-rule)
    (define-key map "s" 'confluence-superscript-text)
    (define-key map "S" 'confluence-subscript-text)
    (define-key map "C" 'confluence-cite-text)
    (define-key map "x" 'confluence-strike-text)
    map)
  "Keybinding prefix map which can be bound for common formatting functions in
confluence mode.")

(defvar confluence-prefix-map
  (let ((map (make-sparse-keymap)))
    (define-key map "f" 'confluence-get-page)
    (define-key map "c" 'confluence-create-page)
    (define-key map "=" 'confluence-ediff-current-page)
    (define-key map "m" 'confluence-ediff-merge-current-page)
    (define-key map "p" 'confluence-get-parent-page)
    (define-key map "r" 'confluence-rename-page)
    (define-key map "s" 'confluence-search)
    (define-key map "." 'confluence-get-page-at-point)
    (define-key map "*" 'confluence-pop-tag-stack)
    (define-key map "v" 'confluence-preview)
    (define-key map "a" 'confluence-get-attachment)
    (define-key map "b" 'confluence-browse-page)
    (define-key map "x" 'confluence-get-related-page)
    (define-key map "j" confluence-format-prefix-map)
    (define-key map "l"
      (let ((label-map (make-sparse-keymap)))
        (define-key label-map "a" 'confluence-add-label)
        (define-key label-map "r" 'confluence-remove-label)
        (define-key label-map "g" 'confluence-get-labels)        
        label-map))
    map)
  "Keybinding prefix map which can be bound for common functions in confluence
mode.")


(define-derived-mode confluence-mode text-mode "Confluence"
  "Set major mode for editing Confluence Wiki pages."
  (turn-off-auto-fill)
  (make-local-variable 'revert-buffer-function)
  (setq revert-buffer-function 'cf-revert-page)
  ;; FIXME, should we support local backup files?
  (make-local-variable 'make-backup-files)
  (setq make-backup-files nil)
  (make-local-variable 'words-include-escapes)
  (setq words-include-escapes t)
  (add-hook 'write-contents-hooks 'cf-save-page)
  ;; we set this to some nonsense so save-buffer works
  (setq buffer-file-name (expand-file-name (concat "." (buffer-name)) "~/"))
  (set-syntax-table (make-syntax-table (syntax-table)))
  (modify-syntax-entry ?\\ "\\")
  (setq font-lock-defaults
        '((confluence-font-lock-keywords confluence-font-lock-keywords-1
                                         confluence-font-lock-keywords-2)
          nil nil nil nil (font-lock-multiline . t)))
)

(define-derived-mode confluence-search-mode confluence-mode "ConfluenceSearch"
  "Set major mode for viewing Confluence Search results."
  (local-set-key [return] 'confluence-get-page-at-point)
)

;; TODO 
;; - add "backup" support (save to restore from local file)?
;; - extended link support
;;   - [$id] links?
;; - add more label support?
;; - change page preview to use async like attachments (xml parsing issues)
;; - add more structured browsing?
;; - funky searches:
;;   - labelText:<label>
;;   - title:<title> -- completion

(provide 'confluence)
;;; confluence.el ends here
