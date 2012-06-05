;;; weblogger.el --- Weblog maintenance via XML-RPC APIs

;; Copyright (C) 2002-2009 Mark A. Hershberger.
;; Inspired by code Copyright (C) 2001 by Simon Kittle.
;; Parts Copyright (C) 2007 Wickersheimer Jeremy.

;; Original Author: Mark A. Hershberger <mah@everybody.org>
;; Created: 2002 Oct 11
;; Keywords: weblog blogger cms movable type openweblog blog
;; URL: http://launchpad.net/weblogger-el
;; Version: 1.4.5
;; Last Modified: <2010-03-11 01:00:19 mah>
;; Package-Requires: ((xml-rpc "1.6.8"))

(defconst weblogger-version "1.4.5"
  "Current version of weblogger.el")

;; This file is NOT (yet) part of GNU Emacs.

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

;; weblogger.el implements the Blogger, MetaWeblog, Movable Type, and
;; LiveJournal APIs to talk to server-side weblog software.

;;; Installation:

;; If you use ELPA (http://tromey.com/elpa), you can install via the
;; M-x package-list-packages interface. This is preferrable as you
;; will have access to updates automatically.

;; Otherwise, just make sure this file and xml-rpc.el are in your
;; load-path (usually ~/.emacs.d is included) and put
;; (require 'weblogger) in your ~/.emacs or ~/.emacs.d/init.el file.

;;; Starting Out:

;; If you don't yet have a weblog, you can set one up for free on
;; various services.  (I suggest OpenWeblog.com, but then I run that
;; site :) )
;;
;; To set up your profile:
;;
;;    M-x weblogger-setup-weblog RET

;; You will be prompted for some information.  The URL should be the
;; one that uses the API you're using, not the one you would use for
;; typing an entry.  For instance, in wordpress, use
;; <blog-url>/xmlrpc.php.

;; *** FIXME This section is complete fantasy at the moment.
;; ;; If you already have a weblog, and your weblog supports RSD
;; ;; (http://archipelago.phrasewise.com/rsd), you can use
;; ;;
;; ;;    M-x weblogger-discover-server RET url RET
;; ;;
;; ;; where url is the URL of your weblog.  This will set up a
;; ;; ~/.webloggerrc file for you if you let it.

;; You can also set up your server information using
;;
;;    M-x customize-group RET weblogger RET
;;
;;; Keymaps:
;;
;; I use the following commands in my .emacs file:
;;
;; (load-file "weblogger.el")
;; (global-set-key "\C-cbs" 'weblogger-start-entry)
;;
;; C-c b s will then switch to a new buffer where you can compose a
;; entry.
;;
;; C-x C-s    -- post-and-publish current buffer to the weblog.
;;               Calling weblogger-publish-entry with an prefix argument
;;               (i.e. C-u C-x C-s) will prompt for which weblog
;;               to use.
;;
;; C-c C-c    -- save as draft and bury the buffer.
;;
;; C-c C-n    -- post (but not publish) the current entry and
;;               load the next entry.
;;
;; C-c C-p    -- post (but not publish) the current entry and
;;               load the previous entry.
;;
;; C-c C-k    -- delete the current entry.
;;
;; M-g        -- synchronise weblogger.el's idea of the entries available
;;               with the weblog server.
;;
;; C-c C-t m  -- edit the main template.
;;
;; C-c C-t a  -- edit the Archive Index template
;;
;; C-c C-s s  -- Change the server being used.
;;
;; C-c C-s w  -- Change the weblog.
;;
;; C-c C-s u  -- Change the user (re-login).
;;
;;
;; Notes:
;; ----
;;
;; This code was originally based on Simon Kittle's blogger.el
;; (http://www.tswoam.co.uk/files/blogger.el.txt), but where his code
;; calls a Perl program, this code uses xml-rpc.el.  You can get
;; xml-rpc.el from <http://elisp.info/package/xml-rpc/>
;;
;; Differences between SK's blogger.el and weblogger.el
;;
;; - Doesn't need any external programs.  Uses xml-rpc.el.
;; - I've added a bunch of defcustom's here to make this integrate
;;   better with Emacs Customization interface.
;; - Created a *weblogger-entry* mode.
;; - Made selection of a weblog more intuitive.  It queries the
;;   server and allows the user to choose the name of the
;;   weblog from a list.
;; - Prompt for weblog on initial entry if weblogger-id isn't set.
;; - Can "ping" http://weblogs.com/ and http://blo.gs/ whenever
;;   you update.
;; - Can "scroll" through entries on the weblog server and edit them.
;; - Many other features.
;;
;;  TODO: (low hanging fruit first?)
;;  * Move APIs to their own file
;;  * RSD
;;  * Menus
;;  * Toolbar
;;  * More robust support for metaWebBlog API
;;  * Support more than just the metaWebBlog API -- ATOM especially
;;  ** WordPress "Page" selection and "Category" support
;;  * Weblog creation using OpenWeblog.com
;;  * Comments
;;  * Develop a minor mode that will allow posting buffer contents
;;    to a weblog.  This way, you can work using nxml/sgml modes on a
;;    buffer and then post the results directly.
;;
;; Bugs/Features:
;;
;;  * When you delete a entry it gets deleted, but it doesn't
;;    disappear from your entry ring until you sync (M-g) with the
;;    server.  But this could be construed as a (mis)feature.
;;  * If the server isn't reachable, (weblogger-determine-capabilities)
;;    will get the wrong information.
;;  * Changed titles aren't put in the weblogger post ring.
;;  * Dependency issues: Use GnuTLS (gnutls-cli) for SSL encryption
;;  ** Otherwise, you may get /a lot/ of terminal beeps and errors
;;  ** (This is a dependency of url.el, but is listed here for clarity.)

(require 'xml-rpc)
(require 'message)
(require 'ring)
(eval-when-compile
  (require 'cl))

(defconst weblogger-maintainer-address "mah@everybody.org"
  "The address where bug reports should be sent.")

(defgroup weblogger nil
  "Edit Weblogs with Emacs."
  :group 'emacs)

(defcustom weblogger-server-username nil
  "Your weblog server username.  You will be prompted if this is left nil."
  :group 'weblogger
  :type 'string)

(defcustom weblogger-server-password ""
  "Your password.  You will be prompted if this is empty or nil."
  :group 'weblogger
  :type 'string)

(defcustom weblogger-server-url
  "http://www.openweblog.com/interface/blogger/"
  "Server you want to use.  If this is an OpenWeblog.com site, leave this
at the default.  Otherwise, you will need to change it."
  :group 'weblogger
  :type 'string)

(defcustom weblogger-weblog-id nil
  "Your weblog ID.  For many weblog servers, you can leave this
nil and weblogger.el will prompt you for the weblog.  If it is a
Manila site, you need to provide the URL of your site."
  :group 'weblogger
  :type 'string)

(defcustom weblogger-max-entries-in-ring 20
  "Maximum number of entries that will be retrieved from the
server.  There may be a server-side limitation to this number."
  :group 'weblogger
  :type 'integer)

(defcustom weblogger-ping-urls '("http://rpc.weblogs.com/RPC2")
  "List of URLs to ping using the XML-RPC interface defined at
<http://www.xmlrpc.com/weblogsCom>."
  :group 'weblogger
  :type 'list)

(defcustom weblogger-save-password nil
  "Whether to save to the password or not."
  :group 'weblogger
  :type 'boolean)

(defcustom weblogger-config-alist nil
  "Alist of possible configurations."
  :group 'weblogger
  :type '(alist :tag "Name"
                :key-type (string :tag "Configuration Name")
                :value-type (list :tag "Weblog Config"
                                  (string :tag "Server URL")
                                  (string :tag "Username")
                                  (string :tag "Password")
                                  (string :tag "Weblog ID"))))

(defcustom weblogger-blogger-firstline-title nil
  "Look for the title in the first line surrounded by <title>
tags when using the Blogger API."
  :group 'weblogger
  :type 'boolean)

(defcustom weblogger-config-name "default"
  "Name of the default configuration."
  :group 'weblogger
  :type 'string)

(defcustom weblogger-start-edit-entry-hook
  (list (lambda ()
          (message-goto-body)
          (while (search-forward "\r" nil t)
            (replace-match "" nil t))))
  "Hook to run after loading an entry in buffer for editing."
  :group 'weblogger
  :type 'hook)

(defcustom weblogger-edit-entry-hook nil
  "Hook to run after updating an entry."
  :group 'weblogger
  :type 'hook)

(defcustom weblogger-pre-struct-hook nil
  "Hook to run just before the buffer is converted to a struct to
send to the server."
  :group 'weblogger
  :type 'hook)

(defcustom weblogger-edit-mode 'nxml-mode
  "Major mode to use for editing weblog entries"
  :group 'weblogger
  :type 'function)

(defcustom weblogger-edit-mode-toggle-hook nil
  "Hook to call when switching to edit mode"
  :group 'weblogger
  :type 'hook)

(defcustom weblogger-weblogger-mode-toggle-hook nil
  "Hook to call when switching back to weblogger mode"
  :group 'weblogger
  :type 'hook)

(defvar weblogger-entry-list nil
  "List of weblog entries that we know about. Chronological
order, with newest first.")

(defvar weblogger-category-list nil
  "List of categories that we know about.")

(defvar weblogger-server-userid nil
  "Server-side ID of logged in user.")

(defvar *weblogger-entry* nil
  "The buffer where we compose entries")

(defvar weblogger-entry-mode-hook nil
  "Hook to run after starting up weblogger mode.")

(defvar weblogger-new-entry-hook '(weblogger-ping-weblogs)
  "Hook to run after sending a new entry.  Typically, this is
where you would put weblogger-ping-weblogs to let weblog
aggregators know that you have updated.")

(defvar weblogger-entry-mode-map nil
  "Keymap for weblogger-entry-mode.")

(defvar weblogger-template-type)
(defvar weblogger-template-mode-map nil
  "Keymap for weblogger-template-mode.")

(defvar weblogger-entry-ring nil
  "Ring that holds all the entries.")

(defvar weblogger-category-ring nil
  "Ring that holds all the categories.")

(defvar weblogger-ring-index 0
  "Pointer to the index on the ring")

(defvar weblogger-capabilities nil
  "Known capabilities of the remote host")

(defvar weblogger-default-title ""
  "The Default title to use when making an entry.  This is added
if your weblog server supports titles on entries but you haven't
set one.  Set to \"\" for no title.")

(defvar weblogger-default-categories nil
  "The default list of categories when making an entry.  This is
added if your weblog server supports categories on entries but you
haven't set one.  Set to nil for no category.")

(defvar weblogger-api-new-entry nil)
(defvar weblogger-api-send-edits nil)
(defvar weblogger-api-list-entries nil)
(defvar weblogger-api-list-categories nil)
(defvar weblogger-api-delete-entry 'weblogger-api-blogger-delete-entry)

(defvar weblogger-weblog-alist nil
  "Weblogs the user can use on the server.")
(defvar weblogger-texttype-alist nil
  "Texttypes supported by the server.")

(defvar menu-bar-weblogger-menu nil)

(defvar weblogger-header nil
  "Holds the weblog header")

(defconst weblogger-blogger-app-key
  "07C72E6970E0FBA5DE21BA9F4800C44534C19870"
  "OBSOLETE. The appkey to send to weblog server.  Generally this
shouldn't be changed.")

(defconst weblogger-no-capabilities '(("wp.getUsersBlogs" . nil)
                                      ("wp.getPage" . nil)
                                      ("wp.getPages" . nil)
                                      ("wp.newPage" . nil)
                                      ("wp.deletePage" . nil)
                                      ("wp.editPage" . nil)
                                      ("wp.getPageList" . nil)
                                      ("wp.getAuthors" . nil)
                                      ("wp.getCategories" . nil)
                                      ("wp.getTags" . nil)
                                      ("wp.newCategory" . nil)
                                      ("wp.deleteCategory" . nil)
                                      ("wp.suggestCategories" . nil)
                                      ("wp.uploadFile" . nil)
                                      ("wp.getCommentCount" . nil)
                                      ("wp.getPostStatusList" . nil)
                                      ("wp.getPageStatusList" . nil)
                                      ("wp.getPageTemplates" . nil)
                                      ("wp.getOptions" . nil)
                                      ("wp.setOptions" . nil)
                                      ("wp.getComment" . nil)
                                      ("wp.getComments" . nil)
                                      ("wp.deleteComment" . nil)
                                      ("wp.editComment" . nil)
                                      ("wp.newComment" . nil)
                                      ("wp.getCommentStatusList" . nil)
                                      ("blogger.getUsersBlogs" . nil)
                                      ("blogger.getUserInfo" . nil)
                                      ("blogger.getPost" . nil)
                                      ("blogger.getRecentPosts" . nil)
                                      ("blogger.getTemplate" . nil)
                                      ("blogger.setTemplate" . nil)
                                      ("blogger.newPost" . nil)
                                      ("blogger.editPost" . nil)
                                      ("blogger.deletePost" . nil)
                                      ("metaWeblog.newPost" . nil)
                                      ("metaWeblog.editPost" . nil)
                                      ("metaWeblog.getPost" . nil)
                                      ("metaWeblog.getRecentPosts" . nil)
                                      ("metaWeblog.getCategories" . nil)
                                      ("metaWeblog.newMediaObject" . nil)
                                      ("metaWeblog.deletePost" . nil)
                                      ("metaWeblog.getTemplate" . nil)
                                      ("metaWeblog.setTemplate" . nil)
                                      ("metaWeblog.getUsersBlogs" . nil)
                                      ("mt.getCategoryList" . nil)
                                      ("mt.getRecentPostTitles" . nil)
                                      ("mt.getPostCategories" . nil)
                                      ("mt.setPostCategories" . nil)
                                      ("mt.supportedMethods" . nil)
                                      ("mt.supportedTextFilters" . nil)
                                      ("mt.getTrackbackPings" . nil)
                                      ("mt.publishPost" . nil)
                                      ("pingback.ping" . nil)
                                      ("pingback.extensions.getPingbacks" . nil)
                                      ("demo.sayHello" . nil)
                                      ("demo.addTwoNumbers" . nil)
                                      ("wpStats.check_key" . nil)
                                      ("wpStats.get_blog_id" . nil)
                                      ("wpStats.get_site_id" . nil)
                                      ("wpStats.update_bloginfo" . nil)
                                      ("wpStats.update_postinfo" . nil)
                                      ("wpStats.ping_blog" . nil)
                                      ("wpStats.flush_posts" . nil)))

(unless weblogger-entry-mode-map
  (setq weblogger-entry-mode-map
        (let ((map (copy-keymap message-mode-map))
              (template-map (make-sparse-keymap)))
          (define-key map "\C-c\C-c" 'weblogger-send-entry)
          (define-key map "\C-x\C-s" 'weblogger-publish-entry)
          (when (fboundp 'unicode-smart-double-quote)
            (define-key map "\"" 'unicode-smart-double-quote)
            (define-key map "'" 'unicode-smart-single-quote)
            (define-key map "-" 'unicode-smart-hyphen)
            (define-key map "." 'unicode-smart-period))
          (define-key map "\C-c\C-n" 'weblogger-next-entry)
          (define-key map "\C-c\C-p" 'weblogger-prev-entry)
          (define-key map "\C-c\C-k" 'weblogger-delete-entry)
          (define-key map "\M-g"     'weblogger-fetch-entries)
          (define-key template-map "m" 'weblogger-edit-main-template)
          (define-key template-map "a" 'weblogger-edit-archive-template)
          (define-key map "\C-c\C-t" template-map)
          (define-key map "\C-c\C-o" 'weblogger-change-server)
          (define-key map "\C-c\C-w" 'weblogger-change-weblog)
          (define-key map "\C-c\C-u" 'weblogger-change-user)
          (define-key map "\C-c\C-e" 'weblogger-toggle-edit-body)
          (define-key map (kbd "C-c C-a") 'weblogger-publish-to-all-weblogs)
          map)))

(unless weblogger-template-mode-map
  (setq weblogger-template-mode-map (copy-keymap text-mode-map))
  (define-key weblogger-template-mode-map "\C-x\C-s"
    'weblogger-save-template))

(unless (fboundp 'define-key-after)
  (defun define-key-after (keymap key definition &optional after)
    "Add binding in KEYMAP for KEY => DEFINITION, right after AFTER's binding.
This is like `define-key' except that the binding for KEY is placed
just after the binding for the event AFTER, instead of at the beginning
of the map.  Note that AFTER must be an event type (like KEY), NOT a command
\(like DEFINITION).

If AFTER is t or omitted, the new binding goes at the end of the keymap.
AFTER should be a single event type--a symbol or a character, not a sequence.

Bindings are always added before any inherited map.

The order of bindings in a keymap matters when it is used as a menu."
    (unless after (setq after t))
    (or (keymapp keymap)
        (signal 'wrong-type-argument (list 'keymapp keymap)))
    (setq key
          (if (<= (length key) 1) (aref key 0)
            (setq keymap (lookup-key keymap
                                     (apply 'vector
                                            (butlast (mapcar 'identity key)))))
            (aref key (1- (length key)))))
    (let ((tail keymap) done inserted)
      (while (and (not done) tail)
        ;; Delete any earlier bindings for the same key.
        (if (eq (car-safe (car (cdr tail))) key)
            (setcdr tail (cdr (cdr tail))))
        ;; If we hit an included map, go down that one.
        (if (keymapp (car tail)) (setq tail (car tail)))
        ;; When we reach AFTER's binding, insert the new binding after.
        ;; If we reach an inherited keymap, insert just before that.
        ;; If we reach the end of this keymap, insert at the end.
        (if (or (and (eq (car-safe (car tail)) after)
                     (not (eq after t)))
                (eq (car (cdr tail)) 'keymap)
                (null (cdr tail)))
            (progn
              ;; Stop the scan only if we find a parent keymap.
              ;; Keep going past the inserted element
              ;; so we can delete any duplications that come later.
              (if (eq (car (cdr tail)) 'keymap)
                  (setq done t))
              ;; Don't insert more than once.
              (or inserted
                  (setcdr tail (cons (cons key definition) (cdr tail))))
              (setq inserted t)))
        (setq tail (cdr tail))))))

(unless menu-bar-weblogger-menu
  (easy-menu-define
    menu-bar-weblogger-menu weblogger-entry-mode-map ""
    '("Weblogger"
      ["Start a new Weblog Entry"     weblogger-start-entry t]
      ["Save weblog entry as draft"   weblogger-save-entry t]
      ["Publish weblog entry"         weblogger-send-entry t :active (buffer-modified-p)]
      ["--" nil nil]
      ["Switch to edit mode"          weblogger-toggle-edit-body t]
      ["--" nil nil]
      ["Delete entry"                 weblogger-delete-entry t]
      ["--" nil nil]
      ["Previous entry"               weblogger-prev-entry t]
      ["Next entry"                   weblogger-next-entry t]
      ["--" nil nil]
      ["Edit Main Template"           weblogger-edit-main-template t]
      ["Edit Archive Template"        weblogger-edit-main-template t]
      ["--" nil t]
      ["Set edit mode"                (lambda () (interactive) (customize-variable 'weblogger-edit-mode)) t]
      ["Change Weblog"                weblogger-change-weblog t]
      ["Setup Weblog"                 weblogger-setup-weblog t]))
  (when (boundp 'menu-bar-tools-menu)
    (define-key-after menu-bar-tools-menu [separator-weblogger]
      '("--") 'simple-calculator)
    (define-key-after menu-bar-tools-menu [start-weblog]
      '(menu-item "Start a new Weblog Entry" weblogger-start-entry :enable
                  (or weblogger-config-alist weblogger-server-url))
      'separator-weblogger)
    (define-key-after menu-bar-tools-menu [setup-weblog]
      '(menu-item "Setup your Weblog" weblogger-setup-weblog) 'start-weblog)))

(defun weblogger-submit-bug-report ()
 "Submit a bug report on weblogger."
 (interactive)
 (require 'reporter)
 (let ((xml-rpc-tz-pd-defined-in
        (if (fboundp 'find-lisp-object-file-name)
            (find-lisp-object-file-name
             'timezone-parse-date (symbol-function 'timezone-parse-date))
          (symbol-file 'timezone-parse-date)))
       (date-parses-as (timezone-parse-date "20091130T00:52:53")))
   (reporter-submit-bug-report
    weblogger-maintainer-address
    (concat "weblogger.el " weblogger-version)
    (list 'xml-rpc-tz-pd-defined-in
          'date-parses-as
          'xml-rpc-load-hook
          'xml-rpc-use-coding-system
          'xml-rpc-allow-unicode-string
          'xml-rpc-base64-encode-unicode
          'xml-rpc-base64-decode-unicode
          'weblogger-config-alist
          'weblogger-config-name
          'weblogger-start-edit-entry-hook
          'weblogger-edit-entry-hook
          'weblogger-pre-struct-hook
          'weblogger-edit-mode
          'weblogger-edit-mode-toggle-hook
          'weblogger-weblogger-mode-toggle-hook
          'weblogger-server-url
          'weblogger-entry-mode-hook
          'weblogger-new-entry-hook
          'weblogger-capabilities))))

;;;###autoload
(defun weblogger-select-configuration (&optional config)
  "Select a previously saved configuration."
  (interactive)
  (let* ((completion-ignore-case t)
         (name (or config
                   (if (= 1 (length weblogger-config-alist))
                       (caar weblogger-config-alist)
                     (completing-read
                      "Config Name: " weblogger-config-alist nil t)))))

    (weblogger-switch-configuration name)
    (weblogger-api-blogger-weblog-alist t)
    (weblogger-fetch-entries)))

;;;###autoload
(defun weblogger-setup-weblog ()
  "Create a profile for a weblog."
  (interactive)
  (weblogger-change-server)
  (setq weblogger-config-name nil)
  (let ((user   (weblogger-server-username t))
        (pass   (weblogger-server-password t))
        (weblog (weblogger-weblog-id       t)))
    (setq weblogger-config-name
	  (read-from-minibuffer "Name this configuration: " "default"))

    (let ((conf (assoc weblogger-config-name weblogger-config-alist))
	  (settings (list weblogger-server-url user
                          (if weblogger-save-password pass "") weblog)))
      (if conf (setcdr conf settings)
        (if (or (not weblogger-config-alist)
                (not (listp weblogger-config-alist)))
	    (setq weblogger-config-alist
                  (list (cons weblogger-config-name settings)))
	  (add-to-list 'weblogger-config-alist
		       (cons weblogger-config-name
			     settings)))))
    (weblogger-save-configuration)
    (weblogger-fetch-entries)))

(defun weblogger-save-configuration ()
  "Save the current configuration using the name from CONFIG in
the filename in weblogger-config-file."
  (customize-save-variable 'weblogger-config-alist
			   weblogger-config-alist))

(defun weblogger-change-server ()
  "Change the server-url."
  (interactive)
  (setq weblogger-server-url
	(read-from-minibuffer "Server Endpoint (URL): "
                              (if (stringp weblogger-server-url)
                                  weblogger-server-url
                                "")))
  (weblogger-determine-capabilities))

(defun weblogger-change-user ()
  "Change username and password."
  (interactive)
  (weblogger-server-username t)
  (weblogger-server-password t))

(defun weblogger-change-weblog ()
  "Change the weblog."
  (interactive)
  (let ((point-save (point)))
    (weblogger-weblog-id t)
    (message-remove-header "Newsgroup")
    (message-add-header (concat "Newsgroup: "
				(weblogger-weblog-name-from-id
				 (weblogger-weblog-id))))
    (goto-char point-save)))

(defun weblogger-change-texttype ()
  "Change Text Type."
  (interactive)
  (let ((point-save (point)))
    (message-remove-header "X-TextType")
    (message-add-header (concat "X-TextType: "
				(weblogger-texttype-name-from-id
				 (weblogger-select-texttype))))
    (goto-char point-save)))

(define-derived-mode weblogger-entry-mode message-mode "Weblog"
  "Major mode for editing text for Weblogger.  Based on message-mode."
  ;; (interactive)
  ;; (message-mode)
  ;; (message-disassociate-draft)
  ;; (use-local-map weblogger-entry-mode-map)
  (unless weblogger-entry-ring
    (setq weblogger-entry-ring (make-ring weblogger-max-entries-in-ring))))

(defun weblogger-template-mode ()
  "Major mode for editing templates for Weblogger. Based on text-mode."
  (interactive)
  (text-mode)
  (use-local-map weblogger-template-mode-map)
  (setq mode-name "weblogger-template")
  (setq major-mode 'weblogger-template-mode))

(defun weblogger-edit-main-template ()
  "Edit the main template"
  (interactive)
  (weblogger-api-blogger-edit-template "main"))

(defun weblogger-edit-archive-template ()
  "Edit the template for archive listings"
  (interactive)
  (weblogger-api-blogger-edit-template "archive"))

;;;###autoload
(defun weblogger-start-entry (&optional prompt)
  "Start creating a weblog entry in the *weblogger-entry* buffer.
With a prefix, it will check the available weblogs on the server
and prompt for the weblog to post to if multiple ones are
available."
  (interactive "P")
  (if prompt (weblogger-weblog-id prompt))
  (unless weblogger-entry-ring
    (setq weblogger-entry-ring (make-ring weblogger-max-entries-in-ring))
    (ring-insert weblogger-entry-ring (list (cons "content" ""))))
  (when (assoc "entry-id" (ring-ref weblogger-entry-ring 0))
    (ring-insert weblogger-entry-ring (list (cons "content" ""))))
  (setq weblogger-ring-index 0)
  (weblogger-edit-entry))

(defun weblogger-entry-setup-headers (entry &optional body-line)
  "Add any pertinant headers to the weblog entry."
  (let ((entry-id (when (cdr (assoc  "entry-id" entry))
		    (if (stringp (cdr (assoc  "entry-id" entry)))
			(cdr (assoc  "entry-id" entry))
		      (int-to-string (cdr (assoc  "entry-id" entry))))))
	(title    (cdr (assoc "title"       entry))))

    (mapc 'message-add-header
	    (delq nil
		  (mapcar
		   (lambda (bit)
		     (when (car (cdr-safe bit))
		       (concat (car bit) ": "
			       (cadr bit))))
		   (list
		    (list "Message-ID"
			  (when entry-id
			    (format "<%s/%s@%s>"
				    entry-id
				    (weblogger-weblog-id)
				    (url-host (url-generic-parse-url
                                               weblogger-server-url)))))
		    (list "Date"
                          (format-time-string "%d %b %Y %H:%M:%S %z"
                                              (caddr (assoc "dateCreated"
                                                            entry))))
		    (list "In-Reply-To"
			  (let ((hold nil))
			    (mapc
			     (lambda (p)
			       (setq hold (concat hold p ", ")))
			     (cdr (assoc "trackbacks"  entry)))
			    (when hold hold)))
		    (list "X-URL"
			  (cdr (assoc "url" entry)))
		    (list "X-TextType"
			  (cdr (assoc "texttype" entry)))
		    (list "Subject" title)
		    (list "Keywords" (cdr (assoc "tags" entry)))
                                        ; Note that the blogger API on
                                        ; blogger.com is depcrated and
                                        ; broken on this element.
		    (list "From"
			  (or (cdr (assoc "authorName"  entry))
			      weblogger-server-username))
		    (list "Newsgroup"
			  (or (weblogger-weblog-name-from-id
                               (weblogger-weblog-id))
                              "unknown"))))))

    (goto-char (point-max))
    (when body-line
      (insert mail-header-separator "\n"))))

(defun weblogger-send-entry (&optional arg)
  "Send but not publish the current entry.  With optional
argument, prompts for the weblog to use."
  (interactive)
  (weblogger-save-entry nil arg)
  (bury-buffer))

(defun weblogger-publish-entry (&optional arg)
  "Publish the current entry.  With optional argument, prompts
for the weblog to use."
  (interactive)
  (set-buffer-modified-p t)
  (weblogger-save-entry t arg))

(defun weblogger-switch-configuration (config)
  "Switch the configuration."
  (let ((conf (cdr (assoc config weblogger-config-alist))))
    (setq weblogger-config-name     config)
    (setq weblogger-server-url      (nth 0 conf))
    (setq weblogger-server-username (nth 1 conf))
    (setq weblogger-server-password (nth 2 conf))
    (setq weblogger-weblog-id       (nth 3 conf))))

(defun weblogger-publish-to-all-weblogs ()
  "Publish to all weblogs in weblog-config-alist."
  (interactive)
  (let ((entry (weblogger-entry-buffer-to-struct))
        weblogger-config-name weblogger-server-url
        weblogger-server-username weblogger-server-password
        weblogger-weblog-id)
    (mapc (lambda (config)
            (weblogger-switch-configuration (car config))
            (weblogger-api-new-entry entry t))
          weblogger-config-alist)))

(defun weblogger-save-entry (&optional publishp arg)
  "Publish the current entry is publishp is set.  With optional
argument, prompts for the weblog to use."
  (interactive)
  (if (not (equal (current-buffer) *weblogger-entry*))
      (message
       "You are not in the *weblogger-entry* buffer.")
    (let ((entry (weblogger-entry-buffer-to-struct)))
      (cond ((and (buffer-modified-p)
		  (not (string-equal (cdr (assoc "content" entry)) "")))
	     (weblogger-server-username arg)
	     (weblogger-server-password arg)
	     (weblogger-weblog-id arg)
	     (cond ((cdr (assoc "entry-id" entry))
		    (weblogger-update-ring entry)
		    (weblogger-api-send-edits entry publishp)
		    (set-buffer-modified-p nil))
		   (t
		    (weblogger-entry-setup-headers
		     (weblogger-api-new-entry entry publishp)))))
	    (t (message "Nothing to post."))))))

(defun weblogger-update-ring (entry)
  "Update the entry ring with the contents of ENTRY"
  (let ((ring-entry (ring-ref
		     weblogger-entry-ring
		     weblogger-ring-index)))
    (mapcar (lambda (el)
	      (let ((field (assoc (car el) ring-entry)))
		(when field
		  (setcdr field (cdr el)))))
	    entry)))

(defun weblogger-server-username (&optional prompt)
  "Get the username.  If you've not yet logged in then prompt for
it."
  (if (or prompt
          (not weblogger-server-username)
          (not (stringp weblogger-server-username)))
      (let ((auth-user
             (when (fboundp 'auth-source-user-or-password)
               (auth-source-user-or-password
                "login" (url-host (url-generic-parse-url
                                   weblogger-server-url))
                "http")))
            (config-user (nth 1 (cdr (assoc weblogger-config-name
                                            weblogger-config-alist)))))
        (setq weblogger-server-username
              (cond (auth-user auth-user)
                    (config-user config-user)
                    (t (if (and prompt weblogger-server-username)
                      (read-from-minibuffer "Username: "
                                            weblogger-server-username)
                    (read-from-minibuffer "Username: "))))))
    weblogger-server-username))

(defun weblogger-server-url ()
  "Get the server url of the current configuration."
  (if (and weblogger-config-alist
	   weblogger-config-name)
      (setq weblogger-server-url
	    (nth 1 (assoc weblogger-config-name weblogger-config-alist)))
    weblogger-server-url))

(defun weblogger-server-password (&optional prompt)
  "Get the password.  If you've not yet logged in then prompt for
it"
  (when (not (stringp weblogger-server-password))
    (setq weblogger-server-password ""))
  (if (or prompt (string= weblogger-server-password ""))
      (let ((auth-pass
             (when (fboundp 'auth-source-user-or-password)
               (auth-source-user-or-password
                "password" (url-host (url-generic-parse-url
                                      weblogger-server-url))
                "http")))
             (get-pass (nth 2 (cdr (assoc weblogger-config-name
                                          weblogger-config-alist)))))
        (setq weblogger-server-password
	      (cond (auth-pass auth-pass)
		    (get-pass get-pass)
		    (t (read-passwd "Password for weblog server: ")))))
    weblogger-server-password))

(defun weblogger-weblog-id (&optional prompt)
  "Get the weblog ID."
  (setq weblogger-weblog-id
	(progn (when (and
		      (assoc weblogger-config-name weblogger-config-alist)
		      (not weblogger-weblog-id))
		 (weblogger-select-configuration weblogger-config-name))
	       (if (or prompt
		       (not weblogger-weblog-id))
		   (weblogger-select-weblog prompt)
		 weblogger-weblog-id))))

(defun weblogger-select-weblog (&optional fetch)
  "Allows the user to select a weblog and returns the weblog ID.
If there is only one weblog owned by the user on the server, then
that weblog is returned.  With FETCH defined, the server is
re-queried for a list of weblogs the user owns"
  (weblogger-weblog-id-from-weblog-name
   (let* ((completion-ignore-case t)
	  (seq 0)
	  (webloglist (mapcar
                       (lambda (weblog)
                         (cons weblog (setq seq (1+ seq))))
                       (weblogger-list-weblog-names fetch))))
     (if (= 1 (length webloglist))
	 (caar webloglist)
       (completing-read
	"Weblog: " webloglist nil t)))))

(defun weblogger-weblog-id-from-weblog-name (name)
  "Returns the weblog id given the name."
  (cdr (assoc name
              (mapcar
               (lambda (weblog)
                 (cons (cdr (assoc "blogName" weblog))
                       (cdr (assoc "blogid" weblog))))
               (weblogger-api-blogger-weblog-alist)))))

(defun weblogger-weblog-name-from-id (id)
  "Returns the weblog name given the id."
  (cdr (assoc id
              (mapcar
               (lambda (weblog)
                 (cons (cdr (assoc "blogid" weblog))
                       (cdr (assoc "blogName" weblog))))
               (weblogger-api-blogger-weblog-alist)))))

(defun weblogger-texttype-name-from-id (id)
  "Returns the texttype name given the id."
  (cdr (assoc id
              (mapcar
               (lambda (texttype)
                 (cons (cdr (assoc "key" texttype))
                       (cdr (assoc "label" texttype))))
               (weblogger-texttype-alist)))))

(defun weblogger-texttype-id-from-name (name)
  "Returns the texttype id given the name."
  (cdr (assoc name
              (mapcar
               (lambda (texttype)
                 (cons (cdr (assoc "label" texttype))
                       (cdr (assoc "key" texttype))))
               (weblogger-texttype-alist)))))

(defun weblogger-list-texttype-names (&optional fetch)
  "Returns a list of texttype names."
  (mapcar
   (lambda (texttype)
     (cdr (assoc "label" texttype)))
   (weblogger-texttype-alist fetch)))

(defun weblogger-texttype-alist (&optional fetch)
  "Returns the alist of texttypes allowed by the server."
  (when (cdr (assoc "mt.supportedTextFilters" weblogger-capabilities))
    (when (or fetch (not weblogger-texttype-alist))
      (setq weblogger-texttype-alist
	    (xml-rpc-method-call
	     weblogger-server-url
	     'mt.supportedTextFilters)))
    weblogger-texttype-alist))

(defun weblogger-select-texttype (&optional fetch)
  "Allows the user to select a texttype for entries."
  (weblogger-texttype-id-from-name
   (let* ((completion-ignore-case t)
	  (seq 0)
	  (ttlist (mapcar
		   (lambda (texttype)
		     (cons texttype (setq seq (1+ seq))))
		   (weblogger-list-texttype-names fetch))))
     (if (= 1 (length ttlist))
	 (caar ttlist)
       (completing-read
	"TextType: " ttlist nil t)))))

(defun weblogger-server-url-from-id (id)
  "Returns the weblog URL given the id."
  (cdr (assoc id
	      (mapcar
	       (lambda (weblog)
		 (cons (cdr (assoc "blogid" weblog))
		       (cdr (assoc "url" weblog))))
	       (weblogger-api-blogger-weblog-alist)))))

(defun weblogger-list-weblog-names (&optional fetch)
  "Returns a list of weblog names."
  (mapcar
   (lambda (blog)
     (cdr (assoc "blogName" blog)))
   (weblogger-api-blogger-weblog-alist fetch)))

(defun weblogger-ping-weblogs (&optional id)
  "Ping the weblog aggregators listed in weblogger-ping-urls."
  (mapcar
   (lambda (url)
     (xml-rpc-method-call-async
      'weblogger-handle-weblog-ping-response
      url
      'weblogUpdates.ping
      (weblogger-weblog-name-from-id
       (or id weblogger-weblog-id)				)
      (weblogger-server-url-from-id
       (or id weblogger-weblog-id))))
   weblogger-ping-urls))

(defun weblogger-handle-weblog-ping-response (&optional resp)
  "Handle the response from a weblog ping.  Print a entry with the result.

For old w3.el, resp is expected.  Otherwise current-buffer is expected to
contain the http result."
  (if resp
      (message (cdr (assoc "message" (cdr resp))))
    (message
     (cdr
      (assoc "message"
             (cdr
              (xml-rpc-xml-to-response
               (xml-rpc-request-process-buffer (current-buffer)))))))))

(defun weblogger-goto-entry (num &optional relativep)
  "Move to the entry identified by NUM in the ring.  If RELATIVE
is set, then add it to the current index and go to that entry."
  (if (buffer-modified-p)
      (weblogger-save-entry nil nil))
  (unless weblogger-entry-list
    (weblogger-api-list-entries weblogger-max-entries-in-ring))
  (let ((entry-id (if relativep
                      (+ (if weblogger-ring-index weblogger-ring-index
                           -1)
                         num)
                    num)))
    (setq weblogger-ring-index entry-id))
  (if (ring-empty-p weblogger-entry-ring)
      (weblogger-api-list-entries weblogger-max-entries-in-ring))
  (weblogger-edit-entry
   (ring-ref weblogger-entry-ring weblogger-ring-index)))

(defun weblogger-next-entry ()
  "Edit the contents of the next entry."
  (interactive)
  (weblogger-goto-entry -1 t))

(defun weblogger-prev-entry ()
  "Edit the contents of the previous entry."
  (interactive)
  (weblogger-goto-entry +1 t))

(defun weblogger-delete-entry ()
  "Delete the entry."
  (interactive)
  (unless weblogger-ring-index
    (message "You must have an entry loaded first."))
  (when (y-or-n-p "Do you really want to delete this entry? ")
    (let* ((msgid (cdr
                   (assoc "entry-id"
			    (ring-ref weblogger-entry-ring
				      weblogger-ring-index)))))
      (funcall weblogger-api-delete-entry msgid)
      (ring-remove weblogger-entry-ring weblogger-ring-index)
      (weblogger-edit-entry
       (ring-ref weblogger-entry-ring weblogger-ring-index)))))

(defun weblogger-api-new-entry (struct publishp)
  "Publish a new entry (STRUCT) using the best method available."
  (run-hooks 'weblogger-new-entry-hook)
  (unless weblogger-api-new-entry
    (weblogger-determine-capabilities))
  (ring-insert
   weblogger-entry-ring
   (add-to-list
    'struct
    (cons "entry-id" (funcall weblogger-api-new-entry struct publishp))))
  (setq weblogger-ring-index 0)
  (ring-ref weblogger-entry-ring weblogger-ring-index))

(defun weblogger-api-send-edits (struct publishp)
  "Update an entry (in STRUCT) using the best method available."
  (run-hooks 'weblogger-edit-entry-hook)
  (unless weblogger-api-send-edits
    (weblogger-determine-capabilities))
  (funcall weblogger-api-send-edits struct publishp))

(defun weblogger-api-list-entries (&optional count)
  "Get a list of entries."
  (unless weblogger-api-list-entries
    (weblogger-determine-capabilities))
  (funcall weblogger-api-list-entries count))

(defun weblogger-api-list-categories ()
  "Get a list of categories."
  (unless weblogger-api-list-categories
    (weblogger-determine-capabilities))
  (funcall weblogger-api-list-categories))

(defun weblogger-api-meta-list-categories ()
  "Return a list of entries that the weblog server has."
  (setq weblogger-category-list
	(mapcar
	 (lambda (category)
	   (ring-insert-at-beginning
            weblogger-category-ring (cdr (assoc "categoryName"
                                                category))))
	 (xml-rpc-method-call
	  (weblogger-server-url)
	  'metaWeblog.getCategories
	  (weblogger-weblog-id)
	  (weblogger-server-username)
	  (weblogger-server-password)
	  ))))


(defun weblogger-api-meta-list-entries (&optional count)
  "Return a list of entries that the weblog server has.  COUNT specifies
how many of the most recent entries to get.  If COUNT is not
specified, then the default is weblogger-max-entries-in-ring."
  (setq weblogger-entry-list
	(mapcar
	 (lambda (entry)
	   (ring-insert-at-beginning
            weblogger-entry-ring
            (weblogger-response-to-struct entry)))
	 (xml-rpc-method-call
	  (weblogger-server-url)
	  'metaWeblog.getRecentPosts
	  (weblogger-weblog-id)
	  (weblogger-server-username)
	  (weblogger-server-password)
	  (or count weblogger-max-entries-in-ring)))))

(defun weblogger-api-meta-send-edits (struct &optional publishp)
  "MetaWeblog API method to post edits to a entry specified by
STRUCT.  If PUBLISHP is non-nil, publishes the entry as well."
  (xml-rpc-method-call
   (weblogger-server-url)
   'metaWeblog.editPost
   (cdr (assoc "entry-id" struct))
   (weblogger-server-username)
   (weblogger-server-password)
   (weblogger-struct-to-request struct)
   publishp))

(defun weblogger-api-meta-new-entry (struct publishp)
  "Post a new entry (STRUCT).  If PUBLISHP is non-nil, publishes
the entry as well."
  (xml-rpc-method-call
   (weblogger-server-url)
   'metaWeblog.newPost
   (weblogger-weblog-id)
   (weblogger-server-username)
   (weblogger-server-password)
   (weblogger-struct-to-request struct)
   publishp))

(defun weblogger-api-blogger-edit-template (type)
  "Edit a Template. TYPE indicates which one."
  (switch-to-buffer "*weblogger-template*")
  (weblogger-template-mode)
  (erase-buffer)
  (insert (xml-rpc-method-call
	   (weblogger-server-url)
	   'blogger.getTemplate
	   weblogger-blogger-app-key
	   (weblogger-weblog-id)
	   (weblogger-server-username)
	   (weblogger-server-password)
	   type))
  (set-buffer-modified-p nil)
  (goto-char (point-min))
  (setq weblogger-template-type type))

(defun weblogger-api-blogger-save-template ()
  "Save a Template. TYPE indicates which one."
  (interactive)
  (if (buffer-modified-p)
      (progn (xml-rpc-method-call
	      (weblogger-server-url)
	      'blogger.setTemplate
	      weblogger-blogger-app-key
	      (weblogger-weblog-id)
	      (weblogger-server-username)
	      (weblogger-server-password)
	      (buffer-substring-no-properties (point-min) (point-max))
	      weblogger-template-type)
	     (set-buffer-modified-p nil))))

(defun weblogger-api-blogger-weblog-alist (&optional fetch)
  "Returns the alist of weblogs owned by a user on the server."
  (setq weblogger-weblog-alist
	(if (or fetch (not weblogger-weblog-alist))
	    (xml-rpc-method-call
	     (weblogger-server-url)
	     'blogger.getUsersBlogs
	     weblogger-blogger-app-key
	     (weblogger-server-username)
	     (weblogger-server-password))
	  weblogger-weblog-alist)))

(defun weblogger-api-blogger-new-entry (struct publishp)
  "Post a new entry from STRUCT.  If PUBLISHP is non-nil, publishes the
entry as well."
  (xml-rpc-method-call
   (weblogger-server-url)
   'blogger.newPost
   weblogger-blogger-app-key
   (weblogger-weblog-id)
   (weblogger-server-username)
   (weblogger-server-password)
   (weblogger-api-blogger-get-content struct)
   publishp))

(defun weblogger-api-blogger-get-content (struct)
  "Return the content for this post, optionally inserting the
title in the first row if weblogger-blogger-firstline-title is
set."
  (if weblogger-blogger-firstline-title
      (concat "<title>"
	      (cdr (assoc "title" struct))
	      "</title>\n"
	      (cdr (assoc "content" struct)))
    (cdr (assoc "content" struct))))

(defun weblogger-api-blogger-send-edits (struct &optional publishp)
  "Blogger API method to post edits to an entry specified by
STRUCT.  If PUBLISHP is non-nil, publishes the entry as well."
  (xml-rpc-method-call
   (weblogger-server-url)
   'blogger.editPost
   weblogger-blogger-app-key
   (cdr (assoc "entry-id" struct))
   (weblogger-server-username)
   (weblogger-server-password)
   (weblogger-api-blogger-get-content struct)
   publishp))

(defun weblogger-api-blogger-list-categories ()
  "Return a list of categories that the weblog server has. (Not
supported yet)"
  (setq weblogger-category-list nil))

(defun weblogger-api-blogger-list-entries (&optional count)
  "Return a list of entries that the weblog server has.  COUNT specifies
how many of the most recent entries to get.  If COUNT is not
specified, then the default is weblogger-max-entries-in-ring."
  (setq weblogger-entry-list
	(mapcar
	 (lambda (entry)
	   (ring-insert-at-beginning weblogger-entry-ring
				     (weblogger-response-to-struct entry)))
	 (xml-rpc-method-call
	  (weblogger-server-url)
	  'blogger.getRecentPosts
	  weblogger-blogger-app-key
	  (weblogger-weblog-id)
	  (weblogger-server-username)
	  (weblogger-server-password)
	  (or count weblogger-max-entries-in-ring)))))

(defun weblogger-api-blogger-delete-entry (msgid)
  (xml-rpc-method-call
   (weblogger-server-url)
   'blogger.deletePost
   weblogger-blogger-app-key
   msgid
   (weblogger-server-username)
   (weblogger-server-password)
   t))

(defun weblogger-edit-entry (&optional entry)
  "Edit a entry.  If ENTRY is specified, then use that entry.
Otherwise, open a new entry."
  (setq *weblogger-entry* (switch-to-buffer "*weblogger-entry*"))
  (setq buffer-read-only nil)
  (weblogger-entry-mode)
  (erase-buffer)
  (weblogger-entry-setup-headers entry t)
  (if (and entry (cdr (assoc "content" entry)))
      (insert (cdr (assoc "content" entry))))
  (message-fetch-field "Keywords")
  (message-goto-keywords) ;; Create Keywords field in new entries
  (set-buffer-modified-p nil)
  (run-hooks 'weblogger-start-edit-entry-hook) ; Force hooks to clear
                                               ; the modified flag
                                               ; themselves if they
                                               ; want to.
  (if (message-fetch-field "Subject")
      (message-goto-body) ;; If Subject exists, move cursor to message
                          ;; body
    (message-goto-subject)) ;; Else, drop cursor on Subject header
  (pop-to-buffer *weblogger-entry*))

(unless (fboundp 'assoc-string)
  (defun assoc-string (key list &optional fold)
    (assoc-ignore-case key list)))

(defun weblogger-response-to-struct (response)
  "Convert the result of the xml-rpc call to a structure we
like."
  (let ((postid      (cdr (assoc-string "postid" response t)))
	(authorName  (cdr (assoc-string "authorname" response t)))
	(userid      (cdr (assoc-string "userid" response t)))
	(title       (cdr (assoc-string "title" response t)))
	(dateCreated (cdr (assoc-string "datecreated" response t)))
	(content          (assoc-string "content" response))
	(trackbacks  (cdr (assoc-string "mt_tb_ping_urls" response t)))
	(textType
         (cdr (assoc-string "mt_convert_breaks" response t)))
	(url         (cdr (assoc-string "link" response t)))
	(description      (assoc-string "description" response t))
	(extended         (assoc-string "mt_text_more" response t))
	(tags        (cdr (assoc-string "mt_tags" response t)))
        (categories  (cdr (assoc-string "categories" response t))))

    (cond (content
	   (delq nil (list
		      (when postid
			(cons "entry-id"     postid))
		      (if title
			  (cons "title"        title)
			;; See if we can extract the title from the
			;; first line of the message body if it wasn't
			;; in a header.
			(when (and
                               weblogger-blogger-firstline-title
                               (string-match "^<title>\\(.*\\)</title>.*\n"
                                             (cdr content)))
			  (setq title (match-string 1 (cdr content)))
			  (setcdr content
				  (with-temp-buffer
				    (insert (cdr content))
				    (goto-char (point-min))
                                    (while (and (not (string=
						      "" (match-string
							  0 (cdr content))))
                                                (search-forward
						 (match-string
						  0 (cdr content)) nil t))
                                      (replace-match "" nil t))
				    (buffer-string)))
			  (cons "title" title)))
		      (when authorName
			(cons "authorName"   authorName))
		      (when userid
			(cons "userid"       userid))
		      (when dateCreated
			(cons "dateCreated"  dateCreated))
		      (when content
			(cons "content"      (cdr content))))))
	  (description
	   (delq nil (list
		      (when authorName
			(cons "authorName"   authorName))
		      (when postid
			(cons "entry-id"     postid))
		      (when trackbacks
			(cons "trackbacks"   trackbacks))
		      (when description
			(cond ((cdr extended)
                               (cons "content"   (concat (cdr description)
                                                         "<!--more-->"
                                                         (cdr extended))))
                              (t
                               (cons "content" (cdr description)))))
		      (when title
			(cons "title"        title))
		      (when url
			(cons "url"          url))
		      (when dateCreated
			(cons "dateCreated"  dateCreated))
		      (when tags
			(cons "tags"   tags))
		      (when categories
			(cons "categories"   categories))
		      (when textType
			(cons "texttype"     textType)))))
	  (t
	   (error "bogosity!")))))

(defun weblogger-struct-to-request (entry)
  "Convert the struct to something that can be used in an xml-rpc
request."
  (delq nil
	(list
	 (assoc "title"        entry)
	 (assoc "authorName"   entry)
	 (assoc "userid"       entry)
         (assoc "dateCreated" entry)
         (when (cdr (assoc "trackbacks"  entry))
           (cons "mt_tb_ping_urls" (cdr (assoc "trackbacks"  entry))))
         (when (cdr (assoc "texttype" entry))
           (cons "mt_convert_breaks" (weblogger-texttype-id-from-name
                                      (cdr (assoc "texttype" entry)))))
         (when (cdr (assoc "url" entry))
           (cons "link" (cdr (assoc "url" entry))))
         (when (cdr (assoc "content" entry))
           (cons "description" (cdr (assoc "content" entry))))
         (when (cdr (assoc "tags" entry))
           (cons "mt_tags" (cdr (assoc "tags" entry))))
         (when (cdr (assoc "categories" entry))
           (cons "categories" (cdr (assoc "categories" entry)))))))

(defun weblogger-server-userid ()
  "Get information on user."
  (or weblogger-server-userid
      (setq weblogger-server-userid
	    (cdr
	     (assoc "userid"
		    (xml-rpc-method-call
		     (weblogger-server-url)
		     'blogger.getUserInfo
		     weblogger-blogger-app-key
		     (weblogger-server-username)
		     (weblogger-server-password)))))))

;;;###autoload
(defun weblogger-fetch-entries ()
  "Sync the entry ring with what is on the weblog server."
  (interactive)
  (setq weblogger-entry-ring (make-ring weblogger-max-entries-in-ring))
  (setq weblogger-category-ring (make-ring 20))
  (weblogger-api-list-categories)
  (weblogger-api-list-entries weblogger-max-entries-in-ring)
  (setq weblogger-ring-index 0))

(defun weblogger-determine-capabilities ()
  "Determine the capabilities of the remote weblog server."
  (setq weblogger-capabilities (copy-alist weblogger-no-capabilities))
  (let ((has-meta-api t)
	(has-mt-api t)
	(has-blogger-api t))
    (condition-case nil
	(progn (mapc
		(lambda (method)
		  (and (assoc method weblogger-capabilities)
		       (setcdr (assoc method weblogger-capabilities) t)))
		(xml-rpc-method-call
		 (weblogger-server-url)
		 'mt.supportedMethods)))
      (error (setq has-mt-api nil))))
  (cond ((cdr (assoc "metaWeblog.editPost" weblogger-capabilities))
	 (setq weblogger-api-send-edits 'weblogger-api-meta-send-edits))
	(t
	 (setq weblogger-api-send-edits
               'weblogger-api-blogger-send-edits)))
  (cond ((cdr (assoc "metaWeblog.newPost" weblogger-capabilities))
	 (setq weblogger-api-new-entry 'weblogger-api-meta-new-entry))
	(t
	 (setq weblogger-api-new-entry 'weblogger-api-blogger-new-entry)))
  (cond ((cdr (assoc "metaWeblog.getCategories" weblogger-capabilities))
	 (setq weblogger-api-list-categories
               'weblogger-api-meta-list-categories))
	(t
	 (setq weblogger-api-list-categories
               'weblogger-api-blogger-list-categories)))
  (cond ((cdr (assoc "metaWeblog.getRecentPosts"
                     weblogger-capabilities))
	 (setq weblogger-api-list-entries
               'weblogger-api-meta-list-entries))
	(t
	 (setq weblogger-api-list-entries
               'weblogger-api-blogger-list-entries))))

(defun weblogger-entry-buffer-to-struct (&optional encode buffer)
  "Convert an entry BUFFER to a struct (which is then used
internally).  If BUFFER is not given, use the current buffer."
  (unless buffer
    (setq buffer (current-buffer)))
  (save-excursion
    (run-hooks weblogger-pre-struct-hook)
    (set-buffer buffer)
    (delq nil
	  (list
	   (cons "authorName"   (message-fetch-field "From"))
	   (cons "dateCreated"
                 (list :datetime (date-to-time
                                  (message-fetch-field "Date"))))
	   (cons "texttype"      (message-fetch-field "X-TextType"))
	   (cons "url"           (message-fetch-field "X-Url"))
	   (cons "title"     (or (message-fetch-field "Subject")
				 weblogger-default-title))
	   (cons "tags" (message-fetch-field "Keywords"))
	   (when (message-fetch-field "In-Reply-To")
             (cons "trackbacks"
                   (or (message-tokenize-header
                        (message-fetch-field "In-Reply-To") ", ")
                       weblogger-default-categories)))
	   (when (and weblogger-ring-index
                      (> (ring-length weblogger-entry-ring) 0))
             (cons "entry-id"
                   (let ((msgid (message-fetch-field "Message-ID")))
                     (if (and msgid (string-match "<\\([0-9]+\\)/" msgid))
                         (match-string 1 msgid)
                       (cdr (assoc "entry-id"
                                   (ring-ref
                                    weblogger-entry-ring
                                    weblogger-ring-index)))))))
	   (cons "content"
		 (progn
		   (message-goto-body)
		   (if encode
		       (url-insert-entities-in-string
			(buffer-substring-no-properties
                         (point) (point-max)))
                     (buffer-substring-no-properties
                      (point) (point-max)))))))))

(defun weblogger-toggle-edit-body ()
  "Toggle between editing the body and editing the headers"
  (interactive)
  (if (string= mode-name "Weblog")
      (progn
        (message-goto-body)
        (setq weblogger-header (buffer-substring (point-min) (point)))
        (delete-region (point-min) (point))
        (run-hooks 'weblogger-edit-mode-toggle-hook)
        (funcall weblogger-edit-mode)
        (make-local-variable 'weblogger-header))
    (if (not (assoc 'weblogger-header (buffer-local-variables)))
        (error "You didn't come here from a weblogger buffer, so we can switch back")
      (goto-char (point-min))
      (run-hooks 'weblogger-weblogger-mode-toggle-hook)
      (goto-char (point-min))
      (insert weblogger-header)
      (weblogger-entry-mode))))

;; TODO -- Support for toolbar
;; (eval-when-compile (defvar tool-bar-map))
;; (if (featurep 'xemacs)
;;     nil					; no XEmacs support just yet.
;;   (when (and (fboundp 'tool-bar-add-item-from-menu)
;;  	     tool-bar-mode)
;;     (defvar weblogger-tool-bar-map
;;       (let ((tool-bar-map (copy-keymap tool-bar-map)))
;;  	;; Zap some items which aren't so relevant and take up space.
;;  	(dolist (key '(print-buffer kill-buffer save-buffer write-file
;;  				    dired open-file))
;;  	  (define-key tool-bar-map (vector key) nil))

;;  	(tool-bar-add-item-from-menu
;;  	 'message-send-and-exit "mail_send" message-mode-map)
;;  	(tool-bar-add-item-from-menu
;;  	 'message-kill-buffer "close" message-mode-map)
;;  	(tool-bar-add-item-from-menu
;;  	 'message-dont-send "cancel" message-mode-map)
;;  	(tool-bar-add-item-from-menu
;;  	 'mml-attach-file "attach" message-mode-map)
;;  	(tool-bar-add-item-from-menu
;;  	 'ispell-message "spell" message-mode-map)
;;  	tool-bar-map))))

(unless (and (fboundp 'widgetp)
	     (widgetp 'alist))
  (define-widget 'alist 'list
    "An association list."
    :key-type '(sexp :tag "Key")
    :value-type '(sexp :tag "Value")
    :convert-widget 'widget-alist-convert-widget
    :tag "Alist")

  (defvar widget-alist-value-type)	;Dynamic variable

  (defun widget-alist-convert-widget (widget)
    ;; Handle `:options'.
    (let* ((options (widget-get widget :options))
	   (widget-alist-value-type (widget-get widget :value-type))
	   (other `(editable-list :inline t
				  (cons :format "%v"
					,(widget-get widget :key-type)
					,widget-alist-value-type)))
	   (args (if options
		     (list `(checklist :inline t
				       :greedy t
				       ,@(mapcar 'widget-alist-convert-option
						 options))
			   other)
		   (list other))))
      (widget-put widget :args args)
      widget))

  (defun widget-alist-convert-option (option)
    ;; Convert a single alist option.
    (let (key-type value-type)
      (if (listp option)
	  (let ((key (nth 0 option)))
	    (setq value-type (nth 1 option))
	    (if (listp key)
		(setq key-type key)
	      (setq key-type `(const ,key))))
	(setq key-type `(const ,option)
	      value-type widget-alist-value-type))
      `(cons :format "Key: %v" ,key-type ,value-type))))

(provide 'weblogger)

;; Local Variables:
;; time-stamp-pattern: "20/^;; Last Modified: <%%>$"
;; End:

;;; weblogger.el ends here
