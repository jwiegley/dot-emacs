;;; yaoddmuse.el --- Yet another oddmuse for Emacs

;; Filename: yaoddmuse.el
;; Description: Yet another oddmuse for Emacs
;; Author: Andy Stewart lazycat.manatee@gmail.com
;; Maintainer: Andy Stewart lazycat.manatee@gmail.com
;; Copyright (C) 2009, Andy Stewart, all rights reserved.
;; Copyright (C) 2009, 2010 rubikitch, all rights reserved.
;; Created: 2009-01-06 12:41:17
;; Version: 0.1.1
;; Last-Updated: 2010/03/20 20:53
;;           By: rubikitch
;; URL: http://www.emacswiki.org/emacs/download/yaoddmuse.el
;; Keywords: yaoddmuse, oddmuse
;; Compatibility: GNU Emacs 22 ~ 23
;;
;; Features that might be required by this library:
;;
;; `url' `cl' `sgml-mode' `skeleton'
;;

;;; This file is NOT part of GNU Emacs

;;; License
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.

;;; Commentary:
;;
;; Yet another oddmuse for Emacs.
;;
;; This mode can edit or post wiki page *asynchronous*.
;; So it can't hang your emacs.
;; You can do your work when get or post wiki page.
;;
;; Below are the command you can use:
;;
;; * Edit:
;;      `yaoddmuse-edit'                     edit wiki page.
;;      `yaoddmuse-edit-default'             edit default wiki page.
;;      `yaoddmuse-follow'                   figure out what page we need to visit
;; * Post:
;;      `yaoddmuse-post-buffer'              post buffer to wiki.
;;      `yaoddmuse-post-current-buffer'      post current buffer to wiki
;;      `yaoddmuse-post-file'                post file to wiki.
;;      `yaoddmuse-post-file-default'        post file to default wiki.
;;      `yaoddmuse-post-library'             post library to wiki.
;;      `yaoddmuse-post-library-default'     post library to default wiki.
;;      `yaoddmuse-post-dired'               post dired marked files to wiki.
;;      `yaoddmuse-post-dired-default'       post dired marked files to wiki.
;;      `yaoddmuse-post-screenshot'          post screenshot to wiki.
;;      `yaoddmuse-post-screenshot-default'  post screenshot to default wiki.
;; * View:
;;      `yaoddmuse-revert'                   reload current wiki page.
;;      `yaoddmuse-browse-page'              browse wiki page.
;;      `yaoddmuse-browse-page-default'      browse default wiki page.
;;      `yaoddmuse-browse-page-diff'         browse wiki page diff.
;;      `yaoddmuse-browse-page-default-diff' browse default wiki page diff.
;;      `yaoddmuse-browse-current-page'      browse current wiki page.
;; * Navigation:
;;      `yaoddmuse-navi-next-heading'        jump next heading.
;;      `yaoddmuse-navi-prev-heading'        jump previous heading.
;; * Update:
;;      `yaoddmuse-update-pagename'          will update Wiki page name.
;; * Insert:
;;      `yaoddmuse-insert-pagename'          insert wiki page name.
;;      `yaoddmuse-insert-file-content'      insert file content.
;; * Misc:
;;      `yaoddmuse-kill-url'                 kill current wiki page url in yank.
;;      `yaoddmuse-toggle-minor'             toggle minor mode state.
;;      `yaoddmuse-redirect'                 redirect page.
;;      `yaoddmuse-delete'                   delete page.
;;      `yaoddmuse-toggle-image-status'      toggle image status.
;;      `yaoddmuse-save-as'                  save special page.
;;
;; Tips:
;; ・ Get page around point:
;;      Command ‘yaoddmuse-follow’ try to get valid page link around point.
;;      If it find, edit this page, otherwise show “No link found at point.”
;;      And you can type “C-u” before call this command,
;;      then it will give you page name completing for edit.
;; ・ Reload or switch edit page:
;;      When you use command ‘yaoddmuse-edit’ or ‘yaoddmuse-edit-default’,
;;      it will prefer to switch edit page if already have one exist.
;;      If you want to reload edit page forcibly, just hit “C-u” before
;;      execute command.
;; ・ Smart display edit page.
;;      Default, edit page buffer popup when current major-mode
;;      is not ‘yaoddmuse-mode’, or use switch edit page buffer
;;      when current major-mode is ‘yaoddmuse-mode’.
;; ・ Revert edit page:
;;      Command ‘yaoddmuse-revert’ revert current edit page and don’t
;;      need input wiki name or page name.
;; ・ Browse page after post successful:
;;      If you type “C-u” before call post command,
;;      will browse page after post successful.
;; ・ Post buffer to wiki:
;;      Command ‘yaoddmuse-post-buffer’ post special buffer to wiki,
;;      or use command ‘yaoddmuse-post-current-buffer’ post current buffer to wiki.
;; ・ Post file to wiki:
;;      Command ‘yaoddmuse-post-file’ post special file to wiki,
;;      it’s useful to fast posting when you don’t want open file.
;; ・ Post mark files in dired to wiki:
;;      Command ‘yaoddmuse-post-dired’ post mark files in dired to wiki,
;;      this command is useful when update many files to wiki.
;; ・ Post library to wiki:
;;      Command ‘yaoddmuse-post-library’ and ‘yaoddmuse-post-library-default’
;;      will post special library to wiki, and not need input file path,
;;      it’s so lazy! ;)
;; ・ Remember last summary:
;;      By default, yaoddmuse remember last `summary' string, if you input
;;      same `summary' as previous time, just hit RET.
;; ・ Pick up file name:
;;      By default, when you use command `yaoddmuse-post-library' and
;;      `yaoddmuse-post-library-default', those commands can pick up
;;      file name around point, if it's library name you want, just
;;      hit RET.  ;)
;; ・ Pick up page name:
;;      When you use commands `yaoddmuse-browse-page' or `yaoddmuse-browse-page-default',
;;      it will try to pick-up page name around point.
;; ・ Encode special file:
;;      If you post special file, such as picture or compress file,
;;      it can encode file content before post it.
;; ・ Redirect page:
;;      You can use command `yaoddmuse-redirect' redirect page.
;;      Just input page name that you want redirect to.
;;      You need input redirect from page if current buffer not
;;      `yaoddmuse' buffer.
;; ・ Delete page:
;;      You can use command `yaoddmuse-delete' delete page.
;;      Just input page name that you want delete.
;; ・ Insert special file:
;;      You can use command `yaoddmuse-insert-file-content' insert
;;      file content.
;;      This command will try to encode special file content, such as,
;;      picture or compress file.
;; ・ Save page:
;;      You can use command `yaoddmuse-save-as' save special page,
;;      such as picture or compress format, and it will notify you
;;      correct suffix to save.
;; ・ Toggle image view:
;;      By default, when got image page, it will decode image and view it.
;;      You can use command `yaoddmuse-toggle-image-status' to toggle
;;      image status for view different content.
;;

;;; Commands:
;;
;; Below are complete command list:
;;
;;  `yaoddmuse-mode'
;;    Yet another mode to edit Oddmuse wiki pages.
;;  `yaoddmuse-edit'
;;    Edit a page on a wiki.
;;  `yaoddmuse-edit-default'
;;    Edit a page with default wiki `yaoddmuse-default-wiki'.
;;  `yaoddmuse-follow'
;;    Figure out what page we need to visit and call `yaoddmuse-edit' on it.
;;  `yaoddmuse-post-buffer'
;;    Post the BUFFER to the current wiki.
;;  `yaoddmuse-post-current-buffer'
;;    Post current buffer to current wiki.
;;  `yaoddmuse-post-file'
;;    Post file to current wiki.
;;  `yaoddmuse-post-file-default'
;;    Post file to default wiki.
;;  `yaoddmuse-post-library'
;;    Post library to current wiki.
;;  `yaoddmuse-post-library-default'
;;    Post library to default wiki.
;;  `yaoddmuse-post-dired'
;;    Post dired marked files to current wiki.
;;  `yaoddmuse-post-dired-default'
;;    Post dired marked files to default wiki.
;;  `yaoddmuse-post-screenshot'
;;    Post screenshot to current wiki.
;;  `yaoddmuse-post-screenshot-default'
;;    Post screenshot to default wiki.
;;  `yaoddmuse-revert'
;;    Reload current edit page.
;;  `yaoddmuse-browse-page'
;;    Browse special page in wiki.
;;  `yaoddmuse-browse-page-default'
;;    Brose special page with `yaoddmuse-default-wiki'.
;;  `yaoddmuse-browse-page-diff'
;;    Browse special page diff in wiki.
;;  `yaoddmuse-browse-page-default-diff'
;;    Brose special page with `yaoddmuse-default-wiki'.
;;  `yaoddmuse-browse-current-page'
;;    Browse current page.
;;  `yaoddmuse-navi-next-heading'
;;    Goto next heading.
;;  `yaoddmuse-navi-prev-heading'
;;    Goto previous heading.
;;  `yaoddmuse-insert-pagename'
;;    Insert a PAGENAME of current wiki with completion.
;;  `yaoddmuse-insert-file-content'
;;    Insert FILE content.
;;  `yaoddmuse-kill-url'
;;    Make the URL of current oddmuse page the latest kill in the kill ring.
;;  `yaoddmuse-update-pagename'
;;    Update all page name match in `yaoddmuse-wikis'.
;;  `yaoddmuse-toggle-minor'
;;    Toggle minor mode state.
;;  `yaoddmuse-redirect'
;;    Redirect page.
;;  `yaoddmuse-delete'
;;    Delete page.
;;  `yaoddmuse-toggle-image-status'
;;    Toggle image status.
;;  `yaoddmuse-save-as'
;;    Save as file.
;;  `emacswiki'
;;    Edit a page on the EmacsWiki.
;;  `emacswiki-post'
;;    Post file to the EmacsWiki.
;;
;;; Customizable Options:
;;
;; Below are customizable option list:
;;
;;  `yaoddmuse-directory'
;;    Directory to storage oddmuse pages.
;;    default = "~/.yaoddmuse"
;;  `yaoddmuse-assoc-mode'
;;    Whether assoc files in `yaoddmuse-directory' with `yaoddmuse-mode'.
;;    default = t
;;  `yaoddmuse-wikis'
;;    Alist mapping wiki names to URLs.
;;    default = (quote (("TestWiki" "http://www.emacswiki.org/cgi-bin/test" utf-8 "uihnscuskc=1;") ("EmacsWiki" "http://www.emacswiki.org/cgi-bin/emacs" utf-8 "uihnscuskc=1;") ("CommunityWiki" "http://www.communitywiki.org/cw" utf-8 "uihnscuskc=1;") ("RatpoisonWiki" "http://ratpoison.antidesktop.net/cgi-bin/wiki" utf-8 "uihnscuskc=1;") ("StumpwmWiki" "http://stumpwm.antidesktop.net/cgi-bin/wiki" utf-8 "uihnscuskc=1;") ...))
;;  `yaoddmuse-default-wiki'
;;    The default wiki name for edit.
;;    default = "EmacsWiki"
;;  `yaoddmuse-username'
;;    Username to use when posting.
;;    default = user-full-name
;;  `yaoddmuse-password'
;;    Password to use when posting.
;;    default = ""
;;  `yaoddmuse-transform-image'
;;    Whether transform image content.
;;    default = t
;;  `yaoddmuse-display-after-get'
;;    Whether display `yaoddmuse-mode' buffer after GET.
;;    default = t
;;  `yaoddmuse-close-after-post'
;;    Whether close `yaoddmuse-mode' buffer after POST.
;;    default = nil
;;  `yaoddmuse-post-dired-confirm'
;;    Whether confirmation is needed to post mark dired files.
;;    default = t
;;  `yaoddmuse-edit-protect'
;;    This option is make user can post wiki page without text captcha.
;;    default = t
;;  `yaoddmuse-use-always-minor'
;;    When t, set all the minor mode bit to all editions.
;;    default = nil
;;  `yaoddmuse-browse-function'
;;    The browse function use in `yaoddmuse-handle-browse'.
;;    default = (quote browse-url)
;;  `yaoddmuse-notify-function'
;;    Notify function for getting and posting.
;;    default = (quote yaoddmuse-notify-default)
;;  `yaoddmuse-highlight-elisp-page'
;;    Whether use syntax highlight elisp page.
;;    default = t
;;  `yaoddmuse-screenshot-program'
;;    The default tool for screenshot.
;;    default = "import"
;;  `yaoddmuse-screenshot-filename'
;;    The default file for save screenshot.
;;    default = "/tmp/yaoddmuse-screenshot.png"

;;; Installation:
;;
;; Put yaoddmuse.el to your load-path.
;; The load-path is usually ~/elisp/.
;; It's set in your ~/.emacs like this:
;; (add-to-list 'load-path (expand-file-name "~/elisp"))
;;
;; And the following to your ~/.emacs startup file.
;;
;; (require 'yaoddmuse)
;;
;; If your computer is always connected Internet when Emacs start up,
;; I recommended you add below to your ~/.emacs, to update Wiki page name
;; when start up:
;;
;;      (yaoddmuse-update-pagename t)
;;
;; And above setup is not necessary, because Yaoddmuse will automatically
;; update Wiki page name when you first call yaoddmuse function.
;; Above setup just avoid *delay* when you first call function.
;;

;;; Customize:
;;
;; `yaoddmuse-directory' to storage oddmuse pages.
;;
;; `yaoddmuse-assoc-mode' Whether assoc files in
;; `yaoddmuse-directory' with `yaoddmuse-mode'.
;;
;; `yaoddmuse-wikis' is alist mapping wiki names to URLs.
;; You can add Oddmuse wiki element with format
;; ("WikiName" "WikiUrl" coding "CaptchaString").
;; But don't modified default elements of `yaoddmuse-wikis',
;; probably causes trouble!
;;
;; `yaoddmuse-default-wiki' the default wiki name for command
;; `yaoddmuse-edit-default'.
;;
;; `yaoddmuse-username' user name for posting, default is
;; this value of `user-full-name'.
;;
;; `yaoddmuse-password' password for posting,
;; You only need this if you want to edit locked pages and you
;; know an administrator password.
;;
;; `yaoddmuse-transform-image' Whether transform image content.
;; If non-nil, will transform image content and view it.
;; Otherwise, don't transform image content.
;;
;; `yaoddmuse-display-after-get' whether display page after get.
;;
;; `yaoddmuse-close-after-post' whether close edit buffer after
;; post wiki page.
;;
;; `yaoddmuse-post-dired-confirm' Whether confirmation is needed
;; to post mark dired files.
;;
;; `yaoddmuse-edit-protect' Some wikis, such as EmacsWiki,
;; use a text captcha to protect pages from being edited.
;; This option is make user can post wiki page without text captcha.
;; So if you edit wiki (such as EmacsWiki),
;; please make sure this option is `non-nil'.Default
;;
;; `yaoddmuse-use-always-minor' When t,
;; set all the minor mode bit to all editions.
;;
;; `yaoddmuse-browse-function' the browse function use
;; in `yaoddmuse-handle-browse',
;; you can customize your own advanced browse function.
;;
;; `yaoddmuse-notify-function' the notify function for
;; get/post message,
;; you can customize your own advanced notify function.
;;
;; `yaoddmuse-highlight-elisp-page'
;; Whether to render ‘emacs-lisp-mode’ syntax highlighting
;; when the current page is an elisp file.
;; If you don’t like this, change it to nil.
;;
;; `yaoddmuse-screenshot-program'
;; The default tool program for screenshot.
;;
;; `yaoddmuse-screenshot-filename'
;; The default file for save screenshot.
;;
;; All of the above can customize by:
;;      M-x customize-group RET yaoddmuse RET
;;


;;; Bug Report:
;;
;; If you have problem, send a bug report via M-x yaoddmuse-send-bug-report.
;; The step is:
;;  0) Setup mail in Emacs, the easiest way is:
;;       (setq user-mail-address "your@mail.address")
;;       (setq user-full-name "Your Full Name")
;;       (setq smtpmail-smtp-server "your.smtp.server.jp")
;;       (setq mail-user-agent 'message-user-agent)
;;       (setq message-send-mail-function 'message-smtpmail-send-it)
;;  1) Be sure to use the LATEST version of yaoddmuse.el.
;;  2) Enable debugger. M-x toggle-debug-on-error or (setq debug-on-error t)
;;  3) Use Lisp version instead of compiled one: (load "yaoddmuse.el")
;;  4) Do it!
;;  5) If you got an error, please do not close *Backtrace* buffer.
;;  6) M-x yaoddmuse-send-bug-report and M-x insert-buffer *Backtrace*
;;  7) Describe the bug using a precise recipe.
;;  8) Type C-c C-c to send.
;;  # If you are a Japanese, please write in Japanese:-)

;;; Change log:
;; 2010/05/04
;;      * Bug report command: `yaoddmuse-send-bug-report'
;;      
;; 2010/03/20
;;      * Add Emacswiki-specific commands for convenience:
;;        `emacswiki'
;;        `emacswiki-post'
;; 2010/02/24
;;      * Please don't use `C-x` key to avoid conflict with Default Emacs binding.
;;         If you need that, please customize `yaoddmuse-mode-map`, thanks!
;;
;; 2010/02/19
;;      * Add new key binding:  C-x C-v (`yaoddmuse-revert')
;;
;; 2009/10/08
;;      * imenu support.
;;
;; 2009/03/29
;;      * Add commands:
;;        `yaoddmuse-browse-page-diff'
;;        `yaoddmuse-browse-page-default-diff'
;;
;; 2009/03/13
;;      * Just ask summary once when post from dired.
;;
;; 2009/03/11
;;      * Refactory code.
;;      * Fix bugs.
;;      * Fix doc.
;;      * Handle retrieve failed case of `yaoddmuse-get-page'.
;;
;; 2009/03/08
;;      * Modified `yaoddmuse-wikis', make captcha string per wiki.
;;      * High edit status at mode-line.
;;      * Fix doc.
;;
;; 2009/03/04
;;      * Fix the bug of `yaoddmuse-post-callback'.
;;
;; 2009/03/02
;;      * Refactory code.
;;      * Add new commands:
;;        `yaoddmuse-post-screenshot'
;;        `yaoddmuse-post-screenshot-default'
;;
;; 2009/02/27
;;      * Improve `yaoddmuse-post'.
;;      * When execute commands
;;       `yaoddmuse-browse-page' or
;;       `yaoddmuse-browse-page-default', will try
;;       to use `yaoddmuse-pagename-at-point' pick-up
;;       page name from current buffer.
;;
;; 2009/02/24
;;      * Fix `yaoddmuse-mode' load bug.
;;      * New command `yaoddmuse-insert-file-content'.
;;      * Transform image page for view.
;;      * New option `yaoddmuse-transform-image'.
;;      * New commands:
;;        `yaoddmuse-toggle-image-status'
;;        `yaoddmuse-save-as'
;;      * Command `yaoddmuse-follow' can pick up
;;        page name from [[image:PAGENAME]].
;;      * Fix doc.
;;
;; 2009/02/23
;;      * Now can upload picture or compress file to Wiki directly,
;;        not need browser any more.
;;      * Highlight new page for warning.
;;      * New commands
;;        `yaoddmuse-redirect'.
;;        `yaoddmuse-delete'.
;;      * Use "flet" wrap "(basic-save-buffer)".
;;      * Fix doc.
;;
;; 2009/02/22
;;      * Add (set-buffer-modified-p nil) make modification flag
;;        with `nil' just after getting page, protect download
;;        content.
;;        Thanks rubikitch for this patch. :)
;;      * Refactory code.
;;      * New commands:
;;        `yaoddmuse-post-dired-default'.
;;        `yaoddmuse-post-file-default'.
;;      * New options:
;;        `yaoddmuse-notify-function'.
;;        `yaoddmuse-display-after-get'.
;;      * Fix doc.
;;
;; 2009/02/19
;;      * Add new command `yaoddmuse-browse-page-default'.
;;
;; 2009/02/17
;;      * Remove unnecessary completion name for `yaoddmuse-post-library'
;;        and `yaoddmuse-post-library-default'
;;      * Pick file name around point when use
;;        `yaoddmuse-post-library' and `yaoddmuse-post-library-default'.
;;
;; 2009/02/13
;;      * Fix bug of `yaoddmuse-update-pagename'.
;;
;; 2009/02/12
;;      * Remove option `yaoddmuse-startup-get-pagename'.
;;      * Add new command `yaoddmuse-update-pagename'.
;;      * Add option `unforced' to function `yaoddmuse-update-pagename'.
;;      * Add miss command `yaoddmuse-toggle-minor'.
;;      * Fix doc.
;;
;; 2009/02/11
;;      * Remember last `summary' string for fast input.
;;
;; 2009/01/19
;;      * Add highlight support for [[image:ImagePage]].
;;
;; 2009/01/12
;;      * Improve wiki syntax highlight.
;;      * Add syntax highlight for `tables' and `dialog'.
;;      * Fix the bug of `yaoddmuse-pagename-at-point'.
;;
;; 2009/01/11
;;      * Add new feature: browse page after post successful
;;        if i type "C-u" before call post command.
;;      * Modified (kill-buffer) to (kill-buffer (current-buffer))
;;        to compatible with Emacs 22.
;;      * Add highlight for [url url-name] support.
;;      * Add navigation functions.
;;      * Remove blank from `yaoddmuse-username'.
;;
;; 2009/01/10
;;      * Add new command `yaoddmuse-follow' for figure
;;        out what page we need to visit.
;;      * Add new option `yaoddmuse-highlight-elisp-page'
;;        to do `emacs-lisp' syntax highlight when current page
;;        is elisp file.
;;        Thanks "benny" for this advice!
;;      * Add new command `yaoddmuse-post-library-default'
;;        post library to default wiki.
;;      * Fix post bug.
;;
;; 2009/01/10
;;      * Add new option `yaoddmuse-browse-function' for customize
;;        your own advanced browse function.
;;
;; 2009/01/09
;;      * Fix regular expression for keywords highlight.
;;
;; 2009/01/06
;;      * First released.
;;

;;; Acknowledgements:
;;
;;      Alex Schroeder  <mailto:kensanata@gmail.com>
;;      rubikitch       <rubikitch@ruby-lang.org>
;;              For create oddmuse.el
;;
;;      rubikitch
;;              For patch.
;;      benny (IRC nickname)
;;              For advices.
;;

;;; TODO
;;
;;

;;; Require
(eval-when-compile (require 'cl))
(require 'sgml-mode)
(require 'skeleton)
(require 'url)
(require 'thingatpt)
(require 'find-func)
(require 'dired)

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Customize ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defgroup yaoddmuse nil
  "Yet another Oddmuse mode for Emacs."
  :group 'edit)

(defcustom yaoddmuse-directory "~/.yaoddmuse"
  "Directory to storage oddmuse pages."
  :type 'string
  :group 'yaoddmuse)

(defcustom yaoddmuse-assoc-mode t
  "Whether assoc files in `yaoddmuse-directory' with `yaoddmuse-mode'.
Default is t."
  :type 'boolean
  :set (lambda (symbol value)
         (set symbol value)
         (if value
             (add-to-list 'auto-mode-alist
                          `(,(expand-file-name yaoddmuse-directory) . yaoddmuse-mode))
           (remove-hook 'auto-mode-alist
                        `(,(expand-file-name yaoddmuse-directory) . yaoddmuse-mode))))
  :group 'yaoddmuse)

(defcustom yaoddmuse-wikis
  '(("TestWiki" "http://www.emacswiki.org/cgi-bin/test" utf-8 "uihnscuskc=1;")
    ("EmacsWiki" "http://www.emacswiki.org/cgi-bin/emacs" utf-8 "uihnscuskc=1;")
    ("CommunityWiki" "http://www.communitywiki.org/cw" utf-8 "uihnscuskc=1;")
    ("RatpoisonWiki" "http://ratpoison.antidesktop.net/cgi-bin/wiki" utf-8 "uihnscuskc=1;")
    ("StumpwmWiki" "http://stumpwm.antidesktop.net/cgi-bin/wiki" utf-8 "uihnscuskc=1;")
    ("OddmuseWiki" "http://www.oddmuse.org/cgi-bin/oddmuse" utf-8 "uihnscuskc=1;"))
  "Alist mapping wiki names to URLs.
First argument is Wiki name.
Second argument is Wiki url.
Third argument is coding for Wiki.
Fourth argument is captcha string for edit protected.

You can add new list as format (WikiName WikiURL CodingSystem CaptchaString).
But don't modified default elements of `yaoddmuse-wikis', probably causes trouble!"
  :type '(repeat (list (string :tag "Wiki")
                       (string :tag "URL")
                       (symbol :tag "Coding System")
                       (string :tag "Captcha")))
  :group 'yaoddmuse)

(defcustom yaoddmuse-default-wiki "EmacsWiki"
  "The default wiki name for edit.
This value must match the KEY value of `yaoddmuse-wikis'.
This value is use by function `yaoddmuse-edit-default'."
  :type 'string
  :group 'yaoddmuse)

(defcustom yaoddmuse-username user-full-name
  "Username to use when posting.
Setting a username is the polite thing to do."
  :type 'string
  :set (lambda (symbol value)
         ;; Remove blank from user name for wiki link navigation.
         (setq value (replace-regexp-in-string " " "" value))
         (set symbol value))
  :group 'yaoddmuse)

(defcustom yaoddmuse-password ""
  "Password to use when posting.
You only need this if you want to edit locked pages and you
know an administrator password."
  :type 'string
  :group 'yaoddmuse)

(defcustom yaoddmuse-transform-image t
  "Whether transform image content.
If non-nil, will transform image content and view it.
Otherwise, don't transform image content.
Default is t."
  :type 'boolean
  :group 'yaoddmuse)

(defcustom yaoddmuse-display-after-get t
  "Whether display `yaoddmuse-mode' buffer after GET.
Non-nil mean display.
Nil mean don't display.
Default is t."
  :type 'boolean
  :group 'yaoddmuse)

(defcustom yaoddmuse-close-after-post nil
  "Whether close `yaoddmuse-mode' buffer after POST.
Non-nil mean close.
Nil mean don't close.
Default is t."
  :type 'boolean
  :group 'yaoddmuse)

(defcustom yaoddmuse-post-dired-confirm t
  "Whether confirmation is needed to post mark dired files.
Nil means no confirmation is needed.
If non-nil, will notify you before post dired mark files."
  :type 'boolean
  :group 'yaoddmuse)

(defcustom yaoddmuse-edit-protect t
  "This option is make user can post wiki page without text captcha.
Some wikis, such as EmacsWiki, use a text captcha
to protect pages from being edited.
So if you edit wiki (such as EmacsWiki),
please make sure this option is `non-nil'."
  :type 'boolean
  :group 'yaoddmuse)

(defcustom yaoddmuse-use-always-minor nil
  "When t, set all the minor mode bit to all editions.
This can be changed for each edition using `yaoddmuse-toggle-minor'."
  :type 'boolean
  :group 'yaoddmuse)

(defcustom yaoddmuse-browse-function 'browse-url
  "The browse function use in `yaoddmuse-handle-browse'.
Default is function `browse-url'."
  :type 'function
  :group 'yaoddmuse)

(defcustom yaoddmuse-notify-function 'yaoddmuse-notify-default
  "Notify function for getting and posting.
It accepts one argument, the string to notify."
  :type 'function
  :group 'yaoddmuse)

(defcustom yaoddmuse-highlight-elisp-page t
  "Whether use syntax highlight elisp page.
Default is t."
  :type 'boolean
  :group 'yaoddmuse)

(defcustom yaoddmuse-screenshot-program "import"
  "The default tool for screenshot."
  :type 'string
  :group 'yaoddmuse)

(defcustom yaoddmuse-screenshot-filename "/tmp/yaoddmuse-screenshot.png"
  "The default file for save screenshot."
  :type 'string
  :group 'yaoddmuse)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Faces ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defface yaoddmuse-tag
  '((t (:foreground "Gold")))
  "Highlight tag."
  :group 'yaoddmuse)

(defface yaoddmuse-link
  '((t (:foreground "Khaki")))
  "Highlight link."
  :group 'yaoddmuse)

(defface yaoddmuse-url
  '((t (:foreground "Grey20")))
  "Highlight link."
  :group 'yaoddmuse)

(defface yaoddmuse-url-name
  '((t (:foreground "Orange")))
  "Highlight link."
  :group 'yaoddmuse)

(defface yaoddmuse-dialog
  '((t (:foreground "Peru")))
  "Highlight dialog."
  :group 'yaoddmuse)

(defface yaoddmuse-lisp-keyword
  '((t (:foreground "PaleGreen")))
  "Highlight lisp keyword `Lisp:'."
  :group 'yaoddmuse)

(defface yaoddmuse-lisp-file
  '((t (:foreground "GreenYellow")))
  "Highlight lisp file."
  :group 'yaoddmuse)

(defface yaoddmuse-source-code
  '((t (:foreground "Yellow")))
  "Highlight source-code."
  :group 'yaoddmuse)

(defface yaoddmuse-image-link
  '((t (:foreground "DarkRed")))
  "Highlight image-link."
  :group 'yaoddmuse)

(defface yaoddmuse-image-link-name
  '((t (:foreground "Chocolate")))
  "Highlight image-link name."
  :group 'yaoddmuse)

(defface yaoddmuse-heading
  '((t (:foreground "Green")))
  "Highlight heading."
  :group 'yaoddmuse)

(defface yaoddmuse-tables
  '((t (:foreground "Aquamarine")))
  "Highlight tables."
  :group 'yaoddmuse)

(defface yaoddmuse-indent
  '((t (:foreground "Tomato")))
  "Highlight indent."
  :group 'yaoddmuse)

(defface yaoddmuse-bold
  '((t (:foreground "DodgerBlue")))
  "Highlight bold."
  :group 'yaoddmuse)

(defface yaoddmuse-underline
  '((t (:foreground "Purple")))
  "Highlight underline."
  :group 'yaoddmuse)

(defface yaoddmuse-italic
  '((t (:foreground "Brown")))
  "Highlight italic."
  :group 'yaoddmuse)

(defface yaoddmuse-short-dash
  '((t (:foreground "Pink2")))
  "Highlight short dash."
  :group 'yaoddmuse)

(defface yaoddmuse-long-dash
  '((t (:foreground "LawnGreen")))
  "Highlight long dash."
  :group 'yaoddmuse)

(defface yaoddmuse-separate
  '((t (:foreground "DarkRed")))
  "Highlight separate."
  :group 'yaoddmuse)

(defface yaoddmuse-level-1
  '((t (:foreground "Grey100")))
  "Highlight indent level 1."
  :group 'yaoddmuse)

(defface yaoddmuse-level-2
  '((t (:foreground "Grey70")))
  "Highlight indent level 2."
  :group 'yaoddmuse)

(defface yaoddmuse-level-3
  '((t (:foreground "Grey40")))
  "Highlight indent level 3."
  :group 'yaoddmuse)

(defface yaoddmuse-new-page
  '((t (:foreground "Red" :bold t)))
  "Warning new page."
  :group 'yaoddmuse)

(defface yaoddmuse-edit-status-face
  '((((class color) (background dark))
     (:foreground "Gold")))
  "Face for highlighting yaoddmuse edit status."
  :group 'yaoddmuse)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Variable ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defvar yaoddmuse-wikiname nil
  "The current wiki.
Must match a key from `yaoddmuse-wikis'.")
(make-variable-buffer-local 'yaoddmuse-wikiname)

(defvar yaoddmuse-pagename nil
  "Page name of the current buffer.")
(make-variable-buffer-local 'yaoddmuse-pagename)

(defvar yaoddmuse-minor nil
  "Is this editing a minor change.")
(make-variable-buffer-local 'yaoddmuse-minor)

(defvar yaoddmuse-edit-status-string nil
  "The edit status at mode-line.")
(make-variable-buffer-local 'yaoddmuse-edit-status)

(defvar yaoddmuse-retrieve-buffer nil
  "The download buffer used by `url-retrieve'.")
(make-variable-buffer-local 'yaoddmuse-retrieve-buffer)

(defvar yaoddmuse-image-status nil
  "The status of current page.
This status will turn on when transform image content.
Default is nil.")
(make-variable-buffer-local 'yaoddmuse-image-status)

(defvar yaoddmuse-pages-hash (make-hash-table :test 'equal)
  "The wiki-name / pages pairs.")

(defvar yaoddmuse-last-summary nil
  "The last summary for input.")

(defvar yaoddmuse-args-get
  "action=browse;raw=1;id=%t"
  "Command to use for publishing pages.
It must print the page to stdout.

%t  URL encoded pagename, eg. HowTo, How_To, or How%20To")

(defvar yaoddmuse-args-index
  "action=index;raw=1"
  "URL arguments to use for publishing index pages.")

(defvar yaoddmuse-args-post
  (concat "title=%t;"
          "summary=%s;"
          "username=%u;"
          "pwd=%p;"
          "recent_edit=%m;"
          "text=%x")
  "URL arguments to use for publishing pages.

%t  pagename
%s  summary
%u  username
%p  password
%x  text")

(defvar yaoddmuse-post-mime-alist
  '((".css" . "text/css")
    (".xml" . "text/xml")
    (".tar" . "application/x-tar")
    (".tar.gz" . "application/x-gzip")
    (".gzip" . "application/x-gzip-compressed")
    (".zip" . "application/x-zip-compressed")
    (".jpeg" . "image/jpeg")
    (".png"  . "image/png"))
  "An alist of file extensions and corresponding MIME content-types.")

(defvar yaoddmuse-imenu-regexp "^\\(=+\\)\\s-*\\(.*?\\)\\s-*\\1"
 "A regular expression for headings to be added to an index menu.")


(defvar yaoddmuse-mode-map
  (let ((map (make-sparse-keymap)))
    ;; Edit.
    (define-key map (kbd "C-c C-e") 'yaoddmuse-edit-default)
    (define-key map (kbd "C-c C-S-e") 'yaoddmuse-edit)
    (define-key map (kbd "C-c C-o") 'yaoddmuse-follow)
    (define-key map (kbd "C-c C-t") 'sgml-tag)
    ;; Post.
    (define-key map (kbd "C-c C-c") 'yaoddmuse-post-current-buffer)
    (define-key map (kbd "C-c C-S-c") 'yaoddmuse-post-buffer)
    (define-key map (kbd "C-c C-l") 'yaoddmuse-post-library-default)
    (define-key map (kbd "C-c C-S-l") 'yaoddmuse-post-library)
    (define-key map (kbd "C-c C-f") 'yaoddmuse-post-file)
    (define-key map (kbd "C-c C-S-f") 'yaoddmuse-post-file-default)
    (define-key map (kbd "C-c C-y") 'yaoddmuse-post-screenshot)
    (define-key map (kbd "C-c C-S-y") 'yaoddmuse-post-screenshot-default)
    ;; View.
    (define-key map (kbd "C-c C-v") 'yaoddmuse-browse-page-default)
    (define-key map (kbd "C-c C-S-v") 'yaoddmuse-browse-page)
    (define-key map (kbd "C-c C-'") 'yaoddmuse-browse-page-default-diff)
    (define-key map (kbd "C-c C-S-'") 'yaoddmuse-browse-page-diff)
    (define-key map (kbd "C-c C-s") 'yaoddmuse-browse-current-page)
    (define-key map (kbd "C-c C-r") 'yaoddmuse-revert)
    ;; Navigation.
    (define-key map (kbd "C-c C-n") 'yaoddmuse-navi-next-heading)
    (define-key map (kbd "C-c C-p") 'yaoddmuse-navi-prev-heading)
    ;; Update.
    (define-key map (kbd "C-c C-j") 'yaoddmuse-update-pagename)
    ;; Insert.
    (define-key map (kbd "C-c C-i") 'yaoddmuse-insert-pagename)
    (define-key map (kbd "C-c C-x") 'yaoddmuse-insert-file-content)
    ;; Misc.
    (define-key map (kbd "C-c C-u") 'yaoddmuse-kill-url)
    (define-key map (kbd "C-c C-m") `yaoddmuse-toggle-minor)
    (define-key map (kbd "C-c C-d") 'yaoddmuse-delete)
    (define-key map (kbd "C-c C-S-D") 'yaoddmuse-redirect)
    (define-key map (kbd "C-c C-S-t") 'yaoddmuse-toggle-image-status)
    (define-key map (kbd "C-c C-w") 'yaoddmuse-save-as)
    map)
  "Keymap used by `yaoddmuse-mode'.")

(defun yaoddmuse-highlight-keywords ()
  "Highlight keywords."
  (font-lock-add-keywords
   nil
   '(("\\`This page does not exist.*$" . 'yaoddmuse-new-page)
     ("<\\(/?[a-z]+\\)>" . 'yaoddmuse-tag)
     ("^=\\{2,\\}\\([^=]+\\)=\\{2,\\}" 1 'yaoddmuse-heading)
     ("\\[\\[\\(image:\\)\\(\\([^\\[]\\|[^\\]]\\)+\\)\\]\\]" 1 'yaoddmuse-image-link)
     ("\\[\\[\\(image:\\)\\(\\([^\\[]\\|[^\\]]\\)+\\)\\]\\]" 2 'yaoddmuse-image-link-name)
     ("\\[\\(\\([^\\[]\\|[^\\]]\\)+\\)[[:blank:]]\\(\\([^\\[]\\|[^\\]]\\)+\\)\\]" 1 'yaoddmuse-url)
     ("\\[\\(\\([^\\[]\\|[^\\]]\\)+\\)[[:blank:]]\\(\\([^\\[]\\|[^\\]]\\)+\\)\\]" 3 'yaoddmuse-url-name)
     ("\\<[A-Z\xc0-\xde]+[a-z\xdf-\xff]+\\([A-Z\xc0-\xde]+[a-z\xdf-\xff]*\\)+\\>" . 'yaoddmuse-link)
     ("\\[\\[\\(\\([^\\[]\\|[^\\]]\\)+\\)\\]\\]" 1 'yaoddmuse-link)
     ("\\b\\(Lisp:\\)\\([^ ]+\\.el\\)\\b" 1 'yaoddmuse-lisp-keyword)
     ("\\b\\(Lisp:\\)\\([^ ]+\\.el\\)\\b" 2 'yaoddmuse-lisp-file)
     ("^\\({{{\\|}}}\\|;;;\\)\\s-" 1 'yaoddmuse-source-code)
     ("^\\[new:?\\([^\\[]\\|[^\\]]\\)*\\]$" . 'yaoddmuse-dialog)
     ("|\\{2,\\}" . 'yaoddmuse-tables)
     ("^\\([:]+\\)\\s-" 1 'yaoddmuse-indent)
     ("\\s-\\(--\\)\\s-" . 'yaoddmuse-short-dash)
     ("\\s-\\(---\\)\\s-" . 'yaoddmuse-long-dash)
     ("^----$" . 'yaoddmuse-separate)
     ("''\\([^']+\\)''" 1 'yaoddmuse-bold)
     ("[^^\n\\*][\\*]+\\([^\\*]+\\)[\\*]+" 1 'yaoddmuse-bold)
     ("\\s-/+\\([^/]+\\)/+\\s-" 1 'yaoddmuse-italic)
     ("\\s-_+\\([^_]+\\)_+\\s-" 1 'yaoddmuse-underline)
     ("^\\(\\([*#]\\)\\{1\\}\\)\\s-" 1 'yaoddmuse-level-1)
     ("^\\(\\([*#]\\)\\{2\\}\\)\\s-" 1 'yaoddmuse-level-2)
     ("^\\(\\([*#]\\)\\{3\\}\\)\\s-" 1 'yaoddmuse-level-3)
     ))
  (font-lock-mode 1))

(define-derived-mode yaoddmuse-mode text-mode "Yaoddmuse"
  "Yet another mode to edit Oddmuse wiki pages."
  ;; Face setup.
  (yaoddmuse-highlight-keywords)
  ;; Local variable setup.
  (set (make-local-variable 'sgml-tag-alist)
       `(("b") ("code") ("em") ("i") ("strong") ("nowiki")
         ("pre" \n) ("tt") ("u")))
  (set (make-local-variable 'skeleton-transformation) 'identity)
  ;; Wiki and page name setup.
  (setq imenu-generic-expression (list (list nil yaoddmuse-imenu-regexp 2)))
  (and buffer-file-name
       ;; Setup wiki name.
       (setq yaoddmuse-wikiname
             (file-name-nondirectory
              (substring (file-name-directory buffer-file-name) 0 -1)))
       ;; Setup page name.
       (setq yaoddmuse-pagename
             (file-name-nondirectory buffer-file-name))
       ;; Initialize oddmuse-minor according to `yaoddmuse-use-always-minor'
       (setq yaoddmuse-minor
             yaoddmuse-use-always-minor))
  ;; Load emacs-lisp-mode syntax highlight,
  ;; if option `yaoddmuse-highlight-elisp-page' is turn on
  ;; and current page is elisp file.
  (when (and yaoddmuse-highlight-elisp-page
             (string-match "^.*\\.el$" yaoddmuse-pagename))
    (set-syntax-table emacs-lisp-mode-syntax-table)
    (setq major-mode 'emacs-lisp-mode)
    (lisp-mode-variables))
  ;; Load keymap.
  (use-local-map yaoddmuse-mode-map)
  ;; Other setup.
  (goto-address)
  (setq indent-tabs-mode nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Interactive Functions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Edit.

(defun yaoddmuse-edit (&optional wikiname pagename prefix)
  "Edit a page on a wiki.
WIKINAME is the name of the wiki as defined in `yaoddmuse-wikis',
PAGENAME is the pagename of the page you want to edit.
Use a PREFIX argument to force a reload of the page."
  (interactive)
  ;; Set value with `prefix'
  ;; when `prefix' is `nil'
  ;; and `current-prefix-arg' is `non-nil'.
  (or prefix (if current-prefix-arg (setq prefix t)))
  ;; Edit page.
  (yaoddmuse-get-pagename wikiname pagename
                          (if prefix
                              'yaoddmuse-handle-get
                            'yaoddmuse-handle-get-or-display)))

(defun yaoddmuse-edit-default (prefix)
  "Edit a page with default wiki `yaoddmuse-default-wiki'.
Use a PREFIX argument to force a reload of the page."
  (interactive "P")
  (yaoddmuse-edit yaoddmuse-default-wiki nil prefix))

(defun yaoddmuse-follow ()
  "Figure out what page we need to visit and call `yaoddmuse-edit' on it.
Default, this try to pick up page name around point.
You can type `C-u' before this command make it prompt
page name when can't find page name around point."
  (interactive)
  ;; Get follow page.
  (if current-prefix-arg
      ;; Read page from user.
      (yaoddmuse-get-pagename yaoddmuse-wikiname nil 'yaoddmuse-handle-follow)
    ;; Otherwise try follow page around point.
    (if (yaoddmuse-pagename-at-point)
        (yaoddmuse-get-page yaoddmuse-wikiname (yaoddmuse-pagename-at-point))
      (message "No valid link around point."))))

;;; Post

(defun yaoddmuse-post-buffer (&optional post-buffer summary prefix)
  "Post the BUFFER to the current wiki.
The current wiki is taken from `yaoddmuse-wiki'.
The POST-BUFFER is the buffer you want post,
Default will read buffer name if POST-BUFFER is void.
SUMMARY is summary name for post.
If PREFIX is non-nil, will view page after post successful."
  (interactive)
  ;; Read buffer name.
  (or post-buffer
      (setq post-buffer (read-buffer "Buffer name: ")))
  (set-buffer post-buffer)
  ;; Try to save file before post.
  (when buffer-file-name
    (flet ((message (&rest args)))
      (basic-save-buffer)))
  ;; Post page.
  (yaoddmuse-post yaoddmuse-wikiname
                  yaoddmuse-pagename
                  (buffer-name)
                  (buffer-string)
                  summary
                  prefix))

(defun yaoddmuse-post-current-buffer (prefix)
  "Post current buffer to current wiki.
The current wiki is taken from `yaoddmuse-wiki'.
Use a PREFIX argument to browse page after post successful."
  (interactive "P")
  (yaoddmuse-post-buffer (current-buffer) nil prefix))

(defun yaoddmuse-post-file (&optional filename wikiname pagename summary prefix)
  "Post file to current wiki.
The current wiki is taken from `yaoddmuse-wiki'.
FILENAME is file name you want post.
WIKINAME is wiki name for post.
PAGENAME is page name for post.
SUMMARY is summary for post.
If PREFIX is non-nil, will view page after post successful."
  (interactive)
  ;; Read file.
  (unless filename
    (setq filename (read-file-name "File name: ")))
  ;; Check file.
  (if (and (file-exists-p filename)
           (not (file-directory-p filename)))
      ;; Post file.
      (yaoddmuse-post wikiname
                      pagename
                      (file-name-nondirectory filename)
                      (yaoddmuse-encode-file filename)
                      summary
                      prefix)
    ;; Error when invalid file name.
    (message "Invalid file name %s" filename)))

(defun yaoddmuse-post-file-default (prefix)
  "Post file to default wiki.
If PREFIX is non-nil, will view page after post successful."
  (interactive "P")
  (yaoddmuse-post-file nil yaoddmuse-default-wiki nil nil prefix))

(defun yaoddmuse-post-library (&optional library wikiname pagename summary prefix)
  "Post library to current wiki.
The current wiki is taken from `yaoddmuse-wikis'.
LIBRARY is library name you want post.
WIKINAME is wiki name for post.
PAGENAME is page name for post.
SUMMARY is summary for post.
If PREFIX is non-nil, will view page after post successful."
  (interactive)
  ;; Get library name.
  (or library (setq library (yaoddmuse-get-library)))
  ;; Post library to wiki.
  (let ((filename (find-library-name library)))
    (yaoddmuse-post-file filename wikiname pagename summary prefix)))

(defun yaoddmuse-post-library-default (prefix)
  "Post library to default wiki.
Use a PREFIX argument to browse page after post successful."
  (interactive "P")
  (let* ((library (yaoddmuse-get-library))
         (filename (find-library-name library))
         (pagename (file-name-nondirectory filename)))
    ;; Post library to default wiki.
    (yaoddmuse-post-file filename yaoddmuse-default-wiki pagename nil prefix)))

(defun yaoddmuse-post-dired (&optional wikiname summary prefix)
  "Post dired marked files to current wiki.
The current wiki is taken from `yaoddmuse-wikis'.
WIKINAME is wiki name for post.
SUMMARY is summary for post.
If PREFIX is non-nil, will view page after post successful."
  (interactive)
  (if (eq major-mode 'dired-mode)
      (if (or (not yaoddmuse-post-dired-confirm)
              (yes-or-no-p "Do you want post marked files to wiki."))
          (let (filename pagename)
            (or summary (setq summary (yaoddmuse-read-summary)))
            (dolist (file (dired-get-marked-files))
              (setq filename file)
              (setq pagename (file-name-nondirectory filename))
              (yaoddmuse-post-file filename wikiname pagename summary prefix))))
    (message "This command in only for `dired-mode'.")))

(defun yaoddmuse-post-dired-default (prefix)
  "Post dired marked files to default wiki.
Use a PREFIX argument to browse page after post successful."
  (interactive "P")
  (yaoddmuse-post-dired yaoddmuse-default-wiki nil prefix))

(defun yaoddmuse-post-screenshot (&optional wikiname summary prefix)
  "Post screenshot to current wiki.
The current wiki is taken from `yaoddmuse-wikis'.
WIKINAME is wiki name for post.
SUMMARY is summary for post.
If PREFIX is non-nil, will view page after post successful."
  (interactive)
  ;; Check screenshot program.
  (if (executable-find yaoddmuse-screenshot-program)
      (progn
        ;; Screenshot.
        (message "Please use mouse select region for screenshot.")
        (call-process yaoddmuse-screenshot-program nil nil nil yaoddmuse-screenshot-filename)
        ;; Post screenshot.
        (yaoddmuse-post-file yaoddmuse-screenshot-filename wikiname nil "Screenshot by yaoddmuse.el" prefix))
    (message "Please make sure have install program '%s'." yaoddmuse-screenshot-program)))

(defun yaoddmuse-post-screenshot-default (prefix)
  "Post screenshot to default wiki.
Use a PREFIX argument to browse page after post successful."
  (interactive "P")
  (yaoddmuse-post-screenshot yaoddmuse-default-wiki nil prefix))

;;; View

(defun yaoddmuse-revert ()
  "Reload current edit page."
  (interactive)
  (yaoddmuse-get-page yaoddmuse-wikiname yaoddmuse-pagename))

(defun yaoddmuse-browse-page (&optional wikiname pagename)
  "Browse special page in wiki.
WIKINAME is the name of the wiki as defined in `yaoddmuse-wikis',
PAGENAME is the pagename of the page you want to edit."
  (interactive)
  (yaoddmuse-get-pagename wikiname pagename 'yaoddmuse-handle-browse))

(defun yaoddmuse-browse-page-default ()
  "Brose special page with `yaoddmuse-default-wiki'."
  (interactive)
  (yaoddmuse-browse-page yaoddmuse-default-wiki))

(defun yaoddmuse-browse-page-diff (&optional wikiname pagename)
  "Browse special page diff in wiki.
WIKINAME is the name of the wiki as defined in `yaoddmuse-wikis',
PAGENAME is the pagename of the page you want to edit."
  (interactive)
  (yaoddmuse-get-pagename wikiname pagename 'yaoddmuse-handle-browse-diff))

(defun yaoddmuse-browse-page-default-diff ()
  "Brose special page with `yaoddmuse-default-wiki'."
  (interactive)
  (yaoddmuse-browse-page-diff yaoddmuse-default-wiki))

(defun yaoddmuse-browse-current-page ()
  "Browse current page."
  (interactive)
  (yaoddmuse-browse-page yaoddmuse-wikiname yaoddmuse-pagename))

;;; Navigation

(defun yaoddmuse-navi-next-heading ()
  "Goto next heading."
  (interactive)
  (if (bolp)
      (forward-char +1))
  (unless (re-search-forward "^=+" nil t)
    (message "Reach bottom heading."))
  (move-beginning-of-line 1))

(defun yaoddmuse-navi-prev-heading ()
  "Goto previous heading."
  (interactive)
  (move-beginning-of-line 1)
  (unless (re-search-backward "^=+" nil t)
    (message "Reach top heading.")))

;;; Misc

(defun yaoddmuse-insert-pagename (&optional pagename)
  "Insert a PAGENAME of current wiki with completion."
  (interactive)
  ;; Insert page name.
  (yaoddmuse-get-pagename yaoddmuse-wikiname pagename 'yaoddmuse-handle-insert))

(defun yaoddmuse-insert-file-content (file)
  "Insert FILE content.
This function will encode special file content, such picture or compress file."
  (interactive "fFile: ")
  (insert (yaoddmuse-encode-file file)))

(defun yaoddmuse-kill-url ()
  "Make the URL of current oddmuse page the latest kill in the kill ring."
  (interactive)
  (kill-new (yaoddmuse-url yaoddmuse-wikiname yaoddmuse-pagename))
  (message "Copy current url '%s' in yank" (yaoddmuse-url yaoddmuse-wikiname yaoddmuse-pagename)))

(defun yaoddmuse-update-pagename (&optional unforced)
  "Update all page name match in `yaoddmuse-wikis'.
By default, this function will update page name forcibly.
If UNFORCED is non-nil, just update page name when have not update."
  (interactive)
  (unless (and unforced
               (> (hash-table-count yaoddmuse-pages-hash) 0))
    (dolist (wiki yaoddmuse-wikis)
      ;; Force update page name list.
      (yaoddmuse-get-pagename (car wiki) nil nil t))))

(defun yaoddmuse-toggle-minor (&optional arg)
  "Toggle minor mode state.
If ARG is non-nil, always turn on."
  (interactive)
  (let ((num (prefix-numeric-value arg)))
    (cond
     ((or (not arg) (equal num 0))
      (setq yaoddmuse-minor (not yaoddmuse-minor)))
     ((> num 0) (set 'yaoddmuse-minor t))
     ((< num 0) (set 'yaoddmuse-minor nil)))
    ;; Update edit status at mode-line.
    (yaoddmuse-update-edit-status)
    ;; Return edit status.
    yaoddmuse-minor))

(defun yaoddmuse-redirect ()
  "Redirect page."
  (interactive)
  ;; Redirect page.
  (yaoddmuse-get-pagename yaoddmuse-wikiname nil 'yaoddmuse-handle-redirect))

(defun yaoddmuse-delete ()
  "Delete page."
  (interactive)
  ;; Delete page.
  (yaoddmuse-get-pagename yaoddmuse-wikiname nil 'yaoddmuse-handle-delete))

(defun yaoddmuse-toggle-image-status ()
  "Toggle image status.
If content is raw text format, transform it to image format.
If content is image format, transform it to raw text format."
  (interactive)
  (save-excursion
    ;; Test whether is image content.
    (if (string-match "\\`#FILE image/\\(png\\|jpeg\\)$"
                      (buffer-substring-no-properties (goto-char (point-min))
                                                      (line-end-position)))
        (if yaoddmuse-image-status
            (yaoddmuse-turn-off-image-status)
          (yaoddmuse-turn-on-image-status))
      (message "Invalid image content."))))

(defun yaoddmuse-save-as ()
  "Save as file.
This function will try to encode special page content before save.
such as picture or compress."
  (interactive)
  (save-excursion
    (let ((test-string (buffer-substring-no-properties
                        (goto-char (point-min))
                        (line-end-position)))
          (data (buffer-substring-no-properties
                 (point-min)
                 (point-max)))
          suffix)
      (when (string-match "\\`#FILE \\([^ \n]+\\)$" test-string)
        (setq data (yaoddmuse-decode-string data))
        (setq suffix (car (rassoc (match-string 1 test-string)
                                  yaoddmuse-post-mime-alist))))
      (with-temp-buffer
        (insert data)
        (write-file (read-file-name (format "File: (Suffix: %s) " suffix)))))))

(defun emacswiki (&optional pagename prefix)
  "Edit a page on the EmacsWiki.
PAGENAME is the pagename of the page you want to edit.
Use a PREFIX argument to force a reload of the page."
  (interactive)
  (yaoddmuse-edit "EmacsWiki" pagename prefix))

(defun emacswiki-post (&optional pagename summary prefix)
  "Post file to the EmacsWiki.
PAGENAME is page name for post, whose default is basename of current filename.
SUMMARY is summary for post.
If PREFIX is non-nil, will view page after post successful. "
  (interactive)
  (let ((file (file-name-nondirectory buffer-file-name)))
    (yaoddmuse-post-file file "EmacsWiki" (or pagename file) summary prefix)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities Functions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun yaoddmuse-get-pagename (wikiname &optional pagename handle-function forced)
  "Get page name in wiki for completing.
WIKINAME is the name of the wiki as defined in `yaoddmuse-wikis',
PAGENAME is page name.
HANDLE-FUNCTION is function handle page with special action.

By default, won't update page name when have updated,
unless option FORCED is non-nil."
  ;; Read wiki name if `wikiname' is void.
  (or wikiname (setq wikiname (yaoddmuse-read-wikiname)))
  ;; Create storage directory.
  (make-directory (concat yaoddmuse-directory "/" wikiname) t)
  ;; Get page name or handle page.
  (if (and (yaoddmuse-get-pagename-table wikiname)
           (not forced))
      ;; Call function `handle-function' directly
      ;; when have updated page name and option `forced' is nil.
      (when (and (fboundp handle-function)
                 handle-function)
        (funcall handle-function wikiname pagename))
    ;; Otherwise get page name.
    (let* ((url (yaoddmuse-get-url wikiname))
           (coding (yaoddmuse-get-coding wikiname))
           retrieve-buffer
           retrieve-buffer-name)
      ;; Initialize url request parameter.
      (yaoddmuse-retrieve-request "GET")
      (setq url (yaoddmuse-format yaoddmuse-args-index coding url))
      ;; Get unique buffer for handle information.
      (setq retrieve-buffer (yaoddmuse-get-unique-buffer))
      (setq retrieve-buffer-name (buffer-name retrieve-buffer))
      ;; Get pagename.
      (with-current-buffer (get-buffer retrieve-buffer-name)
        (setq yaoddmuse-retrieve-buffer
              (url-retrieve url
                            'yaoddmuse-get-pagename-callback
                            (list retrieve-buffer-name coding
                                  wikiname pagename handle-function)))))))

(defun yaoddmuse-get-pagename-callback (&optional redirect retrieve-buffer-name coding
                                                  wikiname pagename handle-function)
  "The callback function for `yaoddmuse-get-pagename'.
REDIRECT is default argument for check status.
RETRIEVE-BUFFER-NAME is name of retrieve buffer.
CODING is coding system for decode.
WIKINAME is wiki name.
PAGENAME is page name.
HANDLE-FUNCTION is function that handle download content."
  (let (table)
    ;; Decode pagename information.
    (yaoddmuse-retrieve-decode retrieve-buffer-name coding)
    ;; Update pagename with wiki.
    (with-current-buffer (get-buffer retrieve-buffer-name)
      (setq table (mapcar 'list (split-string (buffer-string))))
      (puthash wikiname table yaoddmuse-pages-hash)
      (kill-buffer (current-buffer))    ;in 22, must have argument with kill-buffer
      )
    ;; Add special action.
    (when (and (fboundp handle-function)
               handle-function)
      (funcall handle-function wikiname pagename))))

(defun yaoddmuse-get-page (wikiname pagename)
  "Get page.
WIKINAME is the name of the wiki as defined in `yaoddmuse-wikis',
PAGENAME is the pagename of the page you want to edit."
  (let* ((url (yaoddmuse-get-url wikiname))
         (coding (yaoddmuse-get-coding wikiname))
         (yaoddmuse-wikiname wikiname)
         (yaoddmuse-pagename pagename)
         retrieve-buffer
         retrieve-buffer-name)
    ;; Initialize url request parameter.
    (yaoddmuse-retrieve-request "GET")
    (setq url (yaoddmuse-format yaoddmuse-args-get coding url))
    ;; Get unique buffer for handle information.
    (setq retrieve-buffer (yaoddmuse-get-unique-buffer))
    (setq retrieve-buffer-name (buffer-name retrieve-buffer))
    ;; Get page.
    (with-current-buffer (get-buffer retrieve-buffer-name)
      (setq yaoddmuse-retrieve-buffer
            (url-retrieve url
                          'yaoddmuse-get-page-callback
                          (list retrieve-buffer-name coding wikiname pagename))))))

(defun yaoddmuse-get-page-callback (&optional redirect retrieve-buffer-name coding wikiname pagename)
  "The callback function for `yaoddmuse-get-page'.
REDIRECT is default argument for check status.
RETRIEVE-BUFFER-NAME is name of retrieve buffer.
CODING is coding system for decode.
WIKINAME is wiki name for post.
PAGENAME is page name for post."
  (if (eq (car redirect) ':error)
      ;; Kill retrieve buffer and notify user when retrieve failed.
      (with-current-buffer (get-buffer retrieve-buffer-name)
        (funcall yaoddmuse-notify-function
                 (format "Get page '%s' from '%s' failed." pagename wikiname))
        (kill-buffer retrieve-buffer-name))
    ;; Otherwise display edit buffer.
    (let ((page-buffer (find-file-noselect
                        (format "%s/%s/%s" yaoddmuse-directory wikiname pagename)))
          (page-buffer-name (yaoddmuse-get-page-buffer-name wikiname pagename)))
      ;; Decode retrieve page information.
      (yaoddmuse-retrieve-decode retrieve-buffer-name coding)
      ;; Refresh page content.
      (set-buffer page-buffer)
      ;; Rename.
      (unless (equal page-buffer-name (buffer-name))
        (rename-buffer page-buffer-name))
      ;; Erase original information.
      (erase-buffer)
      (insert
       (with-current-buffer (get-buffer retrieve-buffer-name)
         (prog1
             (buffer-string)
           (kill-buffer (current-buffer)) ;in 22, must have argument with kill-buffer
           )))
      ;; Notify user.
      (funcall yaoddmuse-notify-function
               (format "Get page '%s' form '%s' successful." pagename wikiname))
      ;; Make sure load `yaoddmuse-mode' first,
      ;; otherwise buffer-local variable will be reset.
      (yaoddmuse-mode)
      ;; Update edit status at mode-line.
      (yaoddmuse-update-edit-status)
      ;; Adjust page content.
      (yaoddmuse-page-content-adjust)
      ;; Protect download content.
      (set-buffer-modified-p nil)
      ;; Switch or popup page.
      (yaoddmuse-display-page page-buffer-name))))

(defun yaoddmuse-page-content-adjust ()
  "Adjust page content."
  (goto-char (point-min))
  (save-excursion
    (cond ( ;; If got new page.
           (looking-at "\\`This page does not exist")
           ;; Adjust string when got new page.
           (erase-buffer)
           (insert "This page does not exist, you can create it now. :)"))
          ( ;; If got image page and option `yaoddmuse-transform-image' is non-nil.
           (and (looking-at "\\`#FILE image/\\(png\\|jpeg\\)$")
                yaoddmuse-transform-image)
           ;; Transform image content.
           (yaoddmuse-turn-on-image-status)))))

(defun yaoddmuse-post (wikiname pagename default-pagename post-string summary &optional browse-page)
  "Posting string to wiki.
WIKINAME is the name of the wiki as defined in `yaoddmuse-wikis',
PAGENAME is the pagename of the page you want to edit.
DEFAULT-PAGENAME is default name for prompt, just use when PAGENAME is nil.
POST-STRING is the string you want post.
SUMMARY is summary for post.
If BROWSE-PAGE is non-nil, will browse page after post successful."
  ;; Read wiki name when `wikiname' is nil.
  (unless wikiname
    (setq wikiname (yaoddmuse-read-wikiname)))
  ;; Read page name when `pagename' is nil.
  (unless pagename
    (setq pagename (yaoddmuse-read-pagename wikiname)))
  ;; Read summary when `summary' is nil.
  (unless summary
    (setq summary (yaoddmuse-read-summary)))
  ;; If option `browse-page' or `current-prefix-arg' is non-nil,
  ;; browse corresponding page after post successful.
  (unless browse-page
    (setq browse-page current-prefix-arg))
  ;; Post.
  (let* ((url (yaoddmuse-get-url wikiname))
         (coding (yaoddmuse-get-coding wikiname))
         (yaoddmuse-minor (if yaoddmuse-minor "on" "off"))
         (yaoddmuse-wikiname wikiname)
         (yaoddmuse-pagename pagename)
         (text post-string))
    (yaoddmuse-retrieve-request "POST" (yaoddmuse-format (yaoddmuse-get-post-args wikiname) coding))
    (url-retrieve url
                  'yaoddmuse-post-callback
                  (list wikiname pagename browse-page))))

(defun yaoddmuse-post-callback (&optional redirect wikiname pagename browse-page)
  "The callback function for `yaoddmuse-post'.
REDIRECT is default argument for check status.
WIKINAME is wiki name for post.
PAGENAME is page name for post.
If BROWSE-PAGE is non-nil, will browse page after post successful."
  (if (eq (car redirect) ':redirect)
      (let ((table (yaoddmuse-get-pagename-table wikiname)))
        ;; Update `pagename' in `yaoddmuse-pages-hash'
        ;; if can't find in `yaoddmuse-pages-hash'.
        (unless (assoc pagename table)
          (setq table (cons (list pagename) table))
          (puthash wikiname table yaoddmuse-pages-hash))
        ;; Whether close buffer after post.
        (if yaoddmuse-close-after-post
            (kill-buffer (yaoddmuse-get-page-buffer-name wikiname pagename)))
        (funcall yaoddmuse-notify-function
                 (format "Page '%s' post to '%s' successful." pagename wikiname))
        ;; Browse page if option `browse-page' is `non-nil'.
        (if browse-page
            (funcall yaoddmuse-browse-function (yaoddmuse-url wikiname pagename))))
    ;; Post failed.
    (funcall yaoddmuse-notify-function
             (format "Page '%s' post to '%s' failed." pagename wikiname))))

(defun yaoddmuse-handle-get (&optional wikiname pagename)
  "The handle function for get page.
WIKINAME is wiki name for post.
PAGENAME is page name for post."
  ;; Read page name when `pagename' is void.
  (or pagename (setq pagename (yaoddmuse-read-pagename wikiname)))
  ;; Get page.
  (yaoddmuse-get-page wikiname pagename))

(defun yaoddmuse-handle-get-or-display (&optional wikiname pagename)
  "The  function for get or display page.
WIKINAME is wiki name for post.
PAGENAME is page name for post."
  ;; Read page name when `pagename' is void.
  (or pagename (setq pagename (yaoddmuse-read-pagename wikiname)))
  ;; Get or display page.
  (let ((page-buffer-name (yaoddmuse-get-page-buffer-name wikiname pagename)))
    (if (get-buffer page-buffer-name)
        ;; Switch page buffer when it have exist.
        (yaoddmuse-display-page page-buffer-name)
      ;; Otherwise, get page.
      (yaoddmuse-get-page wikiname pagename))))

(defun yaoddmuse-handle-follow (&optional wikiname pagename)
  "The handle function for get page name.
WIKINAME is wiki name for post.
PAGENAME is page name for post."
  ;; Read page name when `pagename' is void.
  (or pagename (setq pagename (yaoddmuse-read-pagename wikiname "Edit page")))
  ;; Follow page.
  (yaoddmuse-get-page wikiname pagename))

(defun yaoddmuse-handle-browse (&optional wikiname pagename)
  "The handle function for browse page.
WIKINAME is wiki name for post.
PAGENAME is page name for post."
  ;; Read page name when `pagename' is void.
  (or pagename (setq pagename (yaoddmuse-read-pagename wikiname "Browse page")))
  ;; Brose page.
  (funcall yaoddmuse-browse-function (yaoddmuse-url wikiname pagename)))

(defun yaoddmuse-handle-browse-diff (&optional wikiname pagename)
  "The handle function for browse page diff.
WIKINAME is wiki name for post.
PAGENAME is page name for post."
  ;; Read page name when `pagename' is void.
  (or pagename (setq pagename (yaoddmuse-read-pagename wikiname "Browse page diff")))
  ;; Brose page.
  (funcall yaoddmuse-browse-function (yaoddmuse-url-diff wikiname pagename)))

(defun yaoddmuse-handle-insert (&optional wikiname pagename)
  "The handle function for insert page name.
WIKINAME is wiki name for post.
PAGENAME is page name for post."
  ;; Read page name when `pagename' is void.
  (or pagename (setq pagename (yaoddmuse-read-pagename wikiname "Insert page")))
  ;; Insert page name.
  (insert pagename))

(defun yaoddmuse-handle-redirect (&optional wikiname pagename)
  "The handle function for redirect page.
WIKINAME is wiki name for post.
PAGENAME is page name for post."
  (let* ((table (yaoddmuse-get-pagename-table wikiname))
         (redirect-from-page (yaoddmuse-read-pagename wikiname "Redirect from page"))
         (redirect-to-page (yaoddmuse-read-pagename wikiname "Redirect to page"))
         (redirect-string (format "#REDIRECT [[%s]]" redirect-to-page))
         (redirect-summary (format "Redirect to %s" redirect-to-page)))
    ;; Modified current buffer if it is
    ;; `yaoddmuse' buffer.
    (when yaoddmuse-pagename
      (erase-buffer)
      (insert redirect-string))
    ;; Redirect.
    (yaoddmuse-post wikiname
                    redirect-from-page
                    nil
                    redirect-string
                    redirect-summary
                    current-prefix-arg)))

(defun yaoddmuse-handle-delete (&optional wikiname pagename)
  "The handle function for delete page.
WIKINAME is wiki name for delete.
PAGENAME is page name for delete."
  ;; Read page name when `pagename' is void.
  (or pagename (setq pagename (yaoddmuse-read-pagename wikiname "Delete page")))
  ;; Delete.
  (yaoddmuse-post wikiname
                  pagename
                  nil
                  "DeletedPage"
                  "Deleted"
                  current-prefix-arg))

(defun yaoddmuse-display-page (page-buffer-name)
  "Display special page buffer.
PAGE-BUFFER-NAME is buffer name of display page."
  ;; Display page when option
  ;; `yaoddmuse-display-after-get' is non-nil.
  (when yaoddmuse-display-after-get
    (set-buffer (window-buffer))
    (if (eq major-mode 'yaoddmuse-mode)
        ;; Switch to retrieve page buffer
        ;; when current major mode is `yaoddmuse-mode'.
        (switch-to-buffer page-buffer-name)
      ;; Popup retrieve page buffer
      ;; when current major mode is not `yaoddmuse-mode'.
      (pop-to-buffer page-buffer-name))))

(defun yaoddmuse-read-wikiname ()
  "Read wiki name for completing."
  (completing-read "Wiki name: " yaoddmuse-wikis nil t))

(defun yaoddmuse-read-pagename (wikiname &optional prompt)
  "Read page name of WIKINAME for completing.
By default, display \"Page name\" as prompt
unless option PROMPT is non-nil."
  (completing-read (concat (or prompt "Page name")
                           (format " (%s): " (or (yaoddmuse-pagename-at-point) "")))
                   (yaoddmuse-get-pagename-table wikiname)
                   nil nil nil nil
                   (yaoddmuse-pagename-at-point)))

(defun yaoddmuse-read-summary ()
  "Read summary for post."
  (setq yaoddmuse-last-summary
        (read-string (format "Summary (%s): " (or yaoddmuse-last-summary ""))
                     nil nil yaoddmuse-last-summary)))

(defun yaoddmuse-url (wikiname pagename)
  "Get the URL of oddmuse wiki.
WIKINAME is wiki name for view.
PAGENAME is page name for view."
  (or (ignore-errors
        (concat (yaoddmuse-get-url wikiname) "/" pagename))
      (error (format "Invalid wiki name: '%s'" wikiname))))

(defun yaoddmuse-url-diff (wikiname pagename)
  "Get the URL of oddmuse wiki.
WIKINAME is wiki name for view.
PAGENAME is page name for view."
  (or (ignore-errors
        (concat (yaoddmuse-get-url wikiname) "/?action=browse;diff=2;id=" pagename))
      (error (format "Invalid wiki name: '%s'" wikiname))))

(defun yaoddmuse-get-pagename-table (wikiname)
  "Get table from `yaoddmuse-pages-hash'.
WIKINAME is wiki name for post."
  (gethash wikiname yaoddmuse-pages-hash))

(defun yaoddmuse-get-url (wikiname)
  "Get url from `yaoddmuse-wikis'.
WIKINAME is wiki name for post."
  (cadr (assoc wikiname yaoddmuse-wikis)))

(defun yaoddmuse-get-coding (wikiname)
  "Get coding from `yaoddmuse-wikis'.
WIKINAME is wiki name for post."
  (caddr (assoc wikiname yaoddmuse-wikis)))

(defun yaoddmuse-get-post-args (wikiname)
  "Return post args for function `yaoddmuse-format'.
The WIKINAME is wiki name for post."
  (if yaoddmuse-edit-protect
      ;; Add Captcha string when option
      ;; `yaoddmuse-edit-protect' is on.
      (concat (cadddr (assoc wikiname yaoddmuse-wikis)) yaoddmuse-args-post)
    ;; Otherwise, just return `yaoddmuse-args-post'.
    yaoddmuse-args-post))

(defun yaoddmuse-get-page-buffer-name (wikiname pagename)
  "Function document.
WIKINAME is wiki name for post.
PAGENAME is page name for post."
  (format "%s:%s" wikiname pagename))

(defun yaoddmuse-get-unique-buffer ()
  "Get a buffer for temporary storage of downloaded content.
Uses `current-time' to make buffer name unique."
  (let (time-now buffer)
    (setq time-now (current-time))
    (get-buffer-create
     ;; Leave blank at front
     ;; to make user can't modified buffer.
     (format " *%s<%s-%s-%s>*"
             "yaoddmuse"
             (nth 0 time-now) (nth 1 time-now) (nth 2 time-now)))))

(defun yaoddmuse-get-library ()
  "Get library name."
  (let* ((dirs load-path)
         (suffixes (find-library-suffixes)))
    (completing-read (format "Library name (%s): " (or (yaoddmuse-region-or-thing) ""))
                     (yaoddmuse-get-library-list)
                     nil nil nil nil
                     (yaoddmuse-region-or-thing))))

(defun yaoddmuse-region-or-thing (&optional thing)
  "Return region or thing around point.
If `mark-active', return region.
If THING is non-nil, return THING around point;
otherwise return symbol around point."
  (if (and mark-active transient-mark-mode)
      (buffer-substring-no-properties (region-beginning)
                                      (region-end))
    (setq thing (or thing 'symbol))
    (ignore-errors
      (save-excursion
        (buffer-substring-no-properties (beginning-of-thing thing)
                                        (end-of-thing thing))))))

(defun yaoddmuse-get-library-list (&optional dirs string)
  "Do completion for file names passed to `locate-file'.
DIRS is directory to search path.
STRING is string to match."
  ;; Use `load-path' as path when ignore `dirs'.
  (or dirs (setq dirs load-path))
  ;; Init with blank when ignore `string'.
  (or string (setq string ""))
  ;; Get library list.
  (let ((string-dir (file-name-directory string))
        name
        names)
    (dolist (dir dirs)
      (unless dir
        (setq dir default-directory))
      (if string-dir
          (setq dir (expand-file-name string-dir dir)))
      (when (file-directory-p dir)
        (dolist (file (file-name-all-completions
                       (file-name-nondirectory string) dir))
          ;; Suffixes match `load-file-rep-suffixes'.
          (setq name (if string-dir (concat string-dir file) file))
          (if (string-match (format "^.*\\.el%s$" (regexp-opt load-file-rep-suffixes)) name)
              (add-to-list 'names name)))))
    names))

(defun yaoddmuse-get-symbol-non-blank ()
  "Return symbol between `blank'."
  (save-excursion
    (let (start end)
      (search-backward-regexp " \\|^" nil t)
      (skip-chars-forward " ")
      (setq start (point))
      (search-forward-regexp " \\|$" nil t)
      (skip-chars-backward " ")
      (setq end (point))
      (if (and start
               end
               (>= end start))
          (buffer-substring-no-properties start end)
        nil))))

(defun yaoddmuse-pagename-at-point ()
  "Page name at point."
  (let* ((pagename-wikiname (word-at-point))
         (pagename-file-link-name
          (yaoddmuse-get-symbol-non-blank)))
    (cond
     ;; Match image link, [[image:PAGENAME]]
     ((yaoddmuse-image-link-p pagename-file-link-name))
     ;; Match lisp file link, Lisp:PAGENAME.el
     ((yaoddmuse-lisp-file-link-p pagename-file-link-name))
     ;; Match Wiki name.
     ((yaoddmuse-current-free-link-contents))
     ((yaoddmuse-wikiname-p pagename-wikiname))
     ;; Try return current page name.
     (t yaoddmuse-pagename))))

(defun yaoddmuse-current-free-link-contents ()
  "Free link contents if the point is between [[ and ]]."
  (save-excursion
    (let* ((pos (point))
           (start (search-backward "[[" nil t))
           (end (search-forward "]]" nil t)))
      (and start end (>= end pos)
           (replace-regexp-in-string
            " " "_"
            (buffer-substring (+ start 2) (- end 2)))))))

(defun yaoddmuse-wikiname-p (str)
  "Whether PAGENAME is WikiName or not.
Return Wikiname or nil.
STR is string around point."
  (let (case-fold-search)
    (if (and str
             (string-match (format "^%s$" "\\<[A-Z\xc0-\xde]+[a-z\xdf-\xff]+\\([A-Z\xc0-\xde]+[a-z\xdf-\xff]*\\)+\\>") str))
        str
      nil)))

(defun yaoddmuse-lisp-file-link-p (str)
  "If STR match Lisp:PAGENAME, return PAGENAME.
Otherwise return nil."
  (let (case-fold-search)
    (if (and str
             (string-match "\\(Lisp:\\)\\([^ ]+\\.el\\)" str))
        (match-string 2 str)
      nil)))

(defun yaoddmuse-image-link-p (str)
  "If STR match [[image:PAGENAME]], return PAGENAME.
Otherwise return nil."
  (let (case-fold-search)
    (if (and str
             (string-match "\\[\\[image:\\(\\([^\\[]\\|[^\\]]\\)+\\)\\]\\]" str))
        (match-string 1 str)
      nil)))

(defun yaoddmuse-retrieve-request (method &optional data)
  "Initialize url request parameter.
METHOD is require method.
DATA is data for post."
  (setq url-request-extra-headers
        (and (string= method "POST")
             '(("Content-type: application/x-www-form-urlencoded;"))))
  (setq url-request-method method)
  (setq url-request-data data))

(defun yaoddmuse-retrieve-decode (retrieve-buffer-name coding)
  "Decode the coding with retrieve page.
RETRIEVE-BUFFER-NAME is name of retrieve buffer.
CODING is coding system for decode."
  (declare (special url-http-end-of-headers))
  (with-current-buffer (get-buffer retrieve-buffer-name)
    (insert
     (with-current-buffer yaoddmuse-retrieve-buffer
       (set-buffer-multibyte t)
       (goto-char (1+ url-http-end-of-headers))
       (decode-coding-region
        (point) (point-max)
        (coding-system-change-eol-conversion coding 'dos))
       (buffer-substring (point) (point-max))))
    (goto-char (point-min))))

(defun yaoddmuse-format (args coding &optional url)
  "Format flags.
Substitute oddmuse format flags according to `yaoddmuse-pagename',
`summary', `yaoddmuse-username',`yaoddmuse-password', `text'
Each ARGS is url-encoded with CODING.
If URL is `non-nil' return new url concat with ARGS."
  (dolist (pair '(("%t" . yaoddmuse-pagename)
                  ("%u" . yaoddmuse-username)
                  ("%m" . yaoddmuse-minor)
                  ("%p" . yaoddmuse-password)
                  ("%s" . summary)
                  ("%x" . text)
                  ))
    (when (and (boundp (cdr pair)) (stringp (symbol-value (cdr pair))))
      (setq args
            (replace-regexp-in-string
             (car pair)
             (url-hexify-string
              (encode-coding-string (symbol-value (cdr pair))
                                    coding))
             args t t))))
  (if url
      (concat url "?" args)
    args))

(defun yaoddmuse-notify-default (msg)
  "Default notify function for string MSG."
  (message "%s" msg))

(defun yaoddmuse-encode-file (file)
  "Encode FILE and return result.
Just encode file when it's suffix match `yaoddmuse-post-mime-alist'."
  (let* ((suffix (replace-regexp-in-string "^[^.]+" "" (file-name-nondirectory file)))
         (mime-type (cdr (assoc suffix yaoddmuse-post-mime-alist))))
    (if (or (string-equal suffix "")
            (not mime-type))
        (with-temp-buffer
          (insert-file-contents file)
          (buffer-string))
      (let ((coding-system-for-read 'binary)
            (coding-system-for-write 'binary)
            default-enable-multibyte-characters)
        (format "#FILE %s\n%s\n"
                mime-type
                (base64-encode-string
                 (with-temp-buffer
                   (insert-file-contents file)
                   (buffer-string))))))))

(defun yaoddmuse-decode-string (str)
  "Decode STR and return result."
  (with-temp-buffer
    (insert str)
    (string-make-unibyte
     (base64-decode-string
      (buffer-substring-no-properties
       (progn
         (goto-char (point-min))
         (forward-line +1)              ;skip mime type information
         (point))
       (point-max))))))

(defun yaoddmuse-turn-on-image-status ()
  "Turn on image stats.
Transform raw text format to image format."
  (save-excursion
    (if yaoddmuse-image-status
        (message "Already image status.")
      (let* ((data                      ;get picture data
              (yaoddmuse-decode-string
               (buffer-substring-no-properties
                (point-min)
                (point-max))))
             (image (create-image data nil t)) ;generate image
             (props                            ;generate properties
              `(display ,image
                        yank-handler
                        (image-file-yank-handler nil t)
                        intangible ,image
                        rear-nonsticky (display intangible))))
        ;; Add properties.
        (add-text-properties (point-min) (point-max) props)
        ;; Set image status.
        (setq yaoddmuse-image-status t)))))

(defun yaoddmuse-turn-off-image-status ()
  "Turn off image status.
Transform image format to raw text."
  (save-excursion
    (if yaoddmuse-image-status
        (let* ((data (buffer-substring-no-properties
                      (point-min)
                      (point-max))))
          ;; Delete image.
          (erase-buffer)
          ;; Insert raw text data.
          (insert data)
          ;; Set image status.
          (setq yaoddmuse-image-status nil))
      (message "Already raw text status."))))

(defun yaoddmuse-update-edit-status ()
  "Update edit status at mode-line.
If current is major editor mode, display [Major] at mode-line.
Otherwise display [Minor] at mode-line."
  ;; Add `yaoddmuse-edit-status' to mode-line.
  (unless (member 'yaoddmuse-edit-status-string mode-line-format)
    (setq mode-line-format (append mode-line-format
                                   (list 'yaoddmuse-edit-status-string))))
  ;; Update `yaoddmuse-edit-status' along with `yaoddmuse-minor'.
  (put 'yaoddmuse-edit-status-string 'risky-local-variable t)
  (setq yaoddmuse-edit-status-string (propertize
                                      (if yaoddmuse-minor
                                          (prog1
                                              "[Minor]"
                                            (message "Minor edit mode."))
                                        (prog1
                                            "[Major]"
                                          (message "Major edit mode.")))
                                      'face 'yaoddmuse-edit-status-face))
  ;; Update mode line.
  (force-mode-line-update))

;;;; Bug report
(defvar yaoddmuse-maintainer-mail-address
  (concat "rubiki" "tch@ru" "by-lang.org"))
(defvar yaoddmuse-bug-report-salutation
  "Describe bug below, using a precise recipe.

When I executed M-x ...

How to send a bug report:
  1) Be sure to use the LATEST version of yaoddmuse.el.
  2) Enable debugger. M-x toggle-debug-on-error or (setq debug-on-error t)
  3) Use Lisp version instead of compiled one: (load \"yaoddmuse.el\")
  4) If you got an error, please paste *Backtrace* buffer.
  5) Type C-c C-c to send.
# If you are a Japanese, please write in Japanese:-)")
(defun yaoddmuse-send-bug-report ()
  (interactive)
  (reporter-submit-bug-report
   yaoddmuse-maintainer-mail-address
   "yaoddmuse.el"
   (apropos-internal "^yaoddmuse-" 'boundp)
   nil nil
   yaoddmuse-bug-report-salutation))

(provide 'yaoddmuse)

;;; yaoddmuse.el ends here

;;; LocalWords:  yaoddmuse el oddmuse wikis TestWiki CommunityWiki StumpwmWiki
;;; LocalWords:  RatpoisonWiki OddmuseWiki username Pagename stdout pagename eg
;;; LocalWords:  HowTo pwd xc xde xdf xff WikiName builtin sgml nowiki pre tt
;;; LocalWords:  uihnscuskc sSummary caddr www urlencoded wikiname eol args pos
;;; LocalWords:  captcha DodgerBlue LawnGreen DarkRed WikiUrl noselect dirs str
;;; LocalWords:  PaleGreen benny navi ImagePage GreenYellow num screenshot msg
;;; LocalWords:  css xml gzip jpeg DeletedPage fFile nonsticky CaptchaString
;;; LocalWords:  WikiURL CodingSystem
