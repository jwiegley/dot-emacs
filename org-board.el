;;; org-board.el --- bookmarking and web archival system for Org mode.

;; Copyright (C) 2016-2017 Charles A. Roelli

;; Author: Charles A. Roelli  <charles@aurox.ch>
;; Maintainer: Charles A. Roelli  <charles@aurox.ch>
;; Created: Wed August 10, 2016
;; Last updated:  Sun  7 May 2017 17:54:12 CEST
;; Version: 1035
;; Keywords: org, bookmarks, archives
;; Homepage: https://github.com/scallywag/org-board
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Commentary:
;;
;; org-board uses `org-attach' and `wget' to provide a bookmarking and
;; web archival system  directly from an Org file.   Any `wget' switch
;; can be used  in `org-board', and presets (like user  agents) can be
;; set for easier  control.  Every snapshot is logged and  saved to an
;; automatically generated folder, and snapshots for the same link can
;; be compared using the `ztree' package (optional dependency; `ediff'
;; used if `zdiff' is not available).  Arbitrary functions can also be
;; run after an archive, allowing for extensive user customization.
;;
;; Commands defined here:
;;
;;   `org-board-archive', `org-board-archive-dry-run',
;;   `org-board-cancel', `org-board-delete-all', `org-board-diff',
;;   `org-board-diff3', `org-board-new', `org-board-open',
;;   `org-board-run-after-archive-function'.
;;
;; Functions defined here:
;;
;;   `org-board-expand-regexp-alist', `org-board-extend-default-path',
;;   `org-board-make-timestamp', `org-board-open-with',
;;   `org-board-options-handler',
;;   `org-board-test-after-archive-function',
;;   `org-board-thing-at-point', `org-board-wget-call',
;;   `org-board-wget-process-sentinel-function'.
;;
;; Variables defined here:
;;
;;   `org-board-after-archive-functions',
;;   `org-board-agent-header-alist', `org-board-archive-date-format',
;;   `org-board-default-browser', `org-board-domain-regexp-alist',
;;   `org-board-log-wget-invocation', `org-board-wget-program',
;;   `org-board-wget-show-buffer', `org-board-wget-switches'.
;;
;; Keymap defined here:
;;
;;   `org-board-keymap'.
;;
;; Functions advised here:
;;
;;   `org-thing-at-point', with `org-board-thing-at-point'.
;;
;;; Documentation:
;;
;;;; * Motivation
;;
;;  org-board is a bookmarking and web archival system for Emacs Org
;;  mode, building on ideas from Pinboard <https://pinboard.in>.  It
;;  archives your bookmarks so that you can access them even when
;;  you're not online, or when the site hosting them goes down.
;;  `wget' is used as a backend for archival, so any of its options
;;  can be used directly from org-board.  This means you can download
;;  whole sites for archival with a couple of keystrokes, while
;;  keeping track of your archives from a simple Org file.
;;
;;;; * Summary
;;
;;  In org-board, a bookmark is represented by an Org heading of any
;;  level, with a `URL' property containing one or more URLs.  Once
;;  such a heading is created, a call to `org-board-archive' creates a
;;  unique ID and directory for the entry via `org-attach', archives
;;  the contents and requisites of the page(s) listed in the `URL'
;;  property using `wget', and saves them inside the entry's
;;  directory.  A link to the (timestamped) root archive folder is
;;  created in the property `ARCHIVED_AT'.  Multiple archives can be
;;  made for each entry.  Additional options to pass to `wget' can be
;;  specified via the property `WGET_OPTIONS'.  The variable
;;  `org-board-after-archive-functions' (defaulting to nil) holds a
;;  list of functions to run after each archival operation.
;;
;;;; * User commands
;;
;;  `org-board-archive' archives the current entry, creating a unique
;;    ID and directory via `org-attach' if necessary.
;;
;;  `org-board-archive-dry-run' shows the `wget' invocation that will
;;    run for this entry in the echo area.
;;
;;  `org-board-new' prompts for a URL to add to the current entry's
;;    properties, then archives the entry immediately.
;;
;;  `org-board-delete-all' deletes all the archives for this entry by
;;    deleting the `org-attach' directory.
;;
;;  `org-board-open' opens the bookmark at point in a browser.
;;    Default to the built-in browser, `eww', and with prefix, the
;;    native operating system browser.
;;
;;  `org-board-diff' uses `zdiff' (if available) or `ediff' to
;;    recursively diff two archives of the same entry.
;;
;;  `org-board-diff3' uses `ediff' to recursively diff three archives
;;    of the same entry.
;;
;;  `org-board-cancel' cancels the current org-board archival process.
;;
;;  `org-board-run-after-archive-function' prompts for a function and
;;    an archive in the current entry, and applies the function to the
;;    archive.
;;
;;  These are all bound in the `org-board-keymap' variable (not bound
;;  to any key by default).
;;
;;;; * Customizable options
;;
;;  `org-board-wget-program' is the path to the wget program.
;;
;;  `org-board-wget-switches' are the command line options to use with
;;  `wget'.  By default these are included as:
;;
;;    "-e robots=off"      ignores robots.txt files.
;;    "--page-requisites"  downloads all page requisites (CSS, images).
;;    "--adjust-extension" add a ".html" extension where needed.
;;    "--convert-links"    convert external links to internal.
;;
;;  `org-board-agent-header-alist' is an alist mapping agent names to
;;  their respective header/user-agent arguments.  Set a
;;  `WGET_OPTIONS' property to a key of this alist (say,
;;  `Mac-OS-10.8') and org-board will replace the key with its
;;  corresponding value before calling wget. This is useful for some
;;  sites that refuse to serve pages to `wget'.
;;
;;  `org-board-wget-show-buffer' controls whether the archival process
;;  buffer is shown in a window (defaults to true).
;;
;;  `org-board-log-wget-invocation' controls whether to log the
;;  archival process command in the root of the archival directory
;;  (defaults to true).
;;
;;  `org-board-domain-regexp-alist' applies certain options when a
;;  domain matches a regular expression.  See the docstring for
;;  details.  As an example, this is used to make sure that `wget'
;;  does not send a User Agent string when archiving from Google
;;  Cache, which will not normally serve pages to it.
;;
;;  `org-board-after-archive-functions' (default nil) holds a list of
;;  functions to run after an archival takes place.  This is intended
;;  for user extensions to `org-board'.  The functions receive three
;;  arguments: a list of URLs downloaded, the folder name where they
;;  were downloaded and the process filter event string (see the Elisp
;;  manual for details on the possible values of this string).  For an
;;  example use of `org-board-after-archive-functions', see the
;;  "Example usage" section below.
;;
;;;; * Known limitations
;;
;;  Options like "--header: 'Agent X" cannot be specified as
;;  properties, because the property API splits on spaces, and such an
;;  option has to be passed to `wget' as one argument.  To work around
;;  this, add these types of options to `org-board-agent-header-alist'
;;  instead, where the property API is not involved.
;;
;;  At the moment, only one archive can be done at a time.
;;
;;;; * Example usage
;;
;;;;; ** Archiving
;;
;;  I recently found a list of articles on linkers that I wanted to
;;  bookmark and keep locally for offline reading.  In a dedicated org
;;  file for bookmarks I created this entry:
;;
;;  ** TODO Linkers (20-part series)
;;  :PROPERTIES:
;;  :URL:          http://a3f.at/lists/linkers
;;  :WGET_OPTIONS: --recursive -l 1 --span-hosts
;;  :END:
;;
;;  Where the `URL' property is a page that already lists the URLs
;;  that I wanted to download.  I specified the recursive property for
;;  `wget' along with a depth of 1 ("-l 1") so that each linked page
;;  would be downloaded.  With point inside the entry, I run "M-x
;;  org-board-archive".  An `org-attach' directory is created and
;;  `wget' starts downloading the pages to it.  Afterwards, the end
;;  the entry looks like this:
;;
;;  ** TODO Linkers (20-part series)
;;  :PROPERTIES:
;;  :URL:          http://a3f.at/lists/linkers
;;  :WGET_OPTIONS: --recursive -l 1 --span-hosts
;;  :ID:           D3BCE79F-C465-45D5-847E-7733684B9812
;;  :ARCHIVED_AT:  [2016-08-30-Tue-15-03-56]
;;  :END:
;;
;;  The value in the `ARCHIVED_AT' property is a link that points to
;;  the root of the timestamped archival directory.  The ID property
;;  was automatically generated by `org-attach'.
;;
;;;;; ** Diffing
;;
;;  You can diff between two archives done for the same entry using
;;  `org-board-diff', so you can see how a page has changed over time.
;;  The diff recurses through the directory structure of an archive
;;  and will highlight any changes that have been made.  `ediff' is
;;  used if `zdiff' is not available (both are capable of recursing
;;  through a directory structure, but `zdiff' is possibly more
;;  intuitive to use).  `org-board-diff3' also offers diffing between
;;  three different archive directories.
;;
;;;;; ** `org-board-after-archive-functions'
;;
;;  `org-board-after-archive-functions' is a list of functions run
;;  after an archive is finished.  You can use it to do anything you
;;  like with newly archived pages.  For example, you could add a
;;  function that copies the new archive to an external hard disk, or
;;  opens the archived page in your browser as soon as it is done
;;  downloading.  You could also, for instance, copy all of the media
;;  files that were downloaded to your own media folder, and pop up a
;;  Dired buffer inside that folder to give you the chance to
;;  organize them.
;;
;;  Here is an example function that copies the archived page to an
;;  external service called `IPFS' <http://ipfs.io/>, a decentralized
;;  versioning and storage system geared towards web content (thanks
;;  to Alan Schmitt):
;;
;;  (defun org-board-add-to-ipfs (urls output-folder event &rest _rest)
;;    "Add the downloaded site to IPFS."
;;    (unless (string-match "exited abnormally" event)
;;      (let* ((parsed-url (url-generic-parse-url (car urls)))
;;             (domain (url-host parsed-url))
;;             (path (url-filename parsed-url))
;;             (output (shell-command-to-string
;;  		     (concat "ipfs add -r "
;;  			     (concat output-folder domain))))
;;             (ipref
;;  	     (nth 1 (split-string
;;  		     (car (last (split-string output "\n" t))) " "))))
;;        (with-current-buffer (get-buffer-create "*org-board-post-archive*")
;;          (princ (format "your file is at %s\n"
;;  			(concat "http://localhost:8080/ipfs/" ipref path))
;;  		(current-buffer))))))
;;
;;  (eval-after-load "org-board"
;;    '(add-hook 'org-board-after-archive-functions 'org-board-add-to-ipfs))
;;
;;  Note that for forward compatibility, it's best to add to a final
;;  `&rest' argument to every function listed in
;;  `org-board-after-archive-functions', since a future update may
;;  provide each function with additional arguments (like a marker
;;  pointing to a buffer position where the archive was initiated, for
;;  example).
;;
;;  For more information on `org-board-after-archive-functions', see
;;  its docstring and the docstring of
;;  `org-board-test-after-archive-function'.
;;
;;  You can also interactively run an after-archive function with the
;;  command `org-board-run-after-archive-function'.  See its docstring
;;  for details.
;;
;;;;
;;;; * Getting started
;;
;;;;; ** Installation
;;
;;  There are two ways to install the package.  One way is to clone
;;  this repository and add the directory to your load-path manually.
;;
;;  (add-to-list 'load-path "/path/to/org-board")
;;  (require 'org-board)
;;
;;  Alternatively, you can download the package directly from Emacs
;;  using MELPA <https://github.com/melpa/melpa>.  M-x
;;  package-install RET org-board RET will take care of it.
;;
;;;; ** Keybindings
;;
;;  The following keymap is defined in `org-board-keymap':
;;
;;  | Key | Command                              |
;;  | a   | org-board-archive                    |
;;  | r   | org-board-archive-dry-run            |
;;  | n   | org-board-new                        |
;;  | k   | org-board-delete-all                 |
;;  | o   | org-board-open                       |
;;  | d   | org-board-diff                       |
;;  | 3   | org-board-diff3                      |
;;  | c   | org-board-cancel                     |
;;  | x   | org-board-run-after-archive-function |
;;  | O   | org-attach-reveal-in-emacs           |
;;  | ?   | Show help for this keymap.           |
;;
;;  To install the keymap give it a prefix key, e.g.:
;;
;;  (global-set-key (kbd "C-c o") org-board-keymap)
;;
;;  Then typing `C-c o a' would run `org-board-archive', for example.
;;
;;;; * Miscellaneous
;;
;;  The location of `wget' should be picked up automatically from the
;;  `PATH' environment variable.  If it is not, then the variable
;;  `org-board-wget-program' can be customized.
;;
;;  Other options are already set so that archiving bookmarks is done
;;  pretty much automatically.  With no `WGET_OPTIONS' specified, by
;;  default `org-board-archive' will just download the page and its
;;  requisites (images and CSS), and nothing else.
;;
;;;;; ** Support for org-capture from Firefox (thanks to Alan Schmitt):
;;
;;  On the Firefox side, install org-capture from here:
;;
;;    http://chadok.info/firefox-org-capture/
;;
;;  Alternatively, you can do it manually by following the
;;  instructions here:
;;
;;    http://weblog.zamazal.org/org-mode-firefox/
;;      (in the “The advanced way” section)
;;
;;  When org-capture is installed, add `(require 'org-protocol)' to
;;  your init file (`~/.emacs').
;;
;;  Then create a capture template like this:
;;
;;    (setq org-board-capture-file "my-org-board.org")
;;
;;    (setq org-capture-templates
;;          `(...
;;            ("c" "capture through org protocol" entry
;;              (file+headline ,org-board-capture-file "Unsorted")
;;              "* %?%:description\n:PROPERTIES:\n:URL: %:link\n:END:\n\n Added %U")
;;            ...))
;;
;;  And add a hook to `org-capture-before-finalize-hook':
;;
;;    (defun do-org-board-dl-hook ()
;;      (when (equal (buffer-name)
;;              (concat "CAPTURE-" org-board-capture-file))
;;        (org-board-archive)))
;;
;;    (add-hook 'org-capture-before-finalize-hook 'do-org-board-dl-hook)
;;
;;;; * Acknowledgements
;;
;;  Thanks to Alan Schmitt for the code to combine `org-board' and
;;  `org-capture', and for the example function used in the
;;  documentation of `org-board-after-archive-functions' above.
;;
;;; Code:

(require 'find-lisp)
(require 'org-attach)
(require 'org-pcomplete)		; `pcomplete/org-mode/org-board/wget'.
(require 'url)				; See `org-board-open'.
(require 'ztree nil t)			; Used for `ztree-diff', not required.

(defgroup org-board nil
  "Options concerning the bookmarking archival system."
  :tag "Org Board"
  :group 'org
  :group 'hypermedia
  :prefix "org-board-"
  :link '(url-link :tag "GitHub repository"
		   "https://github.com/scallywag/org-board")
  :link `(url-link :tag "Send Bug Report"
		   ,(concat "mailto:" "charles@aurox.ch" "?subject=\
org-board bug: \
&body=Describe bug here, starting with `emacs -Q'.  \
Don't forget to mention your Emacs and `org-board' versions."))
  :link '(emacs-commentary-link :tag "Commentary" "org-board"))


(defcustom org-board-wget-program (executable-find "wget")
  "The absolute path to the `wget' binary."
  :type 'file)

(defcustom org-board-wget-switches '("-e robots=off"
				     "--page-requisites"
				     "--adjust-extension"
				     "--convert-links")
  "The default switches to pass to `wget'.

If you change any of these, you may encounter unexpected
behavior when opening or viewing archived pages."
  :type '(repeat string))

(defcustom org-board-wget-show-buffer t
  "Show the buffer with the output of `wget' while it is running.

If `wget' exited abnormally, the buffer will be shown
regardless."
  :type 'boolean)

(defcustom org-board-log-wget-invocation t
  "Log the wget invocation to org-board-{ID}.log.

The log is kept in the root of the timestamped archival folder.

You can use it as a shell script if you want to run it on another
machine, for example."
  :type 'boolean)

(defcustom org-board-archive-date-format
  (if (or (eq system-type 'windows-nt)
	  (eq system-type 'ms-dos)
	  (eq system-type 'cygwin))
      'hyphenate
    'iso-8601)
  "String format for the archive folder name.  Can be either the
symbol `hyphenate', or `iso-8601'.  `hyphenate' is used on
systems not supporting colons in filenames, while `iso-8601' is
used everywhere else."
  :type '(choice (const :tag "hyphenate: like 2016-08-18-Thu-20-19-02"
			hyphenate)
		 (const :tag "iso-8601: like 2017-02-06T17:37:11+0100"
			iso-8601)))

(defcustom org-board-agent-header-alist
  '(("Mac-OS-10.6" . "--header=\"Accept: */*\" \
--user-agent=\"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_6_8) \
AppleWebKit/534.59.10 (KHTML, like Gecko) Version/5.1.9 \
Safari/534.59.10")
    ("Mac-OS-10.8" . "--header=\"Accept: text/html\" \
--user-agent=\"Mozilla/5.0 (Macintosh; Intel Mac OS X 10.8; rv:21.0) \
Gecko/20100101 Firefox/21.0\"")
    ("No-Agent" . "--user-agent=\"\""))

  "Alist of common browser headers for use by `wget' according to device.

Use the key of the alist to activate the corresponding
headers (in `WGET_OPTIONS')."
  :type '(alist :key-type string :value-type string))

(defcustom org-board-default-browser
  (if (require 'eww nil t)
      'eww
    'system)
  "Default browser for opening archived web pages.

`eww' is used if available, otherwise the page will be opened in
the system browser."
  :type '(choice (const :tag "Use `eww'" eww)
		 (const :tag "Use the native OS browser" system)))

(defvar org-board-pcomplete-wget
  `("--execute" "--bind-address=" "--bind-dns-address=" "--dns-servers="
    "--tries=" "--no-clobber" "--backups=" "--continue" "--start-pos="
    "--timestamping" "no-if-modified-since" "no-use-server-timestamps"
    "--server-response" "--spider" "--timeout=" "--dns-timeout="
    "--connect-timeout=" "--read-timeout=" "--limit-rate=" "--wait="
    "--waitretry=" "--random-wait" "--no-proxy" "--quota="
    "--no-dns-cache" "--restrict-file-names=" "--inet4-only" "--inet6only"
    "--prefer-family=" "--retry-connrefused" "--user=" "--password="
    "--no-iri" "--local-encoding" "--remote-encoding" "--unlink"
    "--no-directories" "--force-directories" "--no-host-directories"
    "--protocol-directories" "--cut-dirs=" "--default-page="
    "--http-user=" "--http-password=" "--no-http-keep-alive" "--no-cache"
    "--no-cookies" "--load-cookies" "--save-cookies" "--keep-session-cookies"
    "--ignore-length" "--max-redirect=" "--proxy-user=" "--proxy-password="
    "--referer=" "--save-headers" "--content-disposition" "--content-on-error"
    "--trust-server-names" "--auth-no-challenge" "--secure-protocol="
    "--https-only" "--no-check-certificate" "--certificate="
    "--certificate-type=" "--private-key=" "--private-key-type="
    "--ca-certificate=" "--ca-directory=" "--crl-file=" "--pinnedpubkey="
    "--random-file=" "--egd-file=" "--no-hsts" "--hsts-file="
    "--ftp-user=" "--ftp-password=" "--no-remove-listing" "--no-glob"
    "--no-passive-ftp" "--preserve-permissions" "--retr-symlinks"
    "--ftps-implicit" "--no-ftps-resume-ssl" "--ftps-clear-data-connection"
    "--ftps-fallback-to-ftp" "--recursive" "--level=" "--delete-after"
    "--convert-file-only" "--backup-converted" "--mirror" "--strict-comments"
    "--accept" "--reject" "--accept-regex" "--reject-regex" "--regex-type"
    "--domains=" "--exclude-domains" "--follow-ftp" "--follow-tags="
    "--ignore-tags=" "--ignore-case" "--span-hosts" "--relative"
    "--include-directories=" "--exclude-directories" "--no-parent"
    ,@(mapcar #'car org-board-agent-header-alist)))

(defun pcomplete/org-mode/org-board/wget ()
  "Complete `WGET_OPTIONS'."
  (while (pcomplete-here
	  org-board-pcomplete-wget)))

(when (and (fboundp 'advice-add) (fboundp 'org-thing-at-point))
  (advice-add 'org-thing-at-point :before-until #'org-board-thing-at-point))

(defun org-board-thing-at-point ()
  "Match a `WGET_OPTIONS' property."
  ;; See (find-library "org-pcomplete").
  (let ((line-to-here (buffer-substring (point-at-bol) (point))))
    (when (string-match "\\`[ \t]*:WGET_OPTIONS:[ \t]+" line-to-here)
      (cons "org-board/wget" nil))))

(defcustom org-board-domain-regexp-alist
  ;; Google doesn't like `wget'!
  '(("webcache\\.googleusercontent\\.com.*" . ("No-Agent")))

  "If a URL matches a regexp here, add the corresponding list of
`WGET_OPTIONS' before archiving.  They can either be defined in
`org-board-agent-header-alist' or they can be standard options
for `wget', like `--no-check-certificate'."
  :type '(alist :key-type regexp :value-type (list string)))

(defvar org-board-after-archive-functions nil
  "Special hook run after archiving a site.
Each function there is called with three arguments:

 - a list of URLs downloaded,
 - the folder name where they were downloaded,
 - and the process filter event string.

Generally, if the event string matches \"exited abnormally\" then
something in the archive process went wrong.  The functions added
to this special hook should check for this case.

If the event string does not match \"exited abnormally\" then it
can be assumed that the download completed successfully.  If you
want to be completely sure, check that the string matches
\"finished\\n\" -- see (info \"(elisp) Sentinels\").

For interactive development of functions meant for
`org-board-after-archive-functions', see
`org-board-run-after-archive-function'.")

(defun org-board-test-after-archive-function (urls output-folder
                                                   event &rest _rest)
  "Use this function as a template for designing your own post-archive
functions.

To add a function to `org-board-after-archive-functions', use the
following code:

\(add-hook 'org-board-after-archive-functions 'function-name).

Please note the `&rest' argument to the archive function.  This
is for forward compatibility with `org-board' releases that might
one day make use of further arguments passed to
`org-board-after-archive-functions'."

  (with-current-buffer (get-buffer-create "*org-board-post-archive*")
    (princ "Downloaded " (current-buffer))
    (princ urls (current-buffer))
    (princ ".\n" (current-buffer))))

;;;###autoload
(defvar org-board-keymap
  (let ((keymap (make-sparse-keymap)))
    (define-key keymap "a" 'org-board-archive)
    (define-key keymap "r" 'org-board-archive-dry-run)
    (define-key keymap "n" 'org-board-new)
    (define-key keymap "k" 'org-board-delete-all)
    (define-key keymap "o" 'org-board-open)
    (define-key keymap "d" 'org-board-diff)
    (define-key keymap "3" 'org-board-diff3)
    (define-key keymap "c" 'org-board-cancel)
    (define-key keymap "x" 'org-board-run-after-archive-function)
    (define-key keymap "O" 'org-attach-reveal-in-emacs)
    keymap)
  "Keymap for org-board usage.")


;;; Internal functions

;; `cl-copy-list' from `cl-lib', used in `org-board-archive'.
(defun org-board-copy-list (list)
  "Return a copy of LIST, which may be a dotted list.
The elements of LIST are not copied, just the list structure itself."
  (if (consp list)
      (let ((res nil))
	(while (consp list) (push (pop list) res))
	(prog1 (nreverse res) (setcdr res list)))
    (car list)))

(defun org-board-wget-process-sentinel-function (process event)
  "Outputs debug info to org-board buffer when wget exits abnormally.

Prints success message to echo area otherwise."

  (if (string-match-p "exited abnormally" event)
      ;; If the process did not exit successfully, we copy the process
      ;; buffer output and append the event string to it, to present
      ;; the error to the user.
      (let ((inhibit-read-only t)
	    (current-buffer-contents
	     (with-current-buffer (process-buffer process)
	       (buffer-string))))
	(with-output-to-temp-buffer (process-buffer process)
	  (princ (concat current-buffer-contents
			 (combine-and-quote-strings
			  (process-command process))
			 " " event))))
    ;; Else, if the process exited successfully, inform the user.
    (if (string-match-p "finished" event)
	(message "org-board finished archive for %s"
		 (process-get process 'org-entry))))
  (when org-board-log-wget-invocation
    (ignore-errors
      (let ((wget-output-directory
	     (process-get process 'wget-output-directory))
	    (org-id-token
	     (process-get process 'org-id)))
	(write-region (combine-and-quote-strings
		       (process-command process))
		      nil (concat wget-output-directory
				  "org-board-"
				  org-id-token ".log")))))
  (run-hook-with-args 'org-board-after-archive-functions
                      (process-get process 'urls)
                      (process-get process 'wget-output-directory)
                      event))

(defun org-board-wget-call (path directory args site)
  "Start `wget' in a temporary buffer.

PATH is the absolute path to the `wget' binary.
DIRECTORY is the (unique) directory to save the archived files.
ARGS is a list of strings each containing a command line argument.
SITE is a URL list to archive.

Returns the process associated with `wget'."

  (let* ((output-directory-option
          (concat "--directory-prefix=" directory "/"))
         (output-buffer-name "org-board-wget-call")
         (process-arg-list (append (list "org-board-wget-process"
                                         output-buffer-name
                                         path
                                         output-directory-option)
                                   org-board-wget-switches
                                   args
                                   site))
         (wget-process (apply 'start-process process-arg-list)))
    (if org-board-wget-show-buffer
        (with-output-to-temp-buffer output-buffer-name
          (set-process-sentinel
           wget-process
           'org-board-wget-process-sentinel-function))
      (set-process-sentinel
       wget-process
       'org-board-wget-process-sentinel-function))
    wget-process))



;;;###autoload
(defun org-board-archive ()
  "Archive the URL given by the current entry's `URL' property.

The attachment directory and the unique ID are created if not
already present.  See the docstring of `org-attach-dir'.

Every snapshot is stored in its own timestamped folder, and is
added as a link in the `ARCHIVED_AT' property."

  (interactive)
  (org-board-expand-regexp-alist)
  (let* ((attach-directory (org-attach-dir t))
         (urls (org-entry-get-multivalued-property (point) "URL"))
         (options
          (org-board-options-handler
           (org-entry-get-multivalued-property (point) "WGET_OPTIONS")))
         (timestamp (org-board-make-timestamp))
         (output-directory (concat (file-name-as-directory attach-directory)
                                   (file-name-as-directory timestamp)))
         (org-id-token (org-id-get))
         (link-to-output (concat "[[file:" output-directory "]["
                                 timestamp "]]"))
         (wget-process (org-board-wget-call org-board-wget-program
                                            output-directory
                                            options
                                            urls)))
    (process-put wget-process 'org-entry
                 (org-display-outline-path nil t "/" t))
    (process-put wget-process 'wget-output-directory
                 output-directory)
    (process-put wget-process 'org-id
                 org-id-token)
    (process-put wget-process 'urls
                 (org-board-copy-list urls))
    (org-entry-add-to-multivalued-property (point) "ARCHIVED_AT"
                                           link-to-output)))

;;;###autoload
(defun org-board-archive-dry-run ()
  "Show the `wget' invocation that will be run, in the echo area.

This command takes into account the current options.  It also
creates an `org-attach' directory and property if not already
present."
  (interactive)
  ;; Duplicated code here, the `let' bindings should go in a macro
  ;; instead.
  (let* ((attach-directory (org-attach-dir t))
	 (urls (org-entry-get-multivalued-property (point) "URL"))
	 (options
	  (org-board-options-handler
	   (org-entry-get-multivalued-property (point) "WGET_OPTIONS")))
	 (timestamp (org-board-make-timestamp))
	 (output-directory (concat attach-directory "/"
				   timestamp "/"))
	 (output-directory-option
	  (concat "--directory-prefix=" output-directory "/")))
    (message "%s" (concat org-board-wget-program " " output-directory-option
		     " " (mapconcat 'princ org-board-wget-switches " ")
		     " " (mapconcat 'princ options " ")
		     " " (mapconcat 'princ urls " ")))))

;;;###autoload
(defun org-board-expand-regexp-alist ()
  "Add to `WGET_OPTIONS' w.r.t. `org-board-domain-regexp-alist'."
  (let* ((urls (org-entry-get-multivalued-property (point) "URL")))
    (dolist (url urls)
      (dolist (regexp-option-elem org-board-domain-regexp-alist)
	(if (string-match-p (car regexp-option-elem) url)
	    (dolist (org-board-option (cdr regexp-option-elem))
	      (org-entry-add-to-multivalued-property (point)
						     "WGET_OPTIONS"
						     org-board-option)))))))

;;;###autoload
(defun org-board-make-timestamp ()
  "Return a timestamp suitable for the native operating system.

See also `org-board-archive-date-format'."
  (cond ((eq org-board-archive-date-format 'hyphenate)
	 (format-time-string "%Y-%m-%d-%a-%H-%M-%S"
			     (current-time)))
	((or (eq org-board-archive-date-format 'iso-8601) t)
	 (format-time-string "%FT%T%z"))))

;;;###autoload
(defun org-board-options-handler (wget-options)
  "Expand `WGET_OPTIONS' w.r.t. `org-board-agent-header-alist'."
  (let ((wget-options-expanded))
    (mapc #'(lambda (wget-option)
                (let ((expanded (assoc wget-option
                                       org-board-agent-header-alist)))
                  (if expanded
                      (add-to-list 'wget-options-expanded (cdr expanded) t)
                    (add-to-list 'wget-options-expanded wget-option t))))
            wget-options)
    wget-options-expanded))

;;;###autoload
(defun org-board-delete-all ()
  "Delete all archives for the entry at point.

The parent attachment directory is not removed.  Note that ALL
attachments to the entry are deleted."
  (interactive)
  (org-attach-delete-all)
  (org-entry-delete (point) "ARCHIVED_AT"))

;;;###autoload
(defun org-board-open (arg)
  "Open the archived page pointed to by the `URL' property.

With prefix argument, temporarily flip the value of
`org-board-default-browser' and open there instead.

If that does not work, open a list of HTML files from the
most recent archive, in Dired."
  (interactive "P")
  (let* ((link (car (last
		     (org-entry-get-multivalued-property
		      (point) "ARCHIVED_AT"))))
         (folder
          (progn
            (string-match "^\\[\\[file:\\(.*\\)\\]\\[.*\\]\\]$" link)
            (match-string-no-properties 1 link)))
	 (urls
	  (org-entry-get-multivalued-property (point) "URL")))
    (dolist (url-string urls)
      (let* ((url-parsed (url-generic-parse-url url-string))
	     (url-host-string (url-host url-parsed))
	     (url-path-string (url-filename url-parsed))
	     (url-combined-string (concat folder
					  url-host-string
					  url-path-string))
	     (url-filesystem-guess (if (string=
					(substring
					 url-combined-string -1)
					"/")
				       ;; `url-combined-string' may
				       ;; already have `.html' at the
				       ;; end of it.  But if it
				       ;; doesn't, extend it to end
				       ;; with `index.html'.
				       (org-board-extend-default-path
					url-combined-string)
				     url-combined-string)))
	(unless (eq (org-board-open-with url-filesystem-guess arg) 0)
	  ;; If the above didn't find our HTML file, try appending
	  ;; `.html' to the name and open that instead.  If that
	  ;; doesn't work, throw the job to `find-name-dired'.
	  (let* ((url-html-appended-string
		  (concat url-combined-string ".html")))
	    ;; Should refactor this repetitive opening strategy to a
	    ;; `while' loop instead.
	    (unless (eq (org-board-open-with
			 url-html-appended-string arg)
			0)
	      (find-name-dired folder "*.html"))))))))

;;;###autoload
(defun org-board-open-with (filename-string arg)
  "Open visited file in default external program, return exit code."
  (when filename-string
    ;; With an argument and `system' for `org-board-default-browser',
    ;; or no argument and `eww' for `org-board-default-browser', try
    ;; to open the file in `eww' and return 0 (success), and if an
    ;; error occurs, throw it back to the user.
    (if (or (and arg (eq org-board-default-browser 'system))
            (and (not arg) (eq org-board-default-browser 'eww)))
	(condition-case nil
	    (progn
	      (eww-open-file filename-string)
	      0)
	  (error 1))
      ;; Otherwise, use `open' on a Mac, `xdg-open' on GNU/Linux and
      ;; BSD, and prompt for a shell command otherwise.  (What would
      ;; be the best for Windows?)  Return the exit code of the
      ;; process call.
      (call-process (cond
                     ((eq system-type 'darwin) "open")
                     ((member system-type
			      '(gnu gnu/linux gnu/kfreebsd)) "xdg-open")
                     (t (read-shell-command "Open current file with: ")))
		    nil nil nil
		    filename-string))))

;;;###autoload
(defun org-board-extend-default-path (filename-string)
  "Extend a filename to end in `/index.html'.

Examples: `aurox.ch'  => `aurox.ch/index.html'
          `aurox.ch/' => `aurox.ch/index.html'."
  (if (string= (substring filename-string -1) "/")
      (concat filename-string "index.html")
    (concat filename-string "/index.html")))

;;;###autoload
(defun org-board-new (url)
  "Ask for a URL, create a property with it, and archive it."
  (interactive (list (completing-read "URL: " nil)))
  (org-entry-add-to-multivalued-property nil "URL" url)
  (org-board-archive))

;;;###autoload
(defun org-board-diff (archive1 archive2)
  "Recursively diff two archives from the same entry."
  (interactive
   (let ((dir-default (org-attach-dir)))
     (list (read-directory-name "Directory A to compare: "
                                dir-default nil 'must-match)
           (read-directory-name "Directory B to compare: "
                                dir-default nil 'must-match))))
  ;; We use `ztree' if it's available.  It doesn't do anything that
  ;; `ediff' can't, but it is more user-friendly and faster to use.
  (if (require 'ztree nil t)
      (ztree-diff archive1 archive2)
    (ediff-directories archive1 archive2 nil)))

;;;###autoload
(defun org-board-diff3 (archive1 archive2 archive3)
  "Recursively diff three archives from the same entry."
  (interactive
   (let ((dir-default (org-attach-dir)))
     (list (read-directory-name "Directory A to compare: "
                                dir-default nil 'must-match)
           (read-directory-name "Directory B to compare: "
                                dir-default nil 'must-match)
           (read-directory-name "Directory C to compare: "
                                dir-default nil 'must-match))))
  (ediff-directories3 archive1 archive2 archive3 nil))

;;;###autoload
(defun org-board-cancel ()
  "Cancel the current org-board archival process.

Leave the output buffer intact."
  (interactive)
  ;; Ideally, we should remove the link to the archive too.  But what
  ;; if the user wants to keep the partial download and resume it
  ;; later?  Maybe with a prefix argument only.
  (kill-process "org-board-wget-process"))

(defun org-board-run-after-archive-function (arg function archive)
  "Interactively run a function on an archive.

Run a function on an archive in the entry at point.  The function
should have the same format as recommended for
`org-board-after-archive-functions'.  Prompt first for the
function to run, and then the name of the archive folder to run
it on.  With a prefix ARG, only prompt for functions already
present inside `org-board-after-archive-functions'.

The function is provided with a successful exit string, as if the
archive has just been finished.

This is useful for debugging functions added to
`org-board-after-archive-functions', or for interactively running
post-archive functions on select bookmarks."
  (interactive
   (list
    ;; ARG, not yet used by the function body.
    current-prefix-arg
    ;; FUNCTION
    (intern (completing-read "Function name: "
			     (if current-prefix-arg
				 org-board-after-archive-functions
			       obarray)
			     'functionp 'REQUIRE-MATCH))
    ;; ARCHIVE
    (read-directory-name
     "Archive directory (resembles a timestamp): "
     (org-attach-dir) nil 'must-match)))
  (let ((urls (org-entry-get-multivalued-property (point) "URL")))
    (funcall function urls archive
	     ;; See (info "(elisp) Sentinels").
	     "finished\n")))

(provide 'org-board)

;;; org-board.el ends here
