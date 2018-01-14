;;; aria2.el --- Control aria2c commandline tool from Emacs

;; Copyright (c) 2014 Łukasz Gruner

;; Author: Łukasz Gruner <lukasz@gruner.lu>
;; Maintainer: Łukasz Gruner <lukasz@gruner.lu>
;; Version: 2
;; Package-Version: 20170427.134
;; Package-X-Original-Version: 20141107.1517
;; Package-Requires: ((emacs "24.4"))
;; URL: https://bitbucket.org/ukaszg/aria2-mode
;; Created: 19/10/2014
;; Keywords: download bittorrent aria2

;; This file is not part of Emacs.


;; This work ‘as-is’ we provide.
;; No warranty express or implied.
;; We’ve done our best,
;; to debug and test.
;; Liability for damages denied.
;;
;; Permission is granted hereby,
;; to copy, share, and modify.
;; Use as is fit,
;; free or for profit.
;; These rights, on this notice, rely.


;;; Commentary:

;;; Code:

(require 'eieio-base)
(require 'json)
(require 'url)
(require 'subr-x)
(require 'tabulated-list)

(unless (fboundp 'alist-get)
  (defun alist-get (key alist &optional default remove)
    "Get the value associated to KEY in ALIST.
DEFAULT is the value to return if KEY is not found in ALIST.
REMOVE, if non-nil, means that when setting this element, we should
remove the entry if the new value is `eql' to DEFAULT."
    (ignore remove) ;;Silence byte-compiler.
    (let ((x (assq key alist)))
      (if x (cdr x) default))))

;;; Customization variables start here.

(defgroup aria2 nil
  "An interface for aria2c command."
  :group 'external
  :group 'execute
  :prefix "aria2-")

(defcustom aria2-kill-process-on-emacs-exit nil
  "Whether aria2c should be stopped when exiting Emacs.
If nil Emacs will reattach itself to the process on entering downloads list."
  :type 'boolean
  :group 'aria2)

(defcustom aria2-list-buffer-name "*aria2: downloads list*"
  "Name of buffer to use when showing downloads list."
  :type '(string :tag "Buffer name")
  :group 'aria2)

(defcustom aria2-executable (executable-find "aria2c")
  "Full path to aria2c binary."
  :type 'file
  :group 'aria2)

(defcustom aria2-session-file (expand-file-name "aria2c.session" user-emacs-directory)
  "Name of session file.  Will be used with \"--save-session\" and \"--input-file\" options."
  :type 'file
  :group 'aria2)

(defcustom aria2-download-directory (or (getenv "XDG_DOWNLOAD_DIR") (expand-file-name "~/"))
  "Default directory to store downloaded files."
  :type 'directory
  :group 'aria2)

(defcustom aria2-rcp-listen-port 6800
  "Port on which JSON RCP server will listen."
  :type '(integer :tag "Http port")
  :group 'aria2)

(defcustom aria2-custom-args nil
  "Additional arguments for aria2c.  This should be a list of strings.  See aria2c manual for supported options."
  :type '(repeat (string :tag "Commandline argument."))
  :group 'aria2)

(defcustom aria2-add-evil-quirks nil
  "If t adds aria2-mode to emacs-states, and binds `C-w'.")

(defvar aria2--debug nil
  "Should json commands and replies be printed.")

(defconst aria2--cc-file
  (expand-file-name "aria2-controller.eieio" user-emacs-directory)
  "File used to persist controller status between Emacs restarts.")

;;; Faces definitions start here.

(defface aria2-file-face `((t :inherit mode-line-buffer-id))
  "Face for download name."
  :group 'aria2
  :group 'face)

(defface aria2-status-face `((t :inherit font-lock-constant-face))
  "Face for status."
  :group 'aria2
  :group 'face)

(defface aria2-type-face `((t :inherit font-lock-builtin-face))
  "Face for download type."
  :group 'aria2
  :group 'face)

(defface aria2-done-face `((t :inherit font-lock-doc-face))
  "Face for % done."
  :group 'aria2
  :group 'face)

(defface aria2-download-face `((t :inherit font-lock-string-face))
  "Face for download speed."
  :group 'aria2
  :group 'face)

(defface aria2-upload-face `((t :inherit font-lock-comment-face))
  "Face for upload speed."
  :group 'aria2
  :group 'face)

(defface aria2-error-face `((t :inherit font-lock-warning-face))
  "Face for error messages."
  :group 'aria2
  :group 'face)

(defface aria2-modeline-key-face `((t :inherit font-lock-warning-face))
  "Face for shortcut hints displayed in mode-line."
  :group 'aria2
  :group 'face)

(defface aria2-modeline-mouse-face `((t :inherit default
                                        :box (:line-width 2 :style pressed-button)
                                        :inverse-video t
                                        :weight bold))
  "Face for shortcuts hoovered by a pointer."
  :group 'aria2
  :group 'face)

;;; Utils start here.

(defsubst aria2--url ()
  "Format URL."
  (format "http://localhost:%d/jsonrpc" aria2-rcp-listen-port))

(defun aria2--base64-encode-file (path)
  "Return base64-encoded string with contents of file on PATH."
  (unless (file-exists-p path)
    (signal 'aria2-err-file-doesnt-exist '(path)))
  (with-current-buffer (find-file-noselect path)
    (unwind-protect
        (base64-encode-string (buffer-string) t)
      (kill-buffer))))

;; Before Emacs 26 `process-attributes' is not supported on Darwin.
(if (or (not (eq system-type 'darwin))
        (and (eq system-type 'darwin) (version<= "26" emacs-version)))
    (defun aria2--is-aria-process-p (pid)
      "Return t if `process-attributes' of PID belongs to aria."
      (let ((proc-attr (process-attributes pid)))
        (and
         (string= "aria2c" (alist-get 'comm proc-attr))
         (string= (user-real-login-name) (alist-get 'user proc-attr)))))
  (defun aria2--is-aria-process-p (f &rest ARG)
    "Returns t if PID belongs to aria."
    (let ((pid (car ARG)))
      (eq pid (string-to-number
               (shell-command-to-string
                (format "pgrep -u %s aria2c" (user-real-login-name))))))))

;;; Error definitions start here

(define-error 'aria2-err-too-many-magnet-urls  "Only one magnet link per download is allowed" 'user-error)
(define-error 'aria2-err-file-doesnt-exist     "File doesn't exist"                           'user-error)
(define-error 'aria2-err-not-a-torrent-file    "This is not a .torrent file"                  'user-error)
(define-error 'aria2-err-not-a-metalink-file   "This is not a .metalink file"                 'user-error)
(define-error 'aria2-err-failed-to-start       "Failed to start"                              'error)
(define-error 'aria2-err-no-executable         "Couldn't find `aria2c' executable, aborting"  'error)
(define-error 'aria2-err-no-such-position-type "Wrong position type"                          'error)

(defconst aria2--codes-to-errors-alist
  (list
   (cons "0" "All downloads were successful")
   (cons "1" "An unknown error occurred")
   (cons "2" "Time out occurred")
   (cons "3" "A resource was not found")
   (cons "4" "Aria2 saw the specified number of \"resource not found\" error. See --max-file-not-found option")
   (cons "5" "A download aborted because download speed was too slow. See --lowest-speed-limit option")
   (cons "6" "Network problem occurred")
   (cons "7" "There were unfinished downloads")
   (cons "8" "Remote server did not support resume when resume was required to complete download")
   (cons "9" "There was not enough disk space available")
   (cons "10" "Piece length was different from one in .aria2 control file. See --allow-piece-length-change option")
   (cons "11" "Aria2 was downloading same file at that moment")
   (cons "12" "Aria2 was downloading same info hash torrent at that moment")
   (cons "13" "File already existed. See --allow-overwrite option")
   (cons "14" "Renaming file failed. See --auto-file-renaming option")
   (cons "15" "Aria2 could not open existing file")
   (cons "16" "Aria2 could not create new file or truncate existing file")
   (cons "17" "File I/O error occurred")
   (cons "18" "Aria2 could not create directory")
   (cons "19" "Name resolution failed")
   (cons "20" "Aria2 could not parse Metalink document")
   (cons "21" "FTP command failed")
   (cons "22" "HTTP response header was bad or unexpected")
   (cons "23" "Too many redirects occurred")
   (cons "24" "HTTP authorization failed")
   (cons "25" "Aria2 could not parse bencoded file (usually \".torrent\" file)")
   (cons "26" "A \".torrent\" file was corrupted or missing information that aria2 needed")
   (cons "27" "Magnet URI was bad")
   (cons "28" "Bad/unrecognized option was given or unexpected option argument was given")
   (cons "29" "The remote server was unable to handle the request due to a temporary overloading or maintenance")
   (cons "30" "Aria2 could not parse JSON-RPC request"))
  "Mapping of aria2 error codes to error messages.")

(defsubst aria2--decode-error (err)
  "Provide error messages accroding to ERR."
  (or (cdr-safe (assoc-string err aria2--codes-to-errors-alist nil))
      "Unknown/other error"))

;;; Aria2c process controller starts here.

(defclass aria2-controller (eieio-persistent)
  ((request-id :initarg :request-id
               :initform 0
               :type integer
               :docstring "Value of id field in JSONRPC data, gets incremented for each request.")
   (rcp-url :initarg :rcp-url
            :initform (aria2--url)
            :type string
            :docstring "Url on which aria2c listens for JSON RPC requests.")
   (secret :initarg :secret
           :initform
           (or (let ((uuidgen (executable-find "uuidgen")))
                 (and uuidgen
                      (string-trim (shell-command-to-string uuidgen))))
               (sha1 (format
                      "%s%s%s%s%s%s%s%s%s"
                      (user-uid) (emacs-pid) (system-name) (user-full-name) (current-time)
                      (emacs-uptime) (buffer-string) (random) (recent-keys))))
           :type string
           :docstring "Secret value used for authentication with the aria2c process, for use with --rpc-secret= switch.")
   (pid :initarg :pid
        :initform -1
        :type integer
        :docstring "PID of the aria2c process, or -1 if process isn't running."))
  :docstring "This takes care of starting/stopping aria2c process and provides methods for each remote command.")

;;; Internal methods start here.

(defmethod get-next-id ((this aria2-controller))
  "Return next request id json form. Resets back to 1 upon reaching `most-positive-fixnum'"
  (let ((id (1+ (oref this request-id))))
    (oset this request-id (if (equal id most-positive-fixnum) 0 id))
    id))

(defmethod is-process-running ((this aria2-controller))
  "Returns status of aria2c process."
  (with-slots (pid) this
    (when (and
           (< 0 pid)
           (aria2--is-aria-process-p pid))
      t)))

(defmethod run-process ((this aria2-controller))
  "Starts aria2c process, if not already running."
  (unless (is-process-running this)
    (let ((options (delq nil
                         (append
                          aria2-custom-args
                          `("-D" ;; Start in daemon mode (won't be managed by Emacs).
                            "--enable-rpc=true"
                            ,(format "--rpc-secret=%s" (oref this secret))
                            ,(format "--rpc-listen-port=%s" aria2-rcp-listen-port)
                            ,(format "--dir=%s" aria2-download-directory)
                            ,(format "--save-session=%s" aria2-session-file)
                            ,(when (file-exists-p aria2-session-file)
                               (format "--input-file=%s" aria2-session-file)))))))
      (when aria2--debug
        (message "Starting process: %s %s" aria2-executable (string-join options " ")))
      (apply 'start-process "aria2c" nil aria2-executable options)
      (sleep-for 1)
      ;; aria2 in daemon mode forks to the background, so we search system-processes
      (oset this pid (or (car (cl-remove-if-not #'aria2--is-aria-process-p (list-system-processes)))
                         -1))
      (unless (is-process-running this)
        (signal 'aria2-err-failed-to-start (concat aria2-executable " " (string-join options " ")))))))

(defmethod make-request ((this aria2-controller) method &rest params)
  "Calls a remote METHOD with PARAMS. Returns response alist."
  (run-process this)
  (let ((url-request-method "POST")
        (url-request-data (json-encode-alist
                           (list
                            (cons "jsonrpc" 2.0)
                            (cons "id" (get-next-id this))
                            (cons "method"  method)
                            (cons "params" (vconcat
                                            `(,(format "token:%s" (oref this secret)))
                                            (delq nil params))))))
        (url-request-extra-headers '(("Content-Type" . "application/json")))
        url-history-track
        json-response)
    (when aria2--debug (message "SEND: %s" url-request-data))
    (with-current-buffer (url-retrieve-synchronously (oref this rcp-url) t)
      ;; read last line, where json response is
      (goto-char (point-max))
      (beginning-of-line)
      (setq json-response (json-read))
      (kill-buffer))
    (when aria2--debug (message "RECV: %s" json-response))
    (or (alist-get 'result json-response)
        (error "ERROR: %s" (alist-get 'message (alist-get 'error json-response))))))

;;; Api implementation starts here

(defmethod addUri ((this aria2-controller) urls)
  "Add a list of http/ftp/bittorrent URLS, pointing at the same file.
When sending magnet link, URLS must have only one element."
  (make-request this "aria2.addUri" (vconcat urls)))

(defmethod addTorrent ((this aria2-controller) path)
  "Add PATH pointing at a torrent file to download list."
  (unless (file-exists-p path)
    (signal 'aria2-err-file-doesnt-exist '(path)))
  (unless (string-match-p "\\.torrent$" path)
    (signal 'aria2-err-not-a-torrent-file nil))
  (make-request this "aria2.addTorrent" (aria2--base64-encode-file path)))

(defmethod addMetalink ((this aria2-controller) path)
  "Add local .metalink PATH to download list."
  (unless (file-exists-p path)
    (signal 'aria2-err-file-doesnt-exist '(path)))
  (unless (string-match-p "\\.meta\\(?:4\\|link\\)$" path)
    (signal 'aria2-err-not-a-metalink-file nil))
  (make-request this "aria2.addMetalink" (aria2--base64-encode-file path)))

(defmethod remove-download ((this aria2-controller) gid &optional force)
  "Remove download identified by GID. If FORCE don't unregister download at bittorrent tracker."
  (make-request this (if force "aria2.forceRemove" "aria2.remove") gid))

(defmethod pause ((this aria2-controller) gid &optional force)
  "Pause download identified by GID. If FORCE don't unregister download at bittorrent tracker."
  (make-request this (if force "aria2.forcePause" "aria2.pause") gid))

(defmethod pauseAll ((this aria2-controller) &optional force)
  "Pause all downloads. If FORCE don't unregister download at bittorrent tracker."
  (make-request this (if force "aria2.forcePauseAll" "aria2.pauseAll")))

(defmethod unpause ((this aria2-controller) gid)
  "Unpause download identified by GID."
  (make-request this "aria2.unpause" gid))

(defmethod unpauseAll ((this aria2-controller))
  "Unpause all downloads."
  (make-request this "aria2.unpauseAll"))

(defmethod tellStatus ((this aria2-controller) gid &optional keys)
  "Return status of a download identified by GID."
  (make-request this "aria2.tellStatus" gid keys))

(defmethod tellActive ((this aria2-controller) &optional keys)
  "Return statuses of active downloads."
  (make-request this "aria2.tellActive" keys))

(defmethod tellWaiting ((this aria2-controller) &optional offset num keys)
  "Return statuses of waiting downloads."
  (make-request this "aria2.tellWaiting" (or offset 0) (or num most-positive-fixnum) keys))

(defmethod tellStopped ((this aria2-controller) &optional offset num keys)
  "Return statuses of stopped downloads."
  (make-request this "aria2.tellStopped" (or offset 0) (or num most-positive-fixnum) keys))

(defmethod changePosition ((this aria2-controller) gid pos &optional how)
  "Change position of a download denoted by GID. POS is a number. HOW is one of:
\"POS_SET\" - sets file to POS position from the beginning of a list (first element is 0),
\"POS_CUR\" - moves file by POS places relative to it's current position,
\"POS_END\" - sets file to POS position relative to end of list.
If nil defaults to \"POS_CUR\"."
  (unless (or (null how) (member how '("POS_SET" "POS_CUR" "POS_END")))
    (signal 'aria2-err-no-such-position-type (list how)))
  (make-request this "aria2.changePosition" gid pos (or how "POS_CUR")))

(defmethod changeUri ((this aria2-controller) gid file-index del-uris add-uris &optional position)
  "This method removes the URIs in DEL-URIS list and appends the URIs in ADD-URIS list to download denoted by GID.
FILE-INDEX is 1-based position, identifying a file in a download.
POSITION is a 0-based index specifying where URIs are inserted in waiting list.
Returns a pair of numbers denoting amount of files deleted and files inserted."
  (make-request this "aria2.changeUri" gid file-index del-uris add-uris (or position 0)))

(defmethod getOption ((this aria2-controller) gid)
  "This method returns options of the download denoted by GID."
  (make-request this "aria2.getOption" gid))

(defmethod changeOption ((this aria2-controller) gid options)
  "Set OPTIONS for file denoted by GID. OPTIONS is an alist."
  (make-request this "aria2.changeOption" gid options))

(defmethod getGlobalOption ((this aria2-controller))
  "Return an alist of global options. Global options are used as defaults for newly added files."
  (make-request this "aria2.getGlobalOptions"))

(defmethod changeGlobalOption ((this aria2-controller) options)
  "Changes default global opts to OPTIONS. OPTIONS is an alist of opt-name and value."
  (make-request this "aria2.changeGlobalOption" options))

(defmethod getGlobalStat ((this aria2-controller))
  "Returns global statistics such as the overall download and upload speeds."
  (make-request this "aria2.getGlobalStat"))

(defmethod purgeDownloadResult ((this aria2-controller))
  "This method purges completed/error/removed downloads to free memory."
  (make-request this "aria2.purgeDownloadResult"))

(defmethod removeDownloadResult ((this aria2-controller) gid)
  "Removes a completed/error/removed download denoted by GID from memory."
  (make-request this "aria2.removeDownloadResult" gid))

(defmethod saveSession ((this aria2-controller))
  "Saves the current session to a `aria2-session-file' file."
  (make-request this "aria2.saveSession"))

(defmethod shutdown ((this aria2-controller) &optional force)
  "Shut down aria2c process.  If FORCE don't wait for unregistering torrents."
  (when (is-process-running this)
    (make-request this (if force "aria2.forceShutdown" "aria2.shutdown"))
    (oset this pid -1)))

(defmethod getUris ((this aria2-controller) gid)
  "Return a list of uris used in download identified by GID."
  (make-request this "aria2.getUris" gid))

(defmethod getFiles ((this aria2-controller) gid)
  "Return a file list of a download identified by GID."
  (make-request this "aria2.getFiles" gid))

(defmethod getPeers ((this aria2-controller) gid)
  "Return a list peers of the download denoted by GID."
  (make-request this "aria2.getPeers" gid))

(defmethod getServers ((this aria2-controller) gid)
  "Return currently connected HTTP(S)/FTP servers of the download denoted by GID."
  (make-request this "aria2.getServers" gid))

;;; Major mode settings start here

(defvar aria2--cc nil "Control center object container.")

(defconst aria2--list-format (vector
                              '("File" 40 t) '("Status" 7 t) '("Type" 13 t)
                              '("Done" 4 t) '("Download" 12 t) '("Upload" 12 t)
                              '("Size" 10 nil) '("Error" 0 nil))
  "Format for downloads list columns.")

(defconst aria2--tell-keys
  (vector "gid" "status" "totalLength" "completedLength" "downloadSpeed" "uploadSpeed" "files" "dir" "bittorrent" "errorCode")
  "Default list of keys for use in aria2.tell* calls.")

(defvar aria2--master-timer nil
  "Holds a timer object that dynamically manages frequency of `aria2--refresh-timer', depending on visibility and focused state.")

(defvar aria2--refresh-timer nil
  "Holds a timer object that refreshes downloads list periodically.")

;; FIXME
(defsubst aria2--list-entries-File (e)
  (let ((bt (alist-get 'bittorrent e)))
    (or (and bt (alist-get 'name (alist-get 'info bt)))
        (let ((info (elt (alist-get 'files e) 0)))
          (and (< 0 (length info))
               (file-name-nondirectory
                ;; Get the path
                (alist-get 'path info))))
        "unknown")))

(defsubst aria2--list-entries-Status (e)
  (alist-get 'status e))

(defsubst aria2--list-entries-Type (e)
  (or (and (alist-get 'bittorrent e) "bittorrent")
      (let ((uris
             (alist-get 'uris
                        (elt
                         (alist-get 'files e) 0))))
        (and (< 0 (length uris)) (car-safe
                                  (split-string (alist-get 'uri (elt uris 0)) ":"))))
      "unknown"))

(defsubst aria2--list-entries-Done (e)
  (let ((total (float (string-to-number (alist-get 'totalLength e))))
        (completed (float (string-to-number (alist-get 'completedLength e)))))
    (if (>= 0 total)
        "-"
      (format "%d%%" (* 100.0 (/ completed total))))))

(defsubst aria2--list-entries-Download (e)
  (format "%.2f kB" (/ (string-to-number (alist-get 'downloadSpeed e)) 1024)))

(defsubst aria2--list-entries-Upload (e)
  (format "%.2f kB" (/ (string-to-number (alist-get 'uploadSpeed e)) 1024)))

(defsubst aria2--list-entries-Size (e)
  (let ((size (string-to-number (alist-get 'totalLength e))))
    (if (< size 1024)
        (format "%.2f B" size)
      (setq size (/ size 1024))
      (if (< size 1024)
          (format "%.2f kB" size)
        (setq size (/ size 1024))
        (if (< size 1024)
            (format "%.2f MB" size)
          (setq size (/ size 1024))
          (if (< size 1024)
              (format "%.2f GB" size)
            (format "%2.f TB" (/ size 1024))))))))

(defsubst aria2--list-entries-Err (e)
  (let ((err (alist-get 'errorCode e)))
    (or (and err (aria2--decode-error err))
        " - ")))

(defun aria2--list-entries ()
  "Return entries to be displayed in downloads list."
  (let (entries
        (info (append
               (tellActive aria2--cc aria2--tell-keys)
               (tellWaiting aria2--cc nil nil aria2--tell-keys)
               (tellStopped aria2--cc nil nil aria2--tell-keys)
               nil)))
    (dolist (e info entries)
      (push (list
             (alist-get 'gid e)
             (vector
              (list (aria2--list-entries-File e)     'face 'aria2-file-face)
              (list (aria2--list-entries-Status e)   'face 'aria2-status-face)
              (list (aria2--list-entries-Type e)     'face 'aria2-type-face)
              (list (aria2--list-entries-Done e)     'face 'aria2-done-face)
              (list (aria2--list-entries-Download e) 'face 'aria2-download-face)
              (list (aria2--list-entries-Upload e)   'face 'aria2-upload-face)
              (aria2--list-entries-Size e)
              (list (aria2--list-entries-Err e)      'face 'aria2-error-face)))
            entries))))

;;; Refresh settings start here

(defcustom aria2-refresh-fast 3
  "Timeout after list is refreshed, when it has focus."
  :group 'aria2
  :group 'timer
  :type  '(integer :tag "Number of seconds"))

(defcustom aria2-refresh-normal 8
  "Timeout after list is refreshed, when it doesn't have focus, but its buffer is visible."
  :group 'aria2
  :group 'timer
  :type  '(integer :tag "Number of seconds"))

(defcustom aria2-refresh-slow 20
  "Timeout after list is refreshed, when it doesn't have focus and it's buffer is not visible."
  :group 'aria2
  :group 'timer
  :type  '(integer :tag "Number of seconds"))

(defvar aria2--current-buffer-refresh-speed nil
  "One of :fast :normal :slow or nil if not refreshing. Used to manage refresh timers.")

(defun aria2--manage-refresh-timer ()
  "Restarts `aria2--refresh-timer' on different intervals, depending on focus and buffer visibility."
  (let ((buf (get-buffer aria2-list-buffer-name)))
    (cond ((and
            (eq buf (window-buffer (selected-window))) ; when list has focus
            (not (eq aria2--current-buffer-refresh-speed :fast)))
           (progn
             (when aria2--refresh-timer (cancel-timer aria2--refresh-timer))
             (setq aria2--refresh-timer (run-at-time t aria2-refresh-fast #'aria2--refresh))
             (setq aria2--current-buffer-refresh-speed :fast)))
          ((and
            (get-buffer-window buf) ; list visible but without focus
            (not (eq aria2--current-buffer-refresh-speed :normal)))
           (progn
             (when aria2--refresh-timer (cancel-timer aria2--refresh-timer))
             (setq aria2--refresh-timer (run-at-time t aria2-refresh-normal #'aria2--refresh))
             (setq aria2--current-buffer-refresh-speed :normal)))
          ((not (eq aria2--current-buffer-refresh-speed :slow)) ; list is in the background
           (progn
             (when aria2--refresh-timer (cancel-timer aria2--refresh-timer))
             (setq aria2--refresh-timer (run-at-time t aria2-refresh-slow #'aria2--refresh))
             (setq aria2--current-buffer-refresh-speed :slow))))))

(defun aria2--stop-timer ()
  "Stop timer if any."
  (when aria2--refresh-timer
    (cancel-timer aria2--master-timer)
    (cancel-timer aria2--refresh-timer)
    (setq aria2--refresh-timer nil
          aria2--master-timer nil)))

(defun aria2--refresh ()
  "Refreshes download list buffer. Or stops refresh timers if buffer doesn't exist."
  (let ((buf (get-buffer aria2-list-buffer-name)))
    (if buf
        (with-current-buffer buf (revert-buffer))
      (aria2--stop-timer))))

;; On exit hooks start here
(defun aria2--persist-settings-on-exit ()
  "Persist controller settings, or clear state when aria2c isn't running."
  (aria2--stop-timer)
  (if (and aria2--cc (is-process-running aria2--cc))
      (eieio-persistent-save aria2--cc aria2--cc-file)
    (when (file-exists-p aria2--cc-file)
      (delete-file aria2--cc-file))))

(defun aria2--kill-on-exit ()
  "Stops aria2c process."
  (aria2--stop-timer)
  (when aria2--cc
    (shutdown aria2--cc t)))

(defun aria2-maybe-add-evil-quirks ()
  "Keep aria2-mode in EMACS state, as we already define j/k movement and add C-w * commands."
  (when aria2-add-evil-quirks
    (with-eval-after-load 'evil-states
      (add-to-list 'evil-emacs-state-modes 'aria2-mode)
      (add-to-list 'evil-emacs-state-modes 'aria2-dialog-mode))
    (with-eval-after-load 'evil-maps
      (define-key aria2-mode-map "\C-w" 'evil-window-map))))

;; Interactive commands start here

(defsubst aria2--is-paused-p ()
  (string= "paused" (car (elt (tabulated-list-get-entry) 1))))

(defun aria2-pause ()
  "Pause download."
  (interactive)
  (pause aria2--cc (get-text-property (point) 'tabulated-list-id))
  (message "Pausing download. This may take a moment..."))

(defun aria2-resume ()
  "Resume paused download."
  (interactive)
  (unpause aria2--cc (get-text-property (point) 'tabulated-list-id))
  (revert-buffer))

(defun aria2-toggle-pause ()
  "Toggle 'paused' status for download."
  (interactive)
  (if (aria2--is-paused-p)
      (aria2-resume)
    (aria2-pause)))

(defconst aria2-supported-file-extension-regexp "\\.\\(?:meta\\(?:4\\|link\\)\\|torrent\\)$"
  "Regexp matching .torrent .meta4 and .metalink files.")

(defun aria2--supported-file-type-p (file)
  "Supported FILE predicate. Also allow directories to enable path navigation."
  (or (file-directory-p file)
      (string-match-p aria2-supported-file-extension-regexp file)))

(defun aria2-add-file (arg)
  "Prompt for a file and add it. ARG supports .torrent .meta4 and .metalink files."
  (interactive "P")
  (let ((chosen-file
         (expand-file-name
          (read-file-name
           "Choose .meta4, .metalink or .torrent file: "
           default-directory nil nil nil 'aria2--supported-file-type-p))))
    (if (or (string-blank-p chosen-file)
            (not (file-exists-p chosen-file)))
        (message "No file selected.")
      (if (string-match-p "\\.torrent$" chosen-file)
          (addTorrent aria2--cc chosen-file)
        (addMetalink aria2--cc chosen-file))))
  (revert-buffer))

(defvar aria2-dialog-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map widget-keymap)
    (define-key map [mouse-1] 'widget-button-click)
    map))

(defvar aria2--url-list-widget nil)

(defconst aria2-supported-url-protocols-regexp "\\(?:ftp://\\|http\\(?:s?://\\)\\|magnet:\\)"
  "Regexp matching frp, http, https and magnet urls.")

(defconst aria2-url-list-buffer-name  "*aria2: Add http/https/ftp/magnet url(s)*"
  "Name of a buffer for inputting url's to download.")

(define-derived-mode aria2-dialog-mode fundamental-mode "Add urls"
  "Major moe for adding download urls.")

(defun aria2-add-uris ()
  "Display a form for inputting a list of http/https/ftp/magnet URLs."
  (interactive)
  (switch-to-buffer (get-buffer-create aria2-url-list-buffer-name))
  (kill-all-local-variables)
  (aria2-dialog-mode)
  (let ((inhibit-read-only t)) (erase-buffer))
  (remove-overlays)
  (widget-insert "Please input urls to download.\n\n")
  (widget-insert "Non \"magnet:\" urls must be mirrors pointing to the same file.\n\n")
  (setq aria2--url-list-widget
        (widget-create 'editable-list
                       :entry-format "%i %d %v"
                       :value '("")
                       '(editable-field
                         :valid-regexp aria2-supported-url-protocols-regexp
                         :error "Url does not match supported type."
                         :value "")))
  (widget-insert "\n\n")
  (widget-create 'push-button
                 :notify (lambda (&rest ignore)
                           (setq aria2--url-list-widget nil)
                           (switch-to-buffer aria2-list-buffer-name)
                           (kill-buffer aria2-url-list-buffer-name))
                 "Cancel")
  (widget-insert "  ")
  (widget-create 'push-button
                 :notify (lambda (&rest ignore)
                           (addUri aria2--cc (widget-value aria2--url-list-widget))
                           (setq aria2--url-list-widget nil)
                           (switch-to-buffer aria2-list-buffer-name)
                           (kill-buffer aria2-url-list-buffer-name))
                 "Download")
  (widget-insert "\n")
  (use-local-map aria2-dialog-map)
  (widget-setup)
  (goto-char (point-min))
  (widget-forward 3))

(defun aria2-remove-download (arg)
  "Set download status to 'removed'."
  (interactive "P")
  (when (y-or-n-p "Really remove download? ")
    (remove-download aria2--cc (get-text-property (point) 'tabulated-list-id) (not (equal nil arg)))
    (tabulated-list-delete-entry)))

(defun aria2-clean-removed-download (arg)
  "Clean download with 'removed/completed/error' status.
With prefix remove all applicable downloads."
  (interactive "P")
  (if (equal nil arg)
      (progn
        (removeDownloadResult aria2--cc (get-text-property (point) 'tabulated-list-id))
        (revert-buffer))
    (purgeDownloadResult aria2--cc)
    (revert-buffer)))

(defun aria2-move-up-in-list (arg)
  "Move item one row up, with prefix move to beginning of list."
  (interactive "P")
  (changePosition aria2--cc (get-text-property (point) 'tabulated-list-id) (if (equal nil arg) -1 0) (if (equal nil arg) "POS_CUR" "POS_SET"))
  (revert-buffer))

(defun aria2-move-down-in-list (arg)
  "Move item one row down, with prefix move to end of list."
  (interactive "P")
  (changePosition aria2--cc (get-text-property (point) 'tabulated-list-id) (if (equal nil arg) 1 0) (if (equal nil arg) "POS_CUR" "POS_END"))
  (revert-buffer))

(defun aria2-terminate ()
  "Stop aria2c process and kill buffers."
  (interactive)
  (when (y-or-n-p "Are you sure yo want to terminate aria2 process? ")
    (shutdown aria2--cc)
    (kill-buffer aria2-list-buffer-name)
    (aria2--stop-timer)))

;; Mode line format starts here

(defvar aria2-mode-line-format
  (list
   (propertize "%b" 'face 'mode-line-buffer-id)
   " "
   (propertize
    (concat "[" (propertize "f" 'face 'aria2-modeline-key-face) "]:add file")
    'local-map (make-mode-line-mouse-map 'mouse-1 'aria2-add-file)
    'mouse-face 'aria2-modeline-mouse-face)
   " "
   (propertize
    (concat "[" (propertize "u" 'face 'aria2-modeline-key-face) "]:add url")
    'local-map (make-mode-line-mouse-map 'mouse1 'aria2-add-uris)
    'mouse-face 'aria2-modeline-mouse-face)
   " "
   (propertize
    (concat "[" (propertize "D" 'face 'aria2-modeline-key-face) "]:remove download")
    'local-map (make-mode-line-mouse-map 'mouse1 'aria2-remove-download)
    'mouse-face 'aria2-modeline-mouse-face)
   " "
   (propertize
    (concat "[" (propertize "C" 'face 'aria2-modeline-key-face) "]:clear finished")
    'local-map (make-mode-line-mouse-map 'mouse1 'aria2-clean-removed-download)
    'mouse-face 'aria2-modeline-mouse-face)
   " "
   (propertize
    (concat "[" (propertize "q" 'face 'aria2-modeline-key-face) "]:quit window")
    'local-map (make-mode-line-mouse-map 'mouse1 'aria2-quit)
    'mouse-face 'aria2-modeline-mouse-face)
   " "
   (propertize
    (concat "[" (propertize "Q" 'face 'aria2-modeline-key-face) "]:kill aria2")
    'local-map (make-mode-line-mouse-map 'mouse1 'aria2-terminate)
    'mouse-face 'aria2-modeline-mouse-face))
  "Custom mode-line for use with `aria2-mode'.")

;;; Major mode starts here

(defvar aria2-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "j" 'next-line)
    (define-key map "n" 'next-line)
    (define-key map [down] 'next-line)
    (put 'next-line :advertised-binding "n")
    (define-key map "k" 'previous-line)
    (define-key map "p" 'previous-line)
    (define-key map [up] 'previous-line)
    (put 'previous-line :advertised-binding "p")
    (define-key map "=" 'aria2-move-up-in-list)
    (define-key map "+" 'aria2-move-up-in-list)
    (put 'aria2-move-up-in-list :advertised-binding "=")
    (define-key map "-" 'aria2-move-down-in-list)
    (define-key map "_" 'aria2-move-down-in-list)
    (put 'aria2-move-down-in-list :advertised-binding "-")
    (define-key map "g" 'revert-buffer)
    (put 'revert-buffer :advertised-binding "g")
    (define-key map "q" 'quit-window)
    (define-key map "Q" 'aria2-terminate)
    (define-key map "p" 'aria2-toggle-pause)
    (define-key map "f" 'aria2-add-file)
    (define-key map "u" 'aria2-add-uris)
    (define-key map "D" 'aria2-remove-download)
    (define-key map "C" 'aria2-clean-removed-download)
    map)
  "Keymap for `aria2-mode'.")

(defcustom aria2-mode-hook nil
  "Hook ran afer enabling `aria2-mode'."
  :type 'hook
  :group 'aria2)

(define-derived-mode aria2-mode tabulated-list-mode "Aria2"
  "Mode for controlling aria2 downloader.
\\{aria2-mode-map}"
  :group 'aria2
  (unless (file-executable-p aria2-executable)
    (signal 'aria2-err-no-executable nil))
  ;; try to load controller state from file
  (unless aria2--cc
    (condition-case nil
        (setq aria2--cc (eieio-persistent-read aria2--cc-file aria2-controller))
      (error (setq aria2--cc (make-instance aria2-controller
                                            "aria2-controller"
                                            :file aria2--cc-file)))))
  ;; kill process or save state on exit
  (if aria2-kill-process-on-emacs-exit
      (add-hook 'kill-emacs-hook 'aria2--kill-on-exit)
    (add-hook 'kill-emacs-hook 'aria2--persist-settings-on-exit))
  ;; list settings
  (setq tabulated-list-format aria2--list-format)
  (tabulated-list-init-header)
  (setq tabulated-list-entries #'aria2--list-entries)
  (tabulated-list-print)
  ;; refresh list periodically
  (when (not aria2--master-timer)
    (setq aria2--master-timer
          (run-at-time t 5 #'aria2--manage-refresh-timer)))
  (hl-line-mode 1)
  (aria2-maybe-add-evil-quirks)
  (setq-local mode-line-format aria2-mode-line-format))

;;;###autoload
(defun aria2-downloads-list ()
  "Display aria2 downloads list.  Enable `aria2-mode' to controll the process."
  (interactive)
  (with-current-buffer (pop-to-buffer aria2-list-buffer-name)
    (aria2-mode))
  (message
   (substitute-command-keys
    "Type \\<aria2-mode-map>\\[quit-window] to quit, \\[aria2-terminate] to kill aria, \\[describe-mode] for help")))

(provide 'aria2)

;; Local Variables:
;; coding: utf-8-unix
;; indent-tabs-mode: nil
;; End:

;;; aria2.el ends here
