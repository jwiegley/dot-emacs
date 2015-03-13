;;; dired-sync.el --- sync directories within dired

;; Copyright © 2010 Sebastien Gross <seb•ɑƬ•chezwam•ɖɵʈ•org>

;; Author: Sebastien Gross <seb•ɑƬ•chezwam•ɖɵʈ•org>
;; Keywords: emacs, dired, rsync
;; Created: 2010-12-02
;; Last changed: 2011-09-02 16:08:37
;; Licence: WTFPL, grab your copy here: http://sam.zoy.org/wtfpl/

;; This file is NOT part of GNU Emacs.

;;; History:
;;
;;  * 0.3 - Add dired-do-sync-pool (thanks to ryukzak)
;;
;;  * 0.2 - Fix ssh commands.
;;
;;  * 0.1 - first release

;;; TODO
;;  * move both rsync / ssh commands to variables.

;;; Commentary:
;; 
;; dired-sync provide a simple and easy way to synchronize directories from
;; dired. This tool is based upon both rsync(1) and ssh(1).
;;
;; To install `dired-sync' you simply need to drop dired-sync.el in your
;; load-path and bind (suggested) C-s S key to `dired-do-sync':
;;
;; (when (require 'dired-sync nil t)
;;   (define-key dired-mode-map (kbd "C-c S") 'dired-do-sync))
;;
;; Synchronizations can also be done using pools (seed `dired-do-sync-pool'.
;; For this to work `dired-sync-pools' needs to be configured. To bind
;; `dired-do-sync-pool' to C-c s add this in previous sexp:
;;
;; (define-key dired-mode-map (kbd "C-c s") 'dired-do-sync-pool)
;;
;; There are 3 types of directories synchronizations as explained bellow.
;;
;; * local / local
;;   This is the easiest way. rsync(1) would be enough.
;;
;; * local / remote or remote / local
;;   This is also a simple way, the only requirement is a working ssh
;;   connection to the remote host.
;;
;; * remote / remote
;;   This is a bit more complexe since there are 3 types of remote / remote
;;   syncs.
;;   - source server can reach destination server
;;     In that case `dired-sync' would optimize files synchronisation by
;;     running rsync(1) on the source server through a ssh connection.
;;   - source server cannot reach destination server
;;     This is the more complexe case. `dired-sync' would create a ssh
;;     tunnel from source to destination using your local machine as a
;;     jumphost.
;;     Be aware this mode is greedy regarding bandwidth consumption since
;;     data are transfered twice: from the source server to localhost AND
;;     from localhost to destination server.
;;   - Both source and destination are located on the same remote host.
;;     This case is the same as the first one (source server can reach
;;     destination server) except the destination directory is local (on the
;;     remote host).
;;  If a direct connection could not be established from source to
;;  destination, `dired-sync' would automatically fall back to the tunneled
;;  sync mode.
;;
;;  `dired-sync' is heavily based on ssh(1) configuration hence your
;;  ~/.ssh/config file should be as accurate as possible. It doesn't matter
;;  how many jumphosts you need to use to reach both source and destination
;;  as long as they are declared in you ssh configuration file.
;;
;;  To allow `dired-sync' to work out of the box, key-based ssh
;;  authentication is required.
;;
;;      Source                       Destination
;;
;;    +---------+   (if possible)    +---------+
;;    |  HostA  |<- - - - - - - - - >|  HostB  |
;;    |  UserA  |                    |  UserB  |
;;    +---------+                    +---------+
;;         ^                              ^    
;;    +---------+                    +---------+
;;    |JumphostA|                    |JumphostB|
;;    | UserJHA |                    | UserJHB |
;;    +---------+                    +---------+
;;         ^                              ^
;;         |          +---------+         |
;;         -----------|localhost|----------
;;                    +---------+
;;	      
;; To use that configuration, you ~/.ssh/config may be something like:
;;
;;   Host *
;;        ForwardAgent yes
;;        RhostsRSAAuthentication yes
;;        RSAAuthentication yes
;;        HashKnownHosts yes
;;        IdentityFile ~/.ssh/id_rsa
;;        TCPKeepAlive yes
;;        ServerAliveInterval 30
;;        Port 22
;;        Protocol 2,1
;;
;;   Host jumphostA
;;        User userJHA
;;        HostName jumphostA.example.com
;;
;;   Host hostA
;;        User userA
;;        HostName jumphostA.internal.example.com
;;        ProxyCommand ssh -q -t jumphostA  nc -w 1 %h %p
;;
;;   Host jumphostB
;;        User userJHB
;;        HostName jumphostB.other-example.com
;;
;;   Host hostB
;;        User userB
;;        HostName jumphostV.internal.other-example.com
;;        ProxyCommand ssh -q -t jumphostB  nc -w 1 %h %p
;;
;;
;; then you would be able to connect to hostA by simply typing:
;;
;;    ssh hostA
;;
;; Or opening a dired buffer to hostB: C-X C-f /scp:hostB:
;;
 
;;; Code:

(defconst dired-sync-version "0.3"
  "The version number of dired-sync.")

;;;###autoload
(defun dired-sync-version (arg)
  "Print version number of dired-sync in minibuffer or current
buffer."
  (interactive "P")
  (if arg 
      (insert dired-sync-version) 
    (message dired-sync-version)))

(defcustom dired-sync-timeout 10
  "Timeout (in seconds) when performing ssh login tests."
  :type 'integer
  :group 'dired-sync)

(defcustom dired-sync-command-delay 10
  "Delay (in seconds) between commands when synchronizing 2
tunneled remote hosts."
  :type 'integer
  :group 'dired-sync)

(defcustom dired-sync-commands
  '(:get-user-local
    (lambda (src dst) "id -un")
    :get-user-remote
    (lambda (src dst)
      (dired-sync-with-files
       src dst
       (concat
	"ssh -q -o StrictHostKeyChecking=no "
	"-o PasswordAuthentication=no "
	"-o UserKnownHostsFile=/dev/null "
	(if dst-user
	    (format "%s@%s" dst-user dst-host)
	  dst-host)
	" 'id -un'")))
    :do-sync-local-local
    (lambda (src dst)
      (dired-sync-with-files
       src dst
       (list
	(list "rsync" "--delete" "-a" "-D" "-i" "-u"
	      src-path-quote dst-path-quote)
	nil)))
    :do-sync-remote-local
    (lambda (src dst)
      (dired-sync-with-files
       src dst
       (list
	(list "rsync" "--delete" "-a" "-D" "-i" "-u"
	      (format "%s:%s" src-host src-path) dst-path)
	nil)))
    :do-sync-local-remote
    (lambda (src dst)
      (dired-sync-with-files
       src dst
       (list
	(list "rsync" "--delete" "-a" "-D" "-i" "-u" src-path
	      (format "%s:%s" dst-host dst-path))
	nil)))
    :do-sync-remote-remote-direct
    (lambda (src dst)
      (dired-sync-with-files
       src dst
       (list
	(list "ssh" 
	      "-o" "StrictHostKeyChecking=no"
	      "-o" "PasswordAuthentication=no"
	      "-o" "UserKnownHostsFile=/dev/null"
	      "-A" src-host
	      (concat "rsync --delete -a -D -i -u -e 'ssh -A "
		      "-o StrictHostKeyChecking=no "
		      "-o PasswordAuthentication=no "
		      "-o UserKnownHostsFile=/dev/null' "
		      src-path
		      (format " %s@%s:%s" dst-user dst-host
			      dst-path)))
	nil)))
    :do-sync-remote-remote-same
    (lambda (src dst)
      (dired-sync-with-files
       src dst
       (list
	(list "ssh" 
 	      "-o" "StrictHostKeyChecking=no"
	      "-o" "PasswordAuthentication=no"
	      "-o" "UserKnownHostsFile=/dev/null"
	      "-A" src-host
	      (concat "rsync --delete -a -D -u -i " src-path " "
		      dst-path))
	nil)))
    :do-sync-remote-remote
    (lambda (src dst)
      (dired-sync-with-files
       src dst
       (list
	(list "ssh"
 	      "-o" "StrictHostKeyChecking=no"
	      "-o" "PasswordAuthentication=no"
	      "-o" "UserKnownHostsFile=/dev/null"
	      "-L"
	      (format "%d:127.0.0.1:22" dst-tunnel-port)
	      dst-host)
	(list "ssh" "-A" "-R" 
	      (format "%d:127.0.0.1:%d" src-tunnel-port
		      dst-tunnel-port)
	      src-host
	      (concat 
	       "rsync --delete -a -D -i -u -e "
	       "'ssh -A -p " (format "%d " src-tunnel-port)
	       "-o StrictHostKeyChecking=no "
	       "-o PasswordAuthentication=no "
	       "-o UserKnownHostsFile=/dev/null' "
	       src-path-quote
	       (format " %s@127.0.0.1:%s"
		       dst-user dst-path-quote)))))))

  "PLIST containing commands used to perform synchronization.

Function are called with 2 parameters SRC and DST as return by
`dired-sync-parse-uri' suitable for `dired-sync-with-files'
macro.

:get-user-local

  Shell function to be used to retrieve local username. Please
  note that local is relative to source host.
  Should return a string evaluated by `shell-command'.

:get-user-remote

  Shell function to be used to retrieve remote username from
  source host. This function is used to check source-destination
  connectivity.
  Should return a string evaluated by `shell-command'.

:do-sync-local-local

  Shell function to be used to synchronize two local directories.
  This function should return a list of 2 items suitable for
  `start-process'.

  Generally the first element of the list is a list containing
  full rsync parameters. The second element should be nil.


:do-sync-local-remote

  Shell function to be used to synchronize local directory to a
  remote one. Like ::do-sync-local-local This function should
  return a list of 2 items suitable for `start-process'.

  Generally the first element of the list is a list containing
  full rsync parameters. The second element should be nil.

:do-sync-remote-local

  Same as :do-sync-local-remote but in a reverse way.

:do-sync-remote-remote-direct

  Shell function to be used to synchronize two remote
  directories. This is used then source host can connect to
  destination host. This function should return a list of 2 items
  suitable for `start-process'.

  Generally the first element of the list is a list containing
  full rsync parameters. The second element should be nil.

::do-sync-remote-remote-same

  Shell function to be used to synchronize two remote directories
  on the same host.This function should return a list of 2 items
  suitable for `start-process'.

  Generally the first element of the list is a list containing
  full rsync parameters. The second element should be nil.

:do-sync-remote-remote

  Shell function to be used to synchronize two remote
  directories. This is used when source host cannot connect to
  destination host. This function should return a list of 2
  items suitable for `start-process'.

  Generally the first element of the list is a list containing
  ssh tunnel setup from local host to destination host, second
  element should contain the rsync command from source host to
  destination using local host as a ssh tunnel gateway."
  :type 'plist
  :group 'dired-sync)

(defcustom dired-sync-pools nil
  "List of pool to be used in `dired-sync-pool'.

Each pool consists of a list:

  \(NAME :src SOURCE :dst DESTINATIONs\)

NAME is the pool name.

SOURCE is the pool source directory path.

DESTINATIONs is the pool destination path. it can either be a
path string or a list of paths."
  :type 'plist
  :group 'dired-sync)

(defvar dired-sync-pool-history nil
  "History list for pools `dired-sync-pool'.")

(defvar dired-sync-pool-dst-history nil
  "History list for destinations limit in `dired-sync-pool'.")

(defvar dired-sync-pool-all "*"
  "Marker to be used in `dired-sync-pool' to synchronize all
  destinations.")

(defmacro dired-sync-with-files (src dst &rest body)
  "Execute BODY after converting both SRC and DST to variables according
`dired-sync-parse-uri' PLIST definition.

Variables can be accessed anywhere in BODY.

Variables are: src-file, src-host, src-user, src-path,
src-path-quote, src-tunnel-port, src-direct, dst-file, dst-host,
dst-user, dst-path, dst-path-quote, dst-tunnel-port, dst-direct.

See `dired-sync-parse-uri' for further information."
  `(let* ((src ,src)
	  (src-file (plist-get ,src :file))
	  (src-host (plist-get ,src :host))
	  (src-user (plist-get ,src :user))
	  (src-path (plist-get ,src :path))
	  (src-path-quote (plist-get ,src :path-quote))
	  (src-tunnel-port (plist-get ,src :tunnel-port))
	  (src-direct (plist-get ,src :direct))
	  (dst ,dst)
	  (dst-file (plist-get ,dst :file))
	  (dst-host (plist-get ,dst :host))
	  (dst-user (plist-get ,dst :user))
	  (dst-path (plist-get ,dst :path))
	  (dst-path-quote (plist-get ,dst :path-quote))
	  (dst-tunnel-port (plist-get ,dst :tunnel-port))
	  (dst-direct (plist-get ,dst :direct)))
     ,@body))


(defun dired-sync-get-user (src &optional dst)
  "Return username on S-HOST when connecting using ssh.

If D-HOST is defined, try to connect to D-HOST using S-HOST
as a proxy.

If an error occurs, returns nil.

Both SRC-HOST and DST-HOST provided by `dired-sync-with-files'
macro are used if needed."
  (let* ((err (get-buffer-create "*err*"))
	 (out (get-buffer-create "*out*"))
	 (cmd (funcall (plist-get dired-sync-commands
				  (if dst ':get-user-remote
				    ':get-user-local))
		       src dst))
	 in-s out-s)

    (dired-sync-with-files
     src dst
     (let ((default-directory (format "/%s:/" src-host)))
       (with-timeout
	   (dired-sync-timeout
	    (message
	     (format "dired-sync-get-user timeout on %s : %s"
		     src-host cmd)))
	 (shell-command cmd out err)))
     
     (set-buffer out)
     ;; Just keep the last line in case of error such as
     ;; cd: 1149: can't cd to /path/to
     (point-max)
     (setq out-s (buffer-substring-no-properties 
		  (point-at-bol) (point-at-eol)))
     (kill-buffer out)
     (set-buffer err)
     (setq err-s (buffer-string))
     (kill-buffer err)
     (when (string= "" out-s) (setq out-s nil))
     out-s)))



(defun dired-sync-parse-uri (file)
  "Parse FILE which syntax is given by Info node `(tramp) Filename Syntax'.

Returned value is a PLIST with following properties.

:file

    A copy of original FILE value.

:host

    The remote hostname returned by `tramp-file-real-host'. nil
    if file is local.

:user

    The remove user (login) name if FILE is remote, nil if user
    is not specified in FILE, or if FILE is local. Value is
    retrieved using `tramp-file-name-user'.

:path

    The full pathname retrieved using
    `tramp-file-name-localname'.

:path-quote

    A shell quoted version of the :path as returned by
    `shell-quote-argument'.

:tunnel-port

    Random port used to for ssh tunnel setup."
  (let* ((file (expand-file-name file))
	 (file-vec (or (ignore-errors (tramp-dissect-file-name file))
		       (tramp-dissect-file-name (concat "/:" file) 1)))
	 (host (tramp-file-name-real-host file-vec))
	 (user (tramp-file-name-user file-vec))
	 (path (tramp-file-name-localname file-vec))
	 (method (tramp-file-name-method file-vec))
	 (ret (list :file file :user user :method method
		    :host host :path path
		    :path-quote (shell-quote-argument path)
		    :tunnel-port nil)))
    (when (and host (not user))
      (setq ret (plist-put ret :user (dired-sync-get-user ret)))
      (setq ret (plist-put ret :tunnel-port
			   (+ 1024 (random (- 32767 1024))))))
    ret))



(defun dired-sync-read-src-dst (&optional source destination)
  "Read both source and detination directories from minibuffer if not provided.

If called from a `dired-mode' buffer, use `dired-file-at-point' for
SOURCE."
  (let* ((src (dired-sync-parse-uri
	       (or source
		   (if (eq major-mode 'dired-mode)
		       (dired-file-name-at-point)
		     nil)
		   (read-file-name "Sync source: " nil nil t nil))))
	 (dst (dired-sync-parse-uri
	       (or destination
		   (read-file-name
		    (format "Sync %s to: " (plist-get src :file)))
		nil nil t nil)))
	 direct)
    (dired-sync-with-files
     src dst

     ;; remove tailing / from source file (:file :path and :path-quote)
     ;; Prevent from copying all source files into destination without
     ;; creating a new directory.
     (unless (string= "/" src-path)
       (mapcar '(lambda(x)
		  (setq src
			(plist-put src x
				   (replace-regexp-in-string
				    "/*$" "" (plist-get src x)))))
	       '(:file :path :path-quote)))

     ;; try to get e direct link between the hosts
     (when (and src-host dst-host)
       (setq direct
	     (dired-sync-get-user src dst)))
     (setq src (plist-put src :direct direct))
     (setq dst (plist-put dst :direct direct))
     (list :src src :dst dst))))


;;;###autoload
(defun dired-do-sync (&optional source destination)
  "Synchronize 2 directories using commands defined in
`dired-sync-commands'."
  (interactive)
  (let* ((files (dired-sync-read-src-dst source destination))
	 (src (plist-get files :src))
	 (dst (plist-get files :dst))
	 item clist cmd1 cmd2 )
    (dired-sync-with-files
     src dst
     (cond
      ;; both files are remote and on the same host.
      ((and src-host dst-host (string= src-host dst-host))
       (setq item :do-sync-remote-remote-same))
      ;; both files are remote and src cannot connect to dst
      ((and  src-host dst-host (not src-direct))
       (setq item :do-sync-remote-remote))
      ;; both files are remote and src can connect to dst
      ((and src-host dst-host)
       (setq item :do-sync-remote-remote-direct))
      ;; source is local, destination is remote
      ((and (not src-host) dst-host)
       (setq item :do-sync-local-remote))
      ;; source is remote, destination is local
      ((and src-host (not dst-host))
       (setq item :do-sync-remote-local))
      ;; all files are local
      (t
       (setq item :do-sync-local-local)))
     (setq clist (funcall (plist-get dired-sync-commands item) src dst))
     (setq cmd2 (cadr clist))
     (setq cmd1 (car clist))
     ;; (message (concat "C1: " (mapconcat 'append cmd1 " ")))
     ;; (message (concat "C2: " (mapconcat 'append cmd2 " ")))
     (let* ((p1-str (format "dired-sync %s to %s"
			    (plist-get src :file)
			    (plist-get dst :file)))
	    (p1-buf (format "*%s*" p1-str))
	    (p1 (apply 'start-process p1-str p1-buf (car cmd1) (cdr cmd1)))
	    (p2-str (format "%s (syncing)" p1-str))
	    (p2-buf (format "*%s*" p2-str))
	    p2)

       (process-put p1 :buf p1-buf)
       (unless cmd2
	 (set-process-sentinel p1 'dired-sync-proc-sentinel))
       (when cmd2
	 ;;make sur shh tunnel is up
	 (sit-for dired-sync-command-delay)
	 (setq p2 (apply 'start-process p2-str p2-buf (car cmd2) (cdr cmd2)))
	 (process-put p2 :related p1)
	 (process-put p2 :buf p2-buf)
	 (set-process-sentinel p2 'dired-sync-proc-sentinel)))
     
     t)))


(defun dired-sync-proc-sentinel (proc change)
  (when (eq (process-status proc) 'exit)
    (let ((status (process-exit-status proc))
	  (buf (process-get proc :buf))
	  (related (process-get proc :related)))
      (if (not (eq 0 status))
	  (progn
	    (when (process-buffer proc)
	      (set-window-buffer (selected-window) buf))
	    (error "dired-sync failled"))
	(message "dired-sync success")
	(kill-buffer buf))
      (when related
	(kill-process related)))))


;;;###autoload
(defun dired-do-sync-pool (&optional pool dst-limit)
  "Sync pools defined in `dired-sync-pools'.

If POOL is not defined, user would be prompted for one.

If DST-LIMIT is passed to the function, it would override the
destination for the synchronization.

If called interactively using `universal-argument' (C-u)
synchronization DST-LIMIT would be prompted in addition to POOL.

If DST-LIMIT is `dired-sync-pool-all' all defined destination
would be synchronized."
  (interactive "P")
  (let* ((pool (if (or current-prefix-arg (not pool))
		   (completing-read
		    "Sync pool: "
		    (mapcar 'car dired-sync-pools)
		    nil t nil dired-sync-pool-history nil t)
		 pool))
	 (pool-conf (cdr (assoc pool dired-sync-pools)))
	 (src (plist-get pool-conf :src))
	 (dst (plist-get pool-conf :dst)))

    ;; Make sure dst is a list for further actions.
    (unless (listp dst)
      (setq dst `(,dst)))

    ;; limitation
    (when (and current-prefix-arg
	       (> (length dst) 1))
      (setq dst-limit
	    (completing-read
	     "Limit to destination: "
	     (cons dired-sync-pool-all
		   (if (listp dst) dst `(,dst)))
	     nil t nil dired-sync-pool-dst-history nil t)))

    (when dst-limit
      (if (listp dst-limit)
	  (setq dst dst-limit)
	(unless (string= dired-sync-pool-all dst-limit))
	(setq dst `(,dst-limit))))

    (mapcar
     '(lambda(x)
	(message (format "syncing pool %s: %s -> %s" pool src x))
	(dired-do-sync src x))
     dst)))

(provide 'dired-sync)
