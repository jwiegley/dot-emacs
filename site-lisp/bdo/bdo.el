;;; bdo.el --- Do things to a browser page from Emacs. BETA!

;; Copyright (c) 2012 Chris Done. All rights reserved.

;; Author:   Chris Done <chrisdone@gmail.com>
;; Created:  07-April-2012
;; Version:  0.1
;; Keywords: development

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
;; FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
;; Chris Done BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
;; USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
;; ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
;; OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
;; OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
;; SUCH DAMAGE.
;;
;;; Commentary:
;;
;; Usage:
;; 
;; (add-to-list 'load-path "/the/path/to/bdo")
;; 
;; Optional keybinding:
;; 
;; (define-key css-mode-map (kbd "C-x C-s") 'css-refresh)
;; (defun css-refresh ()
;;   "Refresh the current CSS file."
;;   (interactive)
;;   (when (buffer-modified-p)
;;     (save-buffer))
;;   (bdo-refresh))
;; 

;;; Code:

(require 'cl)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Customization

(defcustom bdo-port
  9090
  "The port to listen on (to which the browser connects)."
  :type 'integer
  :group 'bdo)

(defcustom bdo-js-file
  "bdo.js"
  "The JS file to read (if cannot find absolute or relative to
current buffer, tries to get from 'load-path."
  :type 'string
  :group 'bdo)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Types

(defstruct
  (bdo-client
   (:constructor bdo-client-make))
  id
  links
  process)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Globals

(defvar bdo--clients nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Public functions

(defun bdo-listen ()
  "Start the listener (or: make sure it's started)."
  (interactive)
  (bdo--get-listener)
  (message "Listener started on port %d…" bdo-port))

(defun bdo-stop ()
  "Stop listening."
  (interactive)
  (delete-process (bdo--get-listener))
  (message "Listener stopped."))

(defun bdo-refresh (&optional href)
  "Refresh the current stylesheet."
  (interactive)
  (let* ((client (bdo-client))
         (process (bdo-client-process client))
         (link (and process (bdo-link))))
    (when (and process link)
      (bdo--reply-plain (bdo-client-process client) link)
      (message "Refreshed."))))

(defun bdo-link ()
  "Get the current stylesheet."
  (or (if (boundp 'bdo-link)
          bdo-link
        (set (make-local-variable 'bdo-link) nil))
      (bdo-set-link)))

(defun bdo-set-link ()
  "Set the current stylesheet."
  (interactive)
  (setq bdo-link
        (ido-completing-read "Stylesheet: " (bdo-client-links (bdo-client)))))

(defun bdo-client ()
  "Get the current client."
  (or (if (boundp 'bdo-client)
          (find-if (lambda (client) (string= (bdo-client-id client) bdo-client))
                   bdo--clients)
        (set (make-local-variable 'bdo-client) nil))
      (progn (bdo-set-client)
             (bdo-client))))

(defun bdo-set-client ()
  "Set the current client."
  (interactive)
  (if (consp bdo--clients)
      (let ((id (ido-completing-read "Client: " (mapcar 'bdo-client-id bdo--clients))))
        (setq bdo-client id))
    (error "There are no current clients!")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Private functions

(defun bdo--get-listener ()
  "Get the existing listener or make it."
  (let ((name "*bdo-listener*"))
    (or (get-process name)
        (make-network-process
         :name name
         :server t
         :host nil
         :service bdo-port
         :family 'ipv4
         :coding 'utf-8
         :filter 'bdo--filter
         :sentinel 'bdo--sentinel
         :log 'bdo--log))))

(defun bdo--filter (process data)
  "Callback for INCOMMING data on a connection."
  (when (string-match "\\(GET\\|POST\\) /\\(.+\\) " data)
    (let ((cmd (match-string 2 data))
          (referer (bdo--get-header data "Referer")))
      (cond
       ((string= cmd "bdo")
        (bdo--reply-js process (bdo--get-js (bdo--get-header data "Host")))
        (if (bdo--find-client referer)
            (message "Client re-connected: %s" referer)
          (progn (add-to-list 'bdo--clients (bdo-client-make :id referer :process nil))
                 (message "New client: %s" referer))))
       ((string-match "^poll" cmd)
        (let ((client (bdo--find-client referer)))
          (setf (bdo-client-process client) process)))
       ((string= cmd "links")
        (let ((client (bdo--find-client referer)))
          (bdo--update-links client data)
          (bdo--reply-plain process "Links updated.")))
       (t (bdo--reply-plain process (format "Unknown command: %S" cmd)))))))

(defun bdo--find-client (referer)
  "Find a client by the given referer."
  (find-if (lambda (client)
             (string= (bdo-client-id client) referer))
           bdo--clients))

(defun bdo--reply-js (process body)
  "Reply with some JS."
  (bdo--reply process body "text/javascript"))

(defun bdo--reply-plain (process body)
  "Reply with plain text."
  (bdo--reply process body "text/plain"))

(defun bdo--reply (process body content-type)
  "Send a valid HTTP reply to the browser."
  (process-send-string
   process
   (format "%s\n%s\n%s\n%s\n\n%s"
           "HTTP/1.1 200 OK"
           (format "Content-Type: %s" content-type)
           "Access-Control-Allow-Origin: *"
           (format "Content-Length: %s" (string-bytes body))
           body))
  (process-send-eof process))

(defun bdo--sentinel (process status)
  "Callback for the STATUS CHANGE of a connection.")

(defun bdo--log (server client message)
  "Callback to log the NEW CONNECTIONS of the listener.")

(defun bdo--get-js (host)
  "Get the JS code to send to the client."
  (if (bdo--find-js-file)
      (with-temp-buffer 
        (insert-file-contents (bdo--find-js-file))
        (goto-char (point-max))
        (insert (format "bdo.host = %S;\n" (format "http://%s/" host))
                "bdo.init();")
        (goto-char (point-max))
        (buffer-substring-no-properties (point-min) (point-max)))
    (error "Unable to find `bdo-js-file'.")))

(defun bdo--find-js-file ()
  "Find a path for the JS file that exists."
  (let ((absolute-or-relative bdo-js-file))
    (cond ((file-exists-p absolute-or-relative) absolute-or-relative)
          (t (let ((choices (remove-if-not 'file-exists-p
                                           (mapcar (lambda (dir)
                                                     (concat dir "/" bdo-js-file))
                                                   load-path))))
               (when (consp choices)
                 (car choices)))))))

(defun bdo--get-header (data header)
  "Get the given header."
  (let ((value (and (string-match (format "^%s: \\(.+\\)$" header)
                                  data)
                    (match-string 1 data))))
    (if (not value)
        (error "Unable to get header %s from client, request was: %S." %s data)
      value)))

(defun bdo--update-links (client data)
  "Get the links from the request and update our internal list."
  (let ((post-data (bdo--post-data data)))
    (let ((links (and (string-match "^links=\\(.+\\)" post-data)
                      (read (match-string 1 post-data)))))
      (setf (bdo-client-links client) links))))

(defun bdo--post-data (data)
  "Get the post data from the request."
  (let ((post-data (and (string-match "\n\n\\(.+\\)" data)
                        (match-string 1 data))))
    (if (not post-data)
        (error "Unable to parse post data from request.")
      (url-unhex-string (replace-regexp-in-string "+" "%20" post-data)))))

(provide 'bdo)
;;; bdo.el ends here
