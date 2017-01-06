;;; markdown-preview-mode.el --- markdown realtime preview minor mode.

;; Copyright (C) 2014 <igor.shimko@gmail.com>

;; Author: Igor Shymko <igor.shimko@gmail.com>
;; URL: https://github.com/ancane/markdown-preview-mode
;; Keywords: markdown, gfm, convenience
;; Version: 0.8
;; Package-Requires: ((emacs "24.3") (websocket "1.6") (markdown-mode "2.0") (cl-lib "0.5") (web-server "0.1.1") (uuidgen "0.3"))

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; This package makes use of websockets to deliver rendered markdown to a web browser.
;; Updates happen upon buffer save or on idle.
;;
;;; Code:

(require 'cl-lib)
(require 'websocket)
(require 'markdown-mode)
(require 'web-server)
(require 'uuidgen)

(defgroup markdown-preview nil
  "Markdown preview mode."
  :group 'text
  :prefix "markdown-preview-"
  :link '(url-link "https://github.com/ancane/markdown-preview-mode"))

(defcustom markdown-preview-host "localhost"
  "Markdown preview websocket server address."
  :group 'markdown-preview
  :type 'string)

(defcustom markdown-preview-ws-port 7379
  "Markdown preview websocket server port."
  :group 'markdown-preview
  :type 'integer)

(defcustom markdown-preview-http-port 9000
  "Markdown preview http server port."
  :group 'markdown-preview
  :type 'integer)

(defcustom markdown-preview-style nil
  "Deprecated. Use `markdown-preview-stylesheets'."
  :group 'markdown-preview
  :type 'string)

(defcustom markdown-preview-file-name ".markdown-preview.html"
  "Markdown preview file name."
  :group 'markdown-preview
  :type 'string)

(defcustom markdown-preview-auto-open 'http
  "Markdown preview websocket server address."
  :group 'markdown-preview
  :type '(choice (const :tag "As local file" file)
                 (const :tag "Via http" http)
                 (const :tag "Off" nil)))

(defvar markdown-preview-javascript '()
  "List of client javascript libs for preview.")

(defvar markdown-preview-stylesheets
  (list "http://thomasf.github.io/solarized-css/solarized-dark.min.css")
  "List of client stylesheets for preview.")

(defvar markdown-preview--websocket-server nil
  "`markdown-preview' Websocket server.")

(defvar markdown-preview--http-server nil
  "`markdown-preview' http server.")

(defvar markdown-preview--local-client nil
  "`markdown-preview' local client.")

(defvar markdown-preview--remote-clients (make-hash-table :test 'equal)
  "Remote clients hashtable. UUID -> WS")

(defvar markdown-preview--home-dir (file-name-directory load-file-name)
  "`markdown-preview-mode' home directory.")

(defvar markdown-preview--idle-timer nil
  "Preview idle timer.")

(defvar markdown-preview--uuid nil
  "Unique preview identifier.")

(defvar markdown-preview--preview-buffers (make-hash-table :test 'equal)
  "Preview buffers hashtable. UUID -> buffer-name.")

(defun markdown-preview--stop-idle-timer ()
  "Stop the `markdown-preview' idle timer."
  (when (timerp markdown-preview--idle-timer)
    (cancel-timer markdown-preview--idle-timer)))

(defun markdown-preview--css-links ()
  "Get list of styles for preview in backward compatible way."
  (let* ((custom-style (list markdown-preview-style))
         (all-styles
          (mapc (lambda (x) (add-to-list 'custom-style x t)) markdown-preview-stylesheets)))
    (mapconcat
     (lambda (x)
       (concat "<link rel=\"stylesheet\" type=\"text/css\" href=\"" x "\">"))
     all-styles
     "\n")))

(defun markdown-preview--scripts ()
  "Get list of javascript script tags for preview."
  (mapconcat
   (lambda (x)
     (concat
      "<script src=\"" (if (consp x) (car x) x) "\""
      (if (consp x) (format " %s" (cdr x)))
      "></script>"))
   markdown-preview-javascript
   "\n"))

(defun markdown-preview--read-preview-template (preview-uuid preview-file)
  "Read preview template and writes identified by PREVIEW-UUID
rendered copy to PREVIEW-FILE, ready to be open in browser."
  (with-temp-file preview-file
    (insert-file-contents (expand-file-name "preview.html" markdown-preview--home-dir))
    (when (search-forward "${MD_STYLE}" nil t)
        (replace-match (markdown-preview--css-links) t))
    (when (search-forward "${MD_JS}" nil t)
        (replace-match (markdown-preview--scripts) t))
    (when (search-forward "${WS_HOST}" nil t)
        (replace-match markdown-preview-host t))
    (when (search-forward "${WS_PORT}" nil t)
        (replace-match (format "%s" markdown-preview-ws-port) t))
    (when (search-forward "${MD_UUID}" nil t)
        (replace-match (format "%s" preview-uuid) t))
    (buffer-string)))

(defun markdown-preview--start-http-server (port)
  "Start http server at PORT to serve preview file via http."
  (unless markdown-preview--http-server
    (lexical-let ((docroot default-directory))
      (setq markdown-preview--http-server
            (ws-start
             (lambda (request)
               (with-slots (process headers) request
                 (let* ((path (substring (cdr (assoc :GET headers)) 1))
                        (filename (expand-file-name path docroot)))
                   (if (string= path "")
                       (progn
                         (ws-send-file
                          process
                          (expand-file-name
                           markdown-preview-file-name
                           (with-current-buffer
                               (gethash (markdown-preview--parse-uuid headers)
                                        markdown-preview--preview-buffers)
                             default-directory
                             ))))
                     (if (string= path "favicon.ico")
                         (ws-send-file process (expand-file-name path markdown-preview--home-dir))
                       (if (and (not (file-directory-p filename)) (file-exists-p filename))
                           (ws-send-file process filename)
                         (ws-send-404 process)
                         ))))))
             markdown-preview-http-port)))))

(defun markdown-preview--parse-uuid (headers)
  "Find uuid query param in HEADERS."
  (let ((found (cl-find-if (lambda (x)
                             (when (stringp (car x))
                               (equal "uuid" (format "%s" (car x)))))
                           headers)))
    (when found (cdr found))))


(defun markdown-preview--open-browser-preview ()
  "Open the markdown preview in the browser."
  (when (eq markdown-preview-auto-open 'file)
    (browse-url (expand-file-name markdown-preview-file-name default-directory)))
  (when (eq markdown-preview-auto-open 'http)
    (browse-url
     (format "http://localhost:%d/?uuid=%s" markdown-preview-http-port markdown-preview--uuid)))
  (unless markdown-preview-auto-open
    (message
     (format
      "Preview address: http://0.0.0.0:%d/?uuid=%s"
      markdown-preview-http-port
      markdown-preview--uuid))))

(defun markdown-preview--stop-websocket-server ()
  "Stop the `markdown-preview' websocket server."
  (clrhash markdown-preview--preview-buffers)
  (when markdown-preview--local-client
    (websocket-close markdown-preview--local-client))
  (when markdown-preview--websocket-server
    (delete-process markdown-preview--websocket-server)
    (setq markdown-preview--websocket-server nil)
    (clrhash markdown-preview--remote-clients)))

(defun markdown-preview--stop-http-server ()
  "Stop the `markdown-preview' http server."
  (when markdown-preview--http-server
    (ws-stop markdown-preview--http-server)
    (setq markdown-preview--http-server nil)))

(defun markdown-preview--drop-closed-clients ()
  "Clean closed clients in `markdown-preview--remote-clients' list."
  (maphash (lambda (ws-uuid websocket)
             (unless (websocket-openp websocket))
             (remhash ws-uuid markdown-preview--remote-clients))
           markdown-preview--remote-clients))

(defun markdown-preview--start-websocket-server ()
  "Start `markdown-preview' websocket server."
  (when (not markdown-preview--websocket-server)
    (setq markdown-preview--websocket-server
          (websocket-server
           markdown-preview-ws-port
           :host markdown-preview-host
           :on-message (lambda (websocket frame)
                         (let ((ws-frame-text (websocket-frame-payload frame)))
                           (if (and
				(stringp ws-frame-text)
				(string-prefix-p "MDPM-Register-UUID: " ws-frame-text))
                               (let ((ws-uuid (substring ws-frame-text 20)))
                                 (puthash ws-uuid websocket markdown-preview--remote-clients)
                                 (markdown-preview--send-preview-to websocket ws-uuid))
                             (progn
                               (websocket-send
                                (gethash markdown-preview--uuid markdown-preview--remote-clients)
                                frame))
                             )))
           :on-open (lambda (websocket) (message "Websocket opened"))
           :on-error (lambda (websocket type err) (message (format "====> Error: %s" err)))
           :on-close (lambda (websocket) (markdown-preview--drop-closed-clients))))
    (add-hook 'kill-emacs-hook 'markdown-preview--stop-websocket-server))
  (markdown-preview--open-browser-preview))

(defun markdown-preview--start-local-client ()
  "Start the `markdown-preview' local client."
  (when (not markdown-preview--local-client)
    (setq markdown-preview--local-client
          (websocket-open
           (format "ws://%s:%d" markdown-preview-host markdown-preview-ws-port)
           :on-error (lambda (ws type err)
                       (message "error connecting"))
           :on-close (lambda (websocket)
                       (setq markdown-preview--local-client nil))))))

(defun markdown-preview--send-preview (preview-uuid)
  "Send the `markdown-preview' preview to clients."
  (when (bound-and-true-p markdown-preview-mode)
    (markdown-preview--send-preview-to markdown-preview--local-client preview-uuid)))

(defun markdown-preview--send-preview-to (websocket preview-uuid)
  "Send the `markdown-preview' to a specific WEBSOCKET."
  (let ((mark-position-percent
         (number-to-string
          (truncate
           (* 100
              (/
               (float (-  (line-number-at-pos) (/ (count-screen-lines (window-start) (point)) 2)))
               (count-lines (point-min) (point-max))))))))

    (let ((md-buffer (gethash preview-uuid markdown-preview--preview-buffers)))
      (when md-buffer
        (with-current-buffer md-buffer

          (markdown markdown-output-buffer-name))))

    (with-current-buffer markdown-output-buffer-name ;; get-buffer
      (websocket-send-text websocket
                           (concat
                            "<div>"
                            "<span id='position-percentage'>"
                            mark-position-percent
                            "</span>"
                            "<div id='content'>"
                            (buffer-substring-no-properties (point-min) (point-max))
                            "</div>"
                            "</div>")
                           ))))

(defun markdown-preview--start ()
  "Start `markdown-preview' mode."
  (setq-local markdown-preview--uuid (uuidgen-1))
  (puthash markdown-preview--uuid (buffer-name) markdown-preview--preview-buffers)
  ;;  (gethash markdown-preview--uuid markdown-preview--preview-buffers)
  (markdown-preview--read-preview-template
   markdown-preview--uuid
   (expand-file-name markdown-preview-file-name default-directory))
  (markdown-preview--start-websocket-server)
  (markdown-preview--start-local-client)
  (markdown-preview--start-http-server markdown-preview-http-port)
  (setq markdown-preview--idle-timer
   (run-with-idle-timer 2 t (lambda ()
                              (when markdown-preview--uuid
                                (markdown-preview--send-preview markdown-preview--uuid)))))
  (add-hook 'after-save-hook (lambda ()
                               (when markdown-preview--uuid
                                 (markdown-preview--send-preview markdown-preview--uuid))) nil t))

(defun markdown-preview--stop ()
  "Stop `markdown-preview' mode."
  (remove-hook 'after-save-hook 'markdown-preview--send-preview t)
  (markdown-preview--stop-idle-timer)
  (remhash markdown-preview--uuid markdown-preview--preview-buffers)
  (let ((preview-file (concat (file-name-directory (buffer-file-name)) markdown-preview-file-name)))
    (if (file-exists-p preview-file)
        (delete-file preview-file))))

;;;###autoload
(defun markdown-preview-open-browser ()
  "Open the `markdown-preview' in the browser."
  (interactive)
  (markdown-preview--open-browser-preview))

;;;###autoload
(defun markdown-preview-cleanup ()
  "Cleanup `markdown-preview' mode."
  (interactive)
  (markdown-preview--stop-websocket-server)
  (markdown-preview--stop-http-server))

;;;###autoload
(define-minor-mode markdown-preview-mode
  "Markdown preview mode."
  :group 'markdown-preview
  :init-value nil
  (when (not (or
              (equal major-mode 'markdown-mode)
              (equal major-mode 'gfm-mode)))
    (markdown-mode))
  (if markdown-preview-mode
      (markdown-preview--start)
    (markdown-preview--stop)))

(provide 'markdown-preview-mode)

;;; markdown-preview-mode.el ends here
