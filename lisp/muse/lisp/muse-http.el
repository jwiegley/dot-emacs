;;; muse-http.el --- publish HTML files over HTTP

;; Copyright (C) 2004, 2005, 2006, 2007, 2008, 2009, 2010
;;   Free Software Foundation, Inc.

;; This file is part of Emacs Muse.  It is not part of GNU Emacs.

;; Emacs Muse is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; Emacs Muse is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Emacs Muse; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;;; Contributors:

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Publishing HTML over HTTP (using httpd.el)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-html)
(require 'muse-project)
(require 'httpd)
(require 'cgi)

(defgroup muse-http nil
  "Options controlling the behavior of Emacs Muse over HTTP."
  :group 'press)

(defcustom muse-http-maintainer (concat "webmaster@" (system-name))
  "The maintainer address to use for the HTTP 'From' field."
  :type 'string
  :group 'muse-http)

(defcustom muse-http-publishing-style "html"
  "The style to use when publishing projects over http."
  :type 'string
  :group 'muse-http)

(defcustom muse-http-max-cache-size 64
  "The number of pages to cache when serving over HTTP.
This only applies if set while running the persisted invocation
server.  See main documentation for the `muse-http'
customization group."
  :type 'integer
  :group 'muse-http)

(defvar muse-buffer-mtime nil)
(make-variable-buffer-local 'muse-buffer-mtime)

(defun muse-sort-buffers (l r)
  (let ((l-mtime (with-current-buffer l muse-buffer-mtime))
        (r-mtime (with-current-buffer r muse-buffer-mtime)))
    (cond
     ((and (null l-mtime) (null r-mtime)) l)
     ((null l-mtime) r)
     ((null r-mtime) l)
     (t (muse-time-less-p r-mtime l-mtime)))))

(defun muse-winnow-list (entries &optional predicate)
  "Return only those ENTRIES for which PREDICATE returns non-nil."
  (let ((flist (list t)))
    (let ((entry entries))
      (while entry
        (if (funcall predicate (car entry))
            (nconc flist (list (car entry))))
        (setq entry (cdr entry))))
    (cdr flist)))

(defun muse-http-prune-cache ()
  "If the page cache has become too large, prune it."
  (let* ((buflist
          (sort (muse-winnow-list (buffer-list)
                                  (function
                                   (lambda (buf)
                                     (with-current-buffer buf
                                       muse-buffer-mtime))))
                'muse-sort-buffers))
         (len (length buflist)))
    (while (> len muse-http-max-cache-size)
      (kill-buffer (car buflist))
      (setq len (1- len)))))

(defvar muse-http-serving-p nil)

(defun muse-http-send-buffer (&optional modified code msg)
  "Markup and send the contents of the current buffer via HTTP."
  (httpd-send (or code 200) (or msg "OK")
              "Server: muse.el/" muse-version httpd-endl
              "Connection: close" httpd-endl
              "MIME-Version: 1.0" httpd-endl
              "Date: " (format-time-string "%a, %e %b %Y %T %Z")
              httpd-endl
              "From: " muse-http-maintainer httpd-endl)
  (when modified
    (httpd-send-data "Last-Modified: "
                     (format-time-string "%a, %e %b %Y %T %Z" modified)
                     httpd-endl))
  (httpd-send-data "Content-Type: text/html; charset=iso-8859-1" httpd-endl
                   "Content-Length: " (number-to-string (1- (point-max)))
                   httpd-endl httpd-endl
                   (buffer-string))
  (httpd-send-eof))

(defun muse-http-reject (title msg &optional annotation)
  (muse-with-temp-buffer
    (insert msg ".\n")
    (if annotation
        (insert annotation "\n"))
    (muse-publish-markup-buffer title muse-http-publishing-style)
    (muse-http-send-buffer nil 404 msg)))

(defun muse-http-prepare-url (target explicit)
  (save-match-data
    (unless (or (not explicit)
                (string-match muse-url-regexp target)
                (string-match muse-image-regexp target)
                (string-match muse-file-regexp target))
      (setq target (concat "page?" target
                           "&project=" muse-http-serving-p))))
  (muse-publish-read-only target))

(defun muse-http-render-page (name)
  "Render the Muse page identified by NAME.
When serving from a dedicated Emacs process (see the httpd-serve
script), a maximum of `muse-http-max-cache-size' pages will be
cached in memory to speed up serving time."
  (let ((file (muse-project-page-file name muse-http-serving-p))
        (muse-publish-url-transforms
         (cons 'muse-http-prepare-url muse-publish-url-transforms))
        (inhibit-read-only t))
    (when file
      (with-current-buffer (get-buffer-create file)
        (let ((modified-time (nth 5 (file-attributes file)))
              (muse-publishing-current-file file)
              muse-publishing-current-style)
          (when (or (null muse-buffer-mtime)
                    (muse-time-less-p muse-buffer-mtime modified-time))
            (erase-buffer)
            (setq muse-buffer-mtime modified-time))
          (goto-char (point-max))
          (when (bobp)
            (muse-insert-file-contents file t)
            (let ((styles (cddr (muse-project muse-http-serving-p)))
                  style)
              (while (and styles (null style))
                (let ((include-regexp
                       (muse-style-element :include (car styles)))
                      (exclude-regexp
                       (muse-style-element :exclude (car styles))))
                  (when (and (or (and (null include-regexp)
                                      (null exclude-regexp))
                                 (if include-regexp
                                     (string-match include-regexp file)
                                   (not (string-match exclude-regexp file))))
                             (not (muse-project-private-p file)))
                    (setq style (car styles))
                    (while (muse-style-element :base style)
                      (setq style
                            (muse-style (muse-style-element :base style))))
                    (if (string= (car style) muse-http-publishing-style)
                        (setq style (car styles))
                      (setq style nil))))
                (setq styles (cdr styles)))
              (muse-publish-markup-buffer
               name (or style muse-http-publishing-style))))
          (set-buffer-modified-p nil)
          (muse-http-prune-cache)
          (current-buffer))))))

(defun muse-http-transmit-page (name)
  "Render the Muse page identified by NAME.
When serving from a dedicated Emacs process (see the httpd-serve
script), a maximum of `muse-http-max-cache-size' pages will be
cached in memory to speed up serving time."
  (let ((inhibit-read-only t)
        (buffer (muse-http-render-page name)))
    (if buffer
        (with-current-buffer buffer
          (muse-http-send-buffer muse-buffer-mtime)))))

(defvar httpd-vars nil)

(defsubst httpd-var (var)
  "Return value of VAR as a URL variable.  If VAR doesn't exist, nil."
  (cdr (assoc var httpd-vars)))

(defsubst httpd-var-p (var)
  "Return non-nil if VAR was passed as a URL variable."
  (not (null (assoc var httpd-vars))))

(defun muse-http-serve (page &optional content)
  "Serve the given PAGE from this press server."
  ;; index.html is really a reference to the project home page
  (if (and muse-project-alist
           (string-match "\\`index.html?\\'" page))
      (setq page (concat "page?"
                         (muse-get-keyword :default
                                           (cadr (car muse-project-alist))))))
  ;; handle the actual request
  (let ((vc-follow-symlinks t)
        (muse-publish-report-threshhold nil)
        muse-http-serving-p
        httpd-vars)
    (save-excursion
      ;; process any CGI variables, if cgi.el is available
      (if (string-match "\\`\\([^&]+\\)&" page)
          (setq httpd-vars (cgi-decode (substring page (match-end 0)))
                page (match-string 1 page)))
      (unless (setq muse-http-serving-p (httpd-var "project"))
        (let ((project (car muse-project-alist)))
          (setq muse-http-serving-p (car project))
          (setq httpd-vars (cons (cons "project" (car project))
                                 httpd-vars))))
      (if (and muse-http-serving-p
               (string-match "\\`page\\?\\(.+\\)" page))
          (muse-http-transmit-page (match-string 1 page))))))

(if (featurep 'httpd)
    (httpd-add-handler "\\`\\(index\\.html?\\|page\\(\\?\\|\\'\\)\\)"
                       'muse-http-serve))

(provide 'muse-http)

;;; muse-http.el ends here
