;;; elnode-js.el --- elnode js integration tools -*- lexical-binding: t -*-

;; Copyright (C) 2014  Nic Ferrier

;; Author: Nic Ferrier <nferrier@ferrier.me.uk>
;; Keywords: processes, hypermedia

;; This program is free software; you can redistribute it and/or modify
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

;; Often we make websites with Javascript. Elnode has built in tools
;; to help.

;; elnode-js/browserify -- let's elnode take advantage of browserify
;; to simplify your javascript (by using node's require which
;; browserify translates into the correct browser code).

;;; Code:

(require 'elnode)
(require 'noflet)

(defun elnode-js/node-bin ()
  "Where is the NodeJS binary?

We look in a place provided by `nodejs-repl' package or in
\"~/nodejs\", \"/usr/local/bin\" or in \"/usr/bin\" in that
order."
  (noflet ((file-exists (filename)
             (and (file-exists-p (expand-file-name filename)) filename)))
    (or (and (featurep 'nodejs-repl)
             (symbol-value 'nodejs-repl-command))
        (or (file-exists "~/nodejs/bin/nodejs")
            (file-exists "/usr/local/bin/nodejs")
            (file-exists "/usr/bin/nodejs")))))

(defun elnode-js/browserify-bin (&optional directory)
  "Where is browserify?

We search DIRECTORY, if it's supplied, and then the project root,
if there is one (and if `find-file-in-project' is installed) and
then the `default-directory'."
  (let ((browserify "node_modules/.bin/browserify"))
    (noflet ((file-exists (filename)
               (and (file-exists-p (expand-file-name filename)) filename)))
      (or
       (and directory (file-exists (expand-file-name browserify directory)))
       (and (let ((default-directory (expand-file-name directory)))
              (file-exists
               (expand-file-name
                browserify
                (locate-dominating-file default-directory "node_modules")))))
       (file-exists "node_modules/.bin/browserify")))))

(defun elnode-js/browserify (httpcon docroot path)
  "Run browserify from DOCROOT for the PATH.

Browserify is a nodejs tool that turns nodejs based Javascript
into Javascript that works inside the browser.

nodejs code can use nodejs's `require' form to import modules,
which is simpler than many client side solutions.  So browserify
solves the module problem across node.js and the browser."
  (let ((browserify (elnode-js/browserify-bin docroot))
        (nodejs (elnode-js/node-bin)))
    (when (and nodejs browserify)
      (let ((process-environment
             (cons (format "PATH=%s:%s" nodejs  (getenv "PATH"))
                   process-environment)))
        (let ((default-directory docroot))
          (elnode-http-start httpcon 200 '(Content-type . "application/javascript")))
          (elnode-child-process httpcon browserify (concat docroot path))))))

(defun elnode-js/browserify-send-func (httpcon targetfile)
  "An `elnode-send-file-assoc' function for node.js' browserify.

Associate js with this function in the `elnode-send-file-assoc'
alist to get automatic browserify packaging of JavaScript files
served by `elnode-send-file'.  This includes anything sent by the
elnode webserver.

An easy way of getting this effect is to use
`elnode-make-js-server'."
  (elnode-js/browserify
   httpcon
   (file-name-directory targetfile)
   (file-name-nondirectory targetfile)))

(defvar elnode-make-js-server/docroot-history nil
  "The history for the docroot in `elnode-make-js-server'.")

(defvar elnode-make-js-server/port-history nil
  "The history for the port in `elnode-make-js-server'.")

(defvar elnode-make-js-server/host-history nil
  "The history for the host in `elnode-make-js-server'.")

;;;###autoload
(defun elnode-make-js-server (docroot port &optional host)
  "Make a webserver with additional js browserify support.

See `elnode-make-webserver' for basic webserver details."
  (interactive
   (list
    (if (or (member "package.json" (directory-files default-directory))
            (member "node_modules" (directory-files default-directory)))
        default-directory
        (read-from-minibuffer
         "JS docroot: " default-directory nil nil 
         'elnode-make-js-server/docroot-history
         default-directory))
    (read-from-minibuffer
     "Port: " nil nil nil
     'elnode-make-js-server/port-history)
    (if current-prefix-arg
        (read-from-minibuffer
         "Host: " nil nil nil
         'elnode-make-js-server/host-history)
        elnode-init-host)))
  (let ((handler
         (lambda (httpcon)
           (let ((elnode-send-file-assoc
                  '(("\\.js$" . elnode-js/browserify-send-func))))
             (elnode--webserver-handler-proc
              httpcon docroot elnode-webserver-extra-mimetypes)))))
    (add-to-list
     'elnode--make-webserver-store
     (cons docroot handler))
    (elnode-start handler 
                  :port (string-to-number (format "%s" port))
                  :host host)))

(provide 'elnode-js)

;;; elnode-js.el ends here
