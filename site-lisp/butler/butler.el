;; -*- lexical-binding: t -*-
;;; butler.el --- Client for Jenkins

;; Copyright © 2012-2013 Ashton Kemerling
;;
;; Author: Ashton Kemerling <ashtonkemerling@gmail.com>
;; URL: http://www.github.comc/AshtonKem/Butler.git
;; Version: 0.1.1
;; Keywords: Jenkins, Hudson, CI
;; Package-Requires: ((web "0.3.7"))

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

;; This file is not part of GNU Emacs.

;;; Commentary:

;; Provides an interface to connect to the Jenkins CI server

;;; Installation

;; Will eventually be available in elpa or marmalade


;;; Code:

(defvar butler-servers nil)
(defun butler-buffer ()
  (get-buffer-create "*butler-status*"))

(defvar butler-mode-map
  (let ((map (make-keymap)))
    (define-key map (kbd "g") 'butler-refresh)
    (define-key map (kbd "t") 'trigger-butler-job)
    map))


(define-derived-mode butler-mode fundamental-mode "Butler"
  "A major mode for interacting with various CI servers"
  (use-local-map butler-mode-map))

(require 'json)
(require 'web)
(defun get-server (name)
  (car (delq nil (mapcar #'(lambda (obj)
			     (if (string= name (car (cdr obj)))
				 obj
			       nil))
			 butler-servers))))


(defvar butler-mode-map
  (let ((map (make-keymap)))
    (define-key map (kbd "g") 'magit-status)
    map))


(defun parse-jobs (data)
  (print data)
  (let* ((parsed (json-read-from-string data))
	 (jobs (cdr (assoc 'jobs parsed))))
    jobs))

(defun find-trigger-url (line)
  (let ((start (search "url: " line)))
    (if start
        (substring line (+ start 5)))))

(defun find-trigger-auth ()
  (with-current-buffer (butler-buffer)
    (save-excursion
      (condition-case nil
          (let* ((pos (search-backward "auth: "))
                 (line-start (line-beginning-position))
                 (line-end (line-end-position))
                 (line (buffer-substring line-start line-end))
                 (auth-start (search "auth: " line))
                 (auth-string (substring line (+ auth-start 6))))
            auth-string)
          (search-failed nil)))))

(defun trigger-butler-job ()
  (interactive)
  (with-current-buffer (butler-buffer)
    (let* ((line-start (line-beginning-position))
           (line-end (line-end-position))
           (line (buffer-substring line-start line-end))
           (url (find-trigger-url line))
           (auth (find-trigger-auth)))
      (print url)
      (if (and url auth)
          (web-http-get (lambda (conn headers data))
                        :url url
                        :extra-headers `(("Authorization" . ,auth)))))))


(defun update-butler-status (data target-buffer callback)
  (let ((jobs (parse-jobs data)))
    (with-current-buffer target-buffer
      (mapcar (lambda (job)
		(let ((name (cdr (assoc 'name job)))
		      (inhibit-read-only t)
		      (color (cdr (assoc 'color job)))
                      (url (concat "url: "
                                   (cdr (assoc 'url job))
                                   "build/")))
		  (insert "    ")
		  (cond
		   ((string= color  "red")
		    (insert (propertize "● " 'face `(:foreground ,color))))
		   ((string= color "yellow")
		    (insert (propertize "● " 'face `(:foreground ,color))))
		   ((string= color  "blue")
		    (insert (propertize "● " 'face `(:foreground ,color))))
		   ((string= color  "grey")
		    (insert (propertize "● " 'face `(:foreground ,color))))
                   ((string= color  "aborted")
		    (insert (propertize "● " 'face `(:foreground "grey"))))
		   ((string= color "disabled")
		    (insert (propertize "● " 'face `(:foreground "black"))))
		   ((string= (subseq color -6) "_anime")
		    (insert (propertize "● " 'face `(:foreground ,(subseq color 0 -6)))))
		   (t (insert (concat "Unknown: " "'" color "' "))))
		  (insert name)
                  (insert " ")
                  (insert (propertize url 'invisible t))
		  (insert "\n")))
	      jobs)
      (funcall callback))))

(defun generate-basic-auth (username password)
  (concat "Basic "
            (base64-encode-string
             (concat username ":" password))))

(defun parse-authinfo-file (filename servername)
  (if (file-exists-p filename)
      (with-temp-buffer
        (insert-file-contents filename)
        (search-forward (concat "machine " servername))
        (let* ((line-start (line-beginning-position))
               (line-end (line-end-position))
               (line (buffer-substring line-start line-end))
               (splitted (split-string line " "))
               (filtered (delq "" splitted))
               (username (car (cdr (member "login" filtered))))
               (password (car (cdr (member "password" filtered)))))
          (if (and username password)
              (generate-basic-auth username password))))))

(defun auth-string (server)
  (let* ((args (cdr (cdr server)))
         (name (car (cdr server)))
         (username (cdr (assoc 'server-user args)))
         (password (cdr (assoc 'server-password args)))
         (auth-file (cdr (assoc 'auth-file args))))
    (if auth-file
        (parse-authinfo-file auth-file name)
      (generate-basic-auth username password))))


(defun get-jobs (server buffer callback)
  (lexical-let* ((url-request-method "GET")
	 (args (cdr (cdr server)))
	 (url (cdr (assoc 'server-address args)))
	 (headers
	  `(("Authorization" . ,(auth-string server)))))
    (web-http-get (lambda (httpc header data)
                    (update-butler-status data buffer callback))
                    :url (concat url "/api/json?tree=jobs[name,color,url]")
                    :extra-headers headers)))



(defun draw-butler (buffer callback)
  (with-current-buffer buffer
    (let ((inhibit-read-only t)))
    (dolist (server butler-servers)
      (let ((name (car (cdr server)))
	    (inhibit-read-only t)
	    (address (cdr (assoc 'server-address (cdr (cdr server)))))
            (auth (auth-string server)))
        (goto-char (point-max))
	(insert (concat name " (" address "): "))
        (insert (propertize (concat "auth: "
                                    auth)
                            'invisible t))
        (insert "\n")
	(get-jobs server buffer
                  (if (equal server (car (last butler-servers)))
                      callback
                    (lambda ())))))))


(defun butler-status ()
  (interactive)
  (butler-refresh)
  (switch-to-buffer (butler-buffer)))

(defun butler-refresh ()
  (interactive)
  (lexical-let ((target-point nil)
                (target-buffer (generate-new-buffer "temp")))
    (with-current-buffer (butler-buffer)
      (setq target-point (or (point) 0)))
    (draw-butler target-buffer (lambda ()
                                 (let ((results (buffer-string))
                                       (inhibit-read-only t))
                                   (with-current-buffer (butler-buffer)
                                     (erase-buffer)
                                     (insert results)
                                     (goto-char target-point))
                                   (switch-to-buffer (butler-buffer))
                                   (kill-buffer target-buffer)
                                   (setq buffer-read-only t)
                                   (butler-mode))))))


(provide 'butler)
