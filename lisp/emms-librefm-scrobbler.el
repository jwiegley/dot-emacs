;;; emms-librefm-scrobbler.el --- Libre.FM Scrobbing API

;; Copyright (C) 2014  Free Software Foundation, Inc.

;; Author: Yoni Rabkin <yrk@gnu.org>

;; Keywords: emms, libre.fm, GNU FM

;; EMMS is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; EMMS is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
;; or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
;; License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with EMMS; see the file COPYING.  If not, write to the Free
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
;; MA 02110-1301, USA.

;;; Commentary:

;; To use libre.fm you need to add username and password to
;; ~/.authinfo.gpg or an equivalent file understood by auth-source.
;; To enable scrobbling call (emms-librefm-scrobbler-enable).

;;; Code:

(require 'emms-playing-time)
(require 'auth-source)


(defvar emms-librefm-scrobbler-handshake-url
  "turtle.libre.fm"
  "Endpoint for client handshake.")

(defvar emms-librefm-scrobbler-method
  "https"
  "Transfer method.")

(defvar emms-librefm-scrobbler-username nil
  "Libre.fm username.

Note that the preferred way of authenticating is using authinfo
and only setting `emms-librefm-scrobbler-handshake-url'.  See the
manual for details.")

(defvar emms-librefm-scrobbler-password nil
  "Libre.fm user password.

Note that the preferred way of authenticating is using authinfo.
See also `emms-librefm-scrobbler-username'.")

(defvar emms-librefm-scrobbler-debug
  ""
  "Debugging variable to store communication.")

(defvar emms-librefm-scrobbler-session-id
  nil
  "Session ID for Libre.fm.")

(defvar emms-librefm-scrobbler-now-playing-url
  ""
  "URL for getting the track playing.")

(defvar emms-librefm-scrobbler-submission-url
  ""
  "URL for submissions.")

(defvar emms-librefm-scrobbler-track-play-start-timestamp
  nil
  "Time when a track started playing.")

(defvar emms-librefm-scrobbler-display-submissions
  t
  "Whether to display a user message on every submission.")


;;; ------------------------------------------------------------------
;;; authenticate
;;; ------------------------------------------------------------------
(defun emms-librefm-scrobbler--get-auth-detail (token)
  "Return TOKEN from auth-source.
TOKEN is :user of :secret."
  ;; TODO: Maybe we should enable :create t here.  But it could be
  ;; kind of annoying as it makes a pop-up when no name is present.
  (plist-get
   (car (auth-source-search :host (list emms-librefm-scrobbler-handshake-url "libre.fm")
                            :user (unless (equal emms-librefm-scrobbler-username "")
                                    emms-librefm-scrobbler-username)
                            :max 1 :require '(:user :secret)))
   token))

(defun emms-librefm-scrobbler--username ()
  "Return username for libre.fm."
  (or (emms-librefm-scrobbler--get-auth-detail :user)
      emms-librefm-scrobbler-username))

(defun emms-librefm-scrobbler--password ()
  "Return password for libre.fm."
  (let ((token (emms-librefm-scrobbler--get-auth-detail :secret)))
    (cond ((functionp token) (funcall token))
          ((characterp token) token)
          (t emms-librefm-scrobbler-password))))

;;; ------------------------------------------------------------------
;;; handshake
;;; ------------------------------------------------------------------

(defun emms-librefm-scrobbler-handshake-string (url username password)
  "Return the client handshake string."
  (when (= 0 (length url))
    (error "bad url"))
  (when (= 0 (length username))
    (error "bad username"))
  (when (= 0 (length password))
    (error "bad password"))
  (let ((timestamp (format-time-string "%s")))
    (concat emms-librefm-scrobbler-method
	    "://"
	    url "/?"
	    "hs=true" "&"
	    "p=1.2"   "&"
	    "c=emm"   "&"
	    "v=1.0"   "&"
	    "u=" (url-encode-url username) "&"
	    "t=" timestamp "&"
	    "a=" (md5 (concat (md5 password) timestamp)))))

(defun emms-librefm-scrobbler-handshake-call (url username password)
  "Perform client handshake and return a response in a buffer."
  (let ((url-request-method "POST"))
    (let ((response
	   (url-retrieve-synchronously
	    (emms-librefm-scrobbler-handshake-string
	     url username password))))
      (setq emms-librefm-scrobbler-debug
	    (with-current-buffer response
	      (buffer-substring-no-properties (point-min)
					      (point-max))))
      response)))

(defun emms-librefm-scrobbler-handle-handshake-response (resbuf)
  "Handle the client handshake server response."
  (when (not (bufferp resbuf))
    (error "response not a buffer"))
  (with-current-buffer resbuf
    (goto-char (point-min))
    (when (not (re-search-forward "^.*200 OK$" (point-at-eol) t))
      (error "bad HTTP server response"))
    ;; go to the start of the FM response
    (when (not (re-search-forward "\n\n" (point-max) t))
      (error "bad FM server response"))
    (let ((status (buffer-substring (point-at-bol)
				    (point-at-eol))))
      (when (not (string= status "OK"))
	(error "FM server returned: %s" status))
      (let (session-id
	    now-playing-url
	    submission-url)
	(forward-line 1)
	(setq session-id (buffer-substring (point-at-bol)
					   (point-at-eol)))
	(forward-line 1)
	(setq now-playing-url (buffer-substring (point-at-bol)
						(point-at-eol)))
	(forward-line 1)
	(setq submission-url (buffer-substring (point-at-bol)
					       (point-at-eol)))
	(when (or (= 0 (length session-id))
		  (= 0 (length now-playing-url))
		  (= 0 (length submission-url)))
	  (error "couldn't parse FM server response"))
	(setq emms-librefm-scrobbler-session-id      session-id
	      emms-librefm-scrobbler-now-playing-url now-playing-url
	      emms-librefm-scrobbler-submission-url  submission-url)
	(message "handshake successful")))))

(defun emms-librefm-scrobbler-handshake ()
  "Perform client handshake call and handle response."
  (emms-librefm-scrobbler-handle-handshake-response
   (emms-librefm-scrobbler-handshake-call
    emms-librefm-scrobbler-handshake-url
    (emms-librefm-scrobbler--username)
    (emms-librefm-scrobbler--password))))


;;; ------------------------------------------------------------------
;;; submission
;;; ------------------------------------------------------------------

(defun emms-librefm-scrobbler-make-query (track rating)
  "Format the url parameters for scrobbling."
  (setq rating
	(cond ((equal 'love rating) "L")
	      ((equal 'ban rating)  "B")
	      ((equal 'skip rating) "S")
	      (t "")))
  (let ((artist (emms-track-get track 'info-artist))
	(title  (emms-track-get track 'info-title))
	(album  (or (emms-track-get track 'info-album) ""))
	(track-number (emms-track-get track 'info-tracknumber))
	(musicbrainz-id "")
	(track-length (number-to-string
		       (or (emms-track-get track
					   'info-playing-time)
			   0))))
    (if (and artist title)
	(concat
	 "s=" emms-librefm-scrobbler-session-id
	 "&a[0]=" (url-encode-url artist)
	 "&t[0]=" (url-encode-url title)
	 "&i[0]=" (url-encode-url
		   (or emms-librefm-scrobbler-track-play-start-timestamp
		       (format-time-string "%s")))
	 "&o[0]=" "P"
	 "&r[0]=" (url-encode-url rating)
	 "&l[0]=" track-length
	 "&b[0]=" (url-encode-url album)
	 "&n[0]=" track-number
	 "&m[0]=" musicbrainz-id)
      (error "Track title and artist must be known."))))


;;; ------------------------------------------------------------------
;;; asynchronous submission
;;; ------------------------------------------------------------------

(defun emms-librefm-scrobbler-get-response-status ()
  "Check the HTTP header and return the body."
  (let ((ok200 "HTTP/1.1 200 OK"))
    (if (< (point-max) 1)
	(error "No response from submission server"))
    (if (not (string= ok200 (buffer-substring-no-properties (point-min) 16)))
	(error "submission server not responding correctly"))
    (goto-char (point-min))
    (re-search-forward "\n\n")
    (buffer-substring-no-properties
     (point-at-bol) (point-at-eol))))

(defun emms-librefm-scrobbler-make-async-submission-call (track rating)
  "Make asynchronous submission call."
  (let ((flarb (emms-librefm-scrobbler-make-query track rating)))
    (let* ((url-request-method "POST")
	   (url-request-data flarb)
	   (url-request-extra-headers
	    `(("Content-type" . "application/x-www-form-urlencoded"))))
      (url-retrieve emms-librefm-scrobbler-submission-url
		    #'emms-librefm-scrobbler-async-submission-callback
		    (list (cons track rating))))))

(defun emms-librefm-scrobbler-async-submission-callback (status &optional cbargs)
  "Pass response of asynchronous submission call to handler."
  (let ((response (emms-librefm-scrobbler-get-response-status)))
    ;; From the API docs: This indicates that the
    ;; submission request was accepted for processing. It
    ;; does not mean that the submission was valid, but
    ;; only that the authentication and the form of the
    ;; submission was validated.
    (let ((track (car cbargs)))
      (cond ((string= response "OK")
	     (when emms-librefm-scrobbler-display-submissions
	       (message "Libre.fm: Submitted %s"
			(emms-track-get track 'info-title))))
	    ((string= response "BADSESSION")
	     (emms-librefm-scrobbler-handshake)
	     (emms-librefm-scrobbler-make-async-submission-call (car cbargs) (cdr cbargs)))
	    (t
	     (error "unhandled submission failure"))))))


;;; ------------------------------------------------------------------
;;; hooks
;;; ------------------------------------------------------------------

(defun emms-librefm-scrobbler-start-hook ()
  (setq emms-librefm-scrobbler-track-play-start-timestamp
	(format-time-string "%s")))

(defun emms-librefm-scrobbler-stop-hook ()
  "Submit the track to libre.fm if it has been played for 240
seconds or half the length of the track."
  (let ((current-track (emms-playlist-current-selected-track)))
    (let ((track-length (emms-track-get current-track 'info-playing-time)))
      (when (and track-length
		 ;; only submit files
		 (eq (emms-track-type current-track) 'file))
	(when (and
	       ;; track must be longer than 30 secs
	       (> track-length 30)
	       ;; track must be played for more than 240 secs or
	       ;;   half the tracks length, whichever comes first.
	       (> emms-playing-time (min 240 (/ track-length 2))))
	  (emms-librefm-scrobbler-make-async-submission-call
	   current-track nil))))))

(defun emms-librefm-scrobbler-enable ()
  "Enable the scrobbler and submit played tracks."
  (interactive)
  (when (not emms-librefm-scrobbler-session-id)
    (emms-librefm-scrobbler-handshake))
  (add-hook 'emms-player-started-hook
	    'emms-librefm-scrobbler-start-hook t)
  (add-hook 'emms-player-stopped-hook
	    'emms-librefm-scrobbler-stop-hook)
  (add-hook 'emms-player-finished-hook
	    'emms-librefm-scrobbler-stop-hook))

(defun emms-librefm-scrobbler-disable ()
  "Disable the scrobbler and don't submit played tracks."
  (interactive)
  (setq emms-librefm-scrobbler-session-id nil)
  (remove-hook 'emms-player-started-hook
	       'emms-librefm-scrobbler-start-hook)
  (remove-hook 'emms-player-stopped-hook
	       'emms-librefm-scrobbler-stop-hook)
  (remove-hook 'emms-player-finished-hook
	       'emms-librefm-scrobbler-stop-hook))


(provide 'emms-librefm-scrobbler)


;;; emms-librefm-scrobbler.el ends here
