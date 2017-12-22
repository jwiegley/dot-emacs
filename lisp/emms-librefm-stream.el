;;; emms-librefm-stream.el --- Libre.FM streaming

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


;;; Code:

(require 'xml)
(require 'emms-playlist-mode)
(require 'emms-librefm-scrobbler)


(defvar emms-librefm-stream-host-url
  "alpha.libre.fm"
  "URL for the streaming host")

(defvar emms-librefm-stream-host-base-path
  ""
  "URL for the streaming host base path")

(defvar emms-librefm-stream-session-id
  ""
  "Session ID for radio.")

(defvar emms-librefm-stream-debug
  ""
  "Temporary debug information.")

(defvar emms-librefm-stream-station-name
  ""
  "Last station name tuned to.")

(defvar emms-librefm-stream-emms-tracklist
  ""
  "List of tracks for streaming.")

(defvar emms-librefm-stream-playlist-buffer-name
  "*Emms GNU FM*"
  "Name for non-interactive Emms GNU FM buffer.")

(defvar emms-librefm-stream-playlist-buffer nil
  "Non-interactive Emms GNU FM buffer.")

(defvar emms-librefm-stream-connect-method "https://"
  "Method of connecting to server.")


;;; ------------------------------------------------------------------
;;; HTTP
;;; ------------------------------------------------------------------

(defun emms-librefm-stream-assert-http ()
  "Assert a sane HTTP response from the server.

This function must be called inside the response buffer. Leaves
point after the HTTP headers."
  (goto-char (point-min))
  (when (not (re-search-forward "^.*200 OK$" (point-at-eol) t))
    (error "bad HTTP server response"))
  ;; go to the start of the FM response
  (when (not (re-search-forward "\n\n" (point-max) t))
    (error "bad FM server response")))


;;; ------------------------------------------------------------------
;;; radio handshake
;;; ------------------------------------------------------------------

(defun emms-librefm-stream-tune-handshake-string ()
  "Create the tune handshake string."
  (when (not emms-librefm-scrobbler-username)
    (error "null username"))
  (when (not emms-librefm-scrobbler-password)
    (error "null password"))
  (let ((url (concat emms-librefm-stream-connect-method
		     emms-librefm-stream-host-url
		     "/radio/handshake.php?"
		     "version=1.3.0.58" "&"
		     "platform=linux" "&"
		     "username=" (url-encode-url emms-librefm-scrobbler-username) "&"
		     "passwordmd5=" (md5 emms-librefm-scrobbler-password) "&"
		     "language=en")))
    url))

(defun emms-librefm-stream-tune-handshake-call ()
  "Make the tune handshake call."
  (let ((url-request-method "POST"))
    (let ((response
	   (url-retrieve-synchronously
	    (emms-librefm-stream-tune-handshake-string))))
      (setq emms-librefm-stream-debug
	    (with-current-buffer response
	      (buffer-substring-no-properties (point-min)
					      (point-max))))
      response)))

(defun emms-librefm-stream-handle-tune-handshake-response (resbuf)
  "Handle the tune handshake server response."
  (when (not (bufferp resbuf))
    (error "response not a buffer"))
  (with-current-buffer resbuf
    (emms-librefm-stream-assert-http)
    (let (radio-session-id
	  base-url
	  base-path
	  (start (point)))

      (if (re-search-forward "^session=\\(.*\\)$" (point-max) t)
	  (setq radio-session-id (match-string-no-properties 1))
	(error "no radio session ID from server"))

      (goto-char start)
      (if (re-search-forward "^base_url=\\(.*\\)$" (point-max) t)
	  (setq base-url (match-string-no-properties 1))
	(error "no base url from server"))

      (goto-char start)
      (if (re-search-forward "^base_path=\\(.*\\)$" (point-max) t)
	  (setq base-path (match-string-no-properties 1))
	(error "no base path from server"))

      (setq emms-librefm-stream-session-id radio-session-id
	    emms-librefm-stream-host-url base-url
	    emms-librefm-stream-host-base-path base-path))

    (message "radio handshake successful")))

(defun emms-librefm-stream-tune-handshake ()
  "Make and handle the tune handshake."
  (emms-librefm-stream-handle-tune-handshake-response
   (emms-librefm-stream-tune-handshake-call)))


;;; ------------------------------------------------------------------
;;; tuning
;;; ------------------------------------------------------------------

(defun emms-librefm-stream-tune-string (session-id station)
  "Create the tune string."
  (when (not session-id)
    (error "null session id"))
  (when (not station)
    (error "null station"))
  (let ((url (concat emms-librefm-stream-connect-method
		     emms-librefm-stream-host-url
		     emms-librefm-stream-host-base-path
		     "/adjust.php?"
		     "session=" session-id "&"
		     "url=" (url-encode-url station))))
    url))

(defun emms-librefm-stream-tune-call (session-id station)
  "Make the tune call."
  (let ((url-request-method "POST"))
    (let ((response
	   (url-retrieve-synchronously
	    (emms-librefm-stream-tune-string
	     session-id station))))
      (setq emms-librefm-stream-debug
	    (with-current-buffer response
	      (buffer-substring-no-properties (point-min)
					      (point-max))))
      response)))

(defun emms-librefm-stream-handle-tune-response (resbuf)
  "Handle the tune server response."
  (when (not (bufferp resbuf))
    (error "response not a buffer"))
  (with-current-buffer resbuf
    (emms-librefm-stream-assert-http)
    (let ((status (buffer-substring (point-at-bol)
				    (point-at-eol))))
      (let (response
	    url
	    stationname
	    (start (point)))

	(if (re-search-forward "^response=\\(.*\\)$" (point-max) t)
	    (setq response (match-string-no-properties 1))
	  (error "no response status code"))
	(when (not (string= response "OK"))
	  (error "tune response not OK"))

	(goto-char start)
	(if (re-search-forward "^url=\\(.*\\)$" (point-max) t)
	    (setq url (match-string-no-properties 1))
	  (error "no url from server"))

	(goto-char start)
	(if (re-search-forward "^stationname=\\(.*\\)$" (point-max) t)
	    (setq stationname (match-string-no-properties 1))
	  (error "no stationname from server"))

	(setq emms-librefm-stream-station-name stationname)

	(message "successfully tuned to: %s" stationname)))))

(defun emms-librefm-stream-tune (station)
  "Make and handle tune call."
  (emms-librefm-stream-handle-tune-response
   (emms-librefm-stream-tune-call
    emms-librefm-stream-session-id
    station)))


;;; ------------------------------------------------------------------
;;; radio.getPlaylist
;;; ------------------------------------------------------------------

(defun emms-librefm-stream-getplaylist-string (radio-session-id)
  "Create the getplaylist string."
  (when (not radio-session-id)
    (error "null radio session id"))
  (let ((url (concat emms-librefm-stream-connect-method
		     emms-librefm-stream-host-url
		     emms-librefm-stream-host-base-path
		     "/xspf.php?"
		     "sk=" radio-session-id "&"
		     "discovery=0"          "&"
		     "desktop=1.3.0.58")))
    url))

(defun emms-librefm-stream-getplaylist-call (session-id)
  "Make the getplaylist call."
  (let ((url-request-method "POST"))
    (let ((response
	   (url-retrieve-synchronously
	    (emms-librefm-stream-getplaylist-string session-id))))
      (setq emms-librefm-stream-debug
	    (with-current-buffer response
	      (buffer-substring-no-properties (point-min)
					      (point-max))))
      response)))

(defun emms-librefm-stream-handle-getplaylist-response (resbuf)
  "Handle the getplaylist server response."
  (when (not (bufferp resbuf))
    (error "response not a buffer"))
  (with-current-buffer resbuf
    (emms-librefm-stream-assert-http)
    (xml-parse-region (point) (point-max))))

(defun emms-librefm-stream-getplaylist ()
  "Make and handle radio.getPlaylist."
  (emms-librefm-stream-handle-getplaylist-response
   (emms-librefm-stream-getplaylist-call
    emms-librefm-stream-session-id)))


;;; ------------------------------------------------------------------
;;; XSPF
;;; ------------------------------------------------------------------

(defun emms-librefm-stream-xspf-find (tag data)
  "Return the tracklist portion of PLAYLIST or nil."
  (let ((tree (copy-tree data))
	result)
    (while (and tree (not result))
      (let ((this (car tree)))
	(when (and (listp this)
		   (eq (car this) tag))
	  (setq result this)))
      (setq tree (cdr tree)))
    result))

(defun emms-librefm-stream-xspf-tracklist (playlist)
  "Return the tracklist portion of PLAYLIST or nil."
  (emms-librefm-stream-xspf-find 'trackList (car playlist)))

(defun emms-librefm-stream-xspf-get (tag track)
  "Return the data associated with TAG in TRACK."
  (nth 2 (emms-librefm-stream-xspf-find tag track)))

(defun emms-librefm-stream-xspf-convert-track (track)
  "Convert TRACK to an Emms track."
  (let ((location (emms-librefm-stream-xspf-get 'location track))
	(title    (emms-librefm-stream-xspf-get 'title track))
	(album    (emms-librefm-stream-xspf-get 'album track))
	(creator  (emms-librefm-stream-xspf-get 'creator track))
	(duration (emms-librefm-stream-xspf-get 'duration track))
	(image    (emms-librefm-stream-xspf-get 'image track)))
    (let ((emms-track (emms-dictionary '*track*)))
      (emms-track-set emms-track 'name location)
      (emms-track-set emms-track 'info-artist creator)
      (emms-track-set emms-track 'info-title title)
      (emms-track-set emms-track 'info-album album)
      (emms-track-set emms-track 'info-playing-time
		      (/ (string-to-number duration)
			 1000))
      (emms-track-set emms-track 'type 'url)
      emms-track)))

(defun emms-librefm-stream-xspf-convert-tracklist (tracklist)
  "Convert TRACKLIST to a list of Emms tracks."
  (let (tracks)
    (mapc
     #'(lambda (e)
	 (when (and (listp e)
		    (eq 'track (car e)))
	   (setq tracks
		 (append tracks
			 `(,(emms-librefm-stream-xspf-convert-track e))))))
     tracklist)
    tracks))


;;; ------------------------------------------------------------------
;;; stream
;;; ------------------------------------------------------------------

(defun emms-librefm-stream-set-librefm-playlist-buffer ()
  "Setup the GNU FM buffer and make it `emms-playlist-buffer'."
  (when (not (buffer-live-p emms-librefm-stream-playlist-buffer))
    (setq emms-librefm-stream-playlist-buffer
	  (emms-playlist-new
	   emms-librefm-stream-playlist-buffer-name)))
  (setq emms-playlist-buffer emms-librefm-stream-playlist-buffer))

(defun emms-librefm-stream-queue ()
  "Queue streaming tracks."
  (let ((tracklist
	 (emms-librefm-stream-xspf-tracklist
	  (emms-librefm-stream-getplaylist))))
    (when (not tracklist)
      (setq emms-librefm-stream-emms-tracklist nil)
      (error "could not find tracklist"))
    (setq emms-librefm-stream-emms-tracklist
	  (emms-librefm-stream-xspf-convert-tracklist tracklist))

    (emms-librefm-stream-set-librefm-playlist-buffer)

    (with-current-emms-playlist
      (goto-char (point-max))
      (save-excursion
	(mapc
	 #'(lambda (track)
	     (emms-playlist-insert-track track))
	 emms-librefm-stream-emms-tracklist)))))

(defun emms-librefm-stream-queue-loader ()
  "Queue more streaming music if needed."
  (with-current-emms-playlist
    (goto-char (if emms-playlist-mode-selected-overlay
		   (overlay-start emms-playlist-mode-selected-overlay)
		 (point-min)))
    (when (and (eq (current-buffer)
		   emms-librefm-stream-playlist-buffer)
	       (not (next-single-property-change (point-at-eol)
						 'emms-track)))
      (emms-librefm-stream-queue))))

(defun emms-librefm-stream (station)
  "Stream STATION from a GNU FM server."
  (interactive "sEnter station URL: ")
  (when (not (stringp station))
    (error "bad argument"))

  (add-hook 'emms-player-finished-hook
	    'emms-librefm-stream-queue-loader)
  
  (emms-librefm-stream-tune-handshake)
  (emms-librefm-stream-tune station)

  (message "tuned to %s, getting playlist..."
	   emms-librefm-stream-station-name)

  (emms-librefm-stream-queue)
  (with-current-emms-playlist
    (emms-playlist-mode-play-current-track)))


(provide 'emms-librefm-stream)

;;; emms-librefm-stream.el ends here
