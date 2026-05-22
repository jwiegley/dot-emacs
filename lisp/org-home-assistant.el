;;; org-home-assistant --- Home Assistant REST queries for Org-mode -*- lexical-binding: t -*-

;; Copyright (C) 2026 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 21 May 2026
;; Version: 1.0
;; Keywords: org home-assistant presence
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Lightweight helper for asking a local Home Assistant instance for
;; the current state of an entity, with a small per-entity time-bounded
;; cache.  Intended for use inside Org agenda auto-exclusion functions,
;; capture templates, or anywhere else a quick presence/state check is
;; wanted without setting up an asynchronous WebSocket session.
;;
;; Example configuration:
;;
;;   (setq org-home-assistant-base-url "https://hass.example.lan"
;;         org-home-assistant-token
;;         (lambda ()
;;           (lookup-password "hass.example.lan" "you" 443)))
;;
;;   (equal (org-home-assistant-state "person.nasim_wiegley") "home")
;;
;; Network, auth, and parse failures all return nil so callers can
;; fail closed.

;;; Code:

(require 'json)
(require 'url)

(defgroup org-home-assistant nil
  "Home Assistant REST queries for use from Org-mode."
  :group 'org)

(defcustom org-home-assistant-base-url nil
  "Base URL of the Home Assistant instance, e.g. \"https://hass.lan\".
The state endpoint queried is `<URL>/api/states/<ENTITY>'."
  :type '(choice (const :tag "Unset" nil) string))

(defcustom org-home-assistant-token nil
  "Long-lived access token for the Home Assistant REST API.
Either a literal string, or a zero-argument function returning a string
\(so the token can be fetched lazily from `auth-source' or another
secrets store)."
  :type '(choice (const :tag "Unset" nil) string function))

(defcustom org-home-assistant-timeout 3
  "Seconds to wait for a single REST call before giving up."
  :type 'number)

(defcustom org-home-assistant-cache-ttl 60
  "Seconds a state value remains fresh in `org-home-assistant--cache'."
  :type 'integer)

(defvar org-home-assistant--cache nil
  "Internal cache. Alist of (ENTITY . (FETCHED-AT . STATE)).")

(defun org-home-assistant--token ()
  "Resolve `org-home-assistant-token' to a string, or signal."
  (cond
   ((functionp org-home-assistant-token)
    (funcall org-home-assistant-token))
   ((stringp org-home-assistant-token)
    org-home-assistant-token)
   (t (error "`org-home-assistant-token' is not set"))))

(defun org-home-assistant--fetch (entity)
  "Fetch ENTITY's state from Home Assistant. Return string or nil."
  (condition-case _err
      (let* ((url-request-method "GET")
             (url-request-extra-headers
              `(("Authorization" .
                 ,(concat "Bearer " (org-home-assistant--token))))))
        (with-current-buffer
            (url-retrieve-synchronously
             (format "%s/api/states/%s"
                     org-home-assistant-base-url entity)
             t nil org-home-assistant-timeout)
          (unwind-protect
              (progn
                (goto-char (point-min))
                (when (re-search-forward "\r?\n\r?\n" nil t)
                  (let ((json-object-type 'alist)
                        (json-array-type 'list)
                        (json-key-type 'symbol))
                    (alist-get 'state (json-read)))))
            (kill-buffer))))
    (error nil)))

;;;###autoload
(defun org-home-assistant-clear-cache ()
  "Forget all cached Home Assistant state values."
  (interactive)
  (setq org-home-assistant--cache nil))

;;;###autoload
(defun org-home-assistant-state (entity)
  "Return the current state of ENTITY from Home Assistant, or nil on failure.
ENTITY is the full entity id, e.g. \"person.john_wiegley\".  Results are
cached per entity for `org-home-assistant-cache-ttl' seconds."
  (unless org-home-assistant-base-url
    (error "`org-home-assistant-base-url' is not set"))
  (let* ((cell (assoc entity org-home-assistant--cache))
         (now (float-time)))
    (if (and cell (< (- now (cadr cell)) org-home-assistant-cache-ttl))
        (cddr cell)
      (let ((state (org-home-assistant--fetch entity)))
        (setq org-home-assistant--cache
              (cons (cons entity (cons now state))
                    (assoc-delete-all entity org-home-assistant--cache)))
        state))))

(provide 'org-home-assistant)

;;; org-home-assistant.el ends here
