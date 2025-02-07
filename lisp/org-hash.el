;;; org-hash --- Support for hashing entries in Org-mode

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 31 Jan 2025
;; Version: 1.0
;; Keywords: org capture task todo context
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

(require 'cl-lib)
(eval-when-compile
  (require 'cl))

(require 'org)

(defgroup org-hash nil
  "Support for hashing entries in Org-mode"
  :group 'org)

(defcustom org-hash-algorithm 'sha512_256
  "Default algorithm to use when hashing Org-mode entries."
  :type '(choice
          (const :tag "MD5, produces a 32-character signature" 'md5)
          (const :tag "SHA-1, produces a 40-character signature" 'sha1)
          (const :tag "SHA-2 (SHA-224), produces a 56-character signature" 'sha224)
          (const :tag "SHA-2 (SHA-256), produces a 64-character signature" 'sha256)
          (const :tag "SHA-2 (SHA-384), produces a 96-character signature" 'sha384)
          (const :tag "SHA-2 (SHA-512), produces a 128-character signature" 'sha512)
          (const :tag "SHA-2 (SHA512-256), produces a 64-character signature" 'sha512_256))
  :group 'org-smart-capture)

(defsubst org-hash-property (&optional algorithm)
  (format "HASH_%s" (or algorithm org-hash-algorithm)))

(defun org-hash--entry (&optional pos algorithm)
  "Compute hash of current Org entry at POS (or current if nil)."
  (save-excursion
    (when pos (goto-char pos))
    (org-back-to-heading)
    (let* ((beg (point))
           (end (save-excursion
                  (outline-next-heading)
                  (point)))
           (body (buffer-substring-no-properties beg end))
           (algo (or algorithm org-hash-algorithm))
           (hash
            (with-temp-buffer
              (insert body)
              (org-mode)
              (goto-char (point-min))
              (org-entry-delete (point) (org-hash-property algorithm))
              (secure-hash (if (eq algo 'sha512_256) 'sha512 algo)
                           (buffer-string)))))
      (if (eq algo 'sha512_256)
          (substring hash 0 64)
        hash))))

(defun org-hash-value (&optional pos algorithm)
  "Return value of hash ALGORITHM for the entry at POS."
  (org-entry-get pos (org-hash-property algorithm)))

(defun org-hash-update (&optional pos algorithm)
  "Update the HASH_<algorithm> property of the current Org entry."
  (interactive)
  (org-entry-put pos (org-hash-property algorithm)
                 (org-hash--entry pos algorithm)))

(defun org-hash-remove (&optional pos algorithm)
  "Update the HASH_<algorithm> property of the current Org entry."
  (interactive)
  (org-entry-delete pos (org-hash-property algorithm)))

(defun org-hash-confirm (&optional pos algorithm raise-error)
  "Update the HASH_<algorithm> property of the current Org entry."
  (interactive)
  (let ((hash (org-hash-value pos algorithm)))
    (when hash
      (if (string= hash (org-hash--entry pos algorithm))
          (if (called-interactively-p 'interactive)
              (message "Hashes MATCH")
            t)
        (if (or raise-error (called-interactively-p 'interactive))
            (error "Hashes DO NOT match at position %s!" pos)
          nil)))))

(defun org-hash-update-or-confirm (&optional pos algorithm)
  "Update the HASH_<algorithm> property of the current Org entry."
  (interactive)
  (unless (org-hash-confirm pos algorithm)
    (org-hash-update pos algorithm)))

(defun org-hash-update-or-confirm-all (&optional algorithm)
  "Update the HASH_<algorithm> property for all Org entries.
If an entry with an earlier hash failes to validated, an error is
produced at that point."
  (interactive)
  (org-map-entries
   #'(lambda ()
       (if (org-hash-value (point) algorithm)
           (org-hash-confirm (point) algorithm t)
         (org-hash-update (point) algorithm)))))

(provide 'org-hash)

;;; org-hash.el ends here
