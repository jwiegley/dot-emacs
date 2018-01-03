;;; password-store-otp.el --- Password store (pass) OTP extension support           -*- lexical-binding: t -*-
;;
;; Filename: password-store-otp.el
;; Author: Daniel Barreto
;; Created: Tue Aug 22 13:46:01 2017 (+0200)
;; Version: 0.1.0
;; Package-Requires: ((emacs "25") (s "1.9.0") (password-store "0.1"))
;; URL: https://github.com/volrath/password-store-otp.el
;; Keywords: tools, pass
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;; This package provides functions for working with the pass-otp
;; extension for pass ("the standard Unix password manager").
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or (at
;; your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(require 'password-store)
(require 'seq)
(require 's)

(defcustom password-store-otp-screenshots-path nil
  "OTP screenshots directory."
  :group 'password-store
  :type '(choice (const :tag "Off" nil)
                 (file :tag "Expandable file name")))

(defun password-store-otp--otpauth-lines (lines)
  "Return from LINES those that are OTP urls."
  (seq-filter (lambda (l) (string-prefix-p "otpauth://" l))
              lines))

(defun password-store-otp--get-uri (entry)
  "Own version that produces error if ENTRY has no otp uri."
  (let ((url (car (password-store-otp--otpauth-lines
                   (s-lines (password-store--run-show entry))))))
    (when (not url)
      (error "No OTP url found"))
    url))

(defun password-store-otp--safe-copy (secret)
  "Add SECRET to kill ring.

Clear previous password from kill ring.  Pointer to kill ring is
stored in `password-store-kill-ring-pointer'.  SECRET is cleared
after `password-store-timeout' seconds."
  (password-store-clear)
  (kill-new secret)
  (setq password-store-kill-ring-pointer kill-ring-yank-pointer)
  (setq password-store-timeout-timer
        (run-at-time (password-store-timeout) nil 'password-store-clear)))

(defun password-store-otp--get-qr-image-filename (entry)
  "Return a qr-image-filename for given ENTRY."
  (let ((entry-base (file-name-nondirectory entry)))
    (if password-store-otp-screenshots-path
        (let ((fname (format "%s-%s.png"
                             entry-base
                             (format-time-string "%Y-%m-%dT%T"))))
          (expand-file-name fname
                            password-store-otp-screenshots-path))
      (format "/tmp/%s.png" (make-temp-name entry-base)))))

(defmacro password-store-otp--related-error (&rest body)
  "Catch otp related errors in BODY and displays a better error message."
  (declare (indent defun))
  `(condition-case err
       ,@body
     (error
      (let ((error-msg (error-message-string err)))
        (if (string= error-msg "Error: otp is not in the password store.")
            (error "Error: pass extension `pass-otp' is not installed")
          (error error-msg))))))

(defun password-store-otp-token (entry)
  "Return an OTP token from ENTRY."
  (password-store-otp--related-error
    (password-store--run "otp" entry)))

(defun password-store-otp-uri (entry)
  "Return an OTP URI from ENTRY."
  (password-store-otp--related-error
    (password-store--run "otp" "uri" entry)))

(defun password-store-otp-qrcode (entry &optional type)
  "Display a QR code from ENTRY's OTP, using TYPE."
  (if type
      (shell-command-to-string (format "qrencode -o - -t%s %s"
                                       type
                                       (shell-quote-argument (password-store-otp--get-uri entry))))
    (password-store-otp--related-error
      (password-store--run "otp" "uri" "-q" entry))))

(defun password-store-otp-add-uri (method entry uri)
  "Using METHOD, add in ENTRY a URI.

METHOD can be either `append' or `insert', and it will be used as the
primary \"pass otp\" command line verb."
  (unless (memq method '(append insert))
    (error (format "Unrecognized method %s" method)))
  (password-store-otp--related-error
    (password-store--run "otp" "--help"))  ;; make sure otp extension is installed.
  (message "%s" (shell-command-to-string (format "echo %s | %s otp %s -f %s"
                                                 (shell-quote-argument uri)
                                                 password-store-executable
                                                 method
                                                 (shell-quote-argument entry)))))


;;; Interactive functions

;;;###autoload
(defun password-store-otp-token-copy (entry)
  "Copy an OTP token from ENTRY to clipboard."
  (interactive (list (read-string "Password entry: ")))
  (password-store-otp--safe-copy (password-store-otp-token entry))
  (message "Copied %s to the kill ring. Will clear in %s seconds." entry (password-store-timeout)))

;;;###autoload
(defun password-store-otp-uri-copy (entry)
  "Copy an OTP URI from ENTRY to clipboard."
  (interactive (list (read-string "Password entry: ")))
  (password-store-otp--safe-copy (password-store-otp-uri entry))
  (message "Copied %s to the kill ring. Will clear in %s seconds." entry (password-store-timeout)))

;;;###autoload
(defun password-store-otp-insert (entry otp-uri)
  "Insert a new ENTRY containing OTP-URI."
  (interactive (list (read-string "Password entry: ")
                     (read-passwd "OTP URI: " t)))
  (password-store-otp-add-uri 'insert entry otp-uri))

;;;###autoload
(defun password-store-otp-append (entry otp-uri)
  "Append to an ENTRY the given OTP-URI."
  (interactive (list (read-string "Password entry: ")
                     (read-passwd "OTP URI: " t)))
  (password-store-otp-add-uri 'append entry otp-uri))

;;;###autoload
(defun password-store-otp-append-from-image (entry)
  "Check clipboard for an image and scan it to get an OTP URI, append it to ENTRY."
  (interactive (list (read-string "Password entry: ")))
  (let ((qr-image-filename (password-store-otp--get-qr-image-filename entry)))
    (when (not (zerop (call-process "import" nil nil nil qr-image-filename)))
      (error "Couldn't get image from clipboard"))
    (with-temp-buffer
      (condition-case nil
          (call-process "zbarimg" nil t nil "-q" "--raw"
                        qr-image-filename)
        (error
         (error "It seems you don't have `zbar-tools' installed")))
      (password-store-otp-append
       entry
       (buffer-substring (point-min) (point-max))))
    (when (not password-store-otp-screenshots-path)
      (delete-file qr-image-filename))))

(provide 'password-store-otp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; password-store-otp.el ends here
