;;; smime-card.el --- Make smime.el work with card readers

;; Copyright (C) 2005 Brailcom, o.p.s.
;; Author: Milan Zamazal <pdm@zamazal.org>

;; COPYRIGHT NOTICE
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2, or (at your option) any later
;; version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
;; or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
;; for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is a simple wrapper around smime.el allowing to use private keys stored
;; on a smard card.
;;
;; To use it, just put (require 'smime-card) to you Emacs startup file and
;; customize the variable `smime-card-file-keys'.

;;; Code:

(require 'smime)

;;; Configuration

(defcustom smime-card-file-keys '()
  "Alist of certificate files and their corresponding private key card ids.
Each element of the list is of the form (FILE . KEY-ID), where FILE is a
certificate file stored on a regular file system and KEY-ID is the identifier
of the corresponding private key stored on the card.
If FILE begins with the prefix `card:', the certificate is retrieved from the
card under the id following the `card:' prefix in FILE."
  :type '(alist :key-type (file :tag "Certificate file")
                :value-type (string :tag "Key identifier"))
  :group 'smime)

(defcustom smime-card-fetch-certificates nil
  "If non-nil, fetch certificates from the card before verifying messages."
  :type 'boolean
  :group 'smime)

;;; Internals

(defvar smime-card-key nil)

(defun smime-card-key (keyfile)
  (cdr (assoc keyfile smime-card-file-keys)))

(defvar smime-card-engine-command
  "engine dynamic -pre SO_PATH:/usr/lib/opensc/engine_pkcs11.so -pre ID:pkcs11 -pre LIST_ADD:1 -pre LOAD\n")

(defvar smime-card-process-output "")

(defun smime-card-process-filter (process string)
  (setq smime-card-process-output (concat smime-card-process-output string)))

(defun smime-card-wait-for-prompt (process)
  (while (not (string-match "\\(OpenSSL> \\|PIN: \\)$"
                            smime-card-process-output))
    (unless (accept-process-output process 5)
      (message "OpenSSL: Timeout")
      (throw 'error nil)))
  (prog1 (if (string= (match-string 1 smime-card-process-output) "PIN: ")
             'pin
           t)
    (setq smime-card-process-output "")))

(defun smime-card-call-openssl-region (b e buf &rest args)
  (let* ((infile (make-temp-file "smime-card-in"))
         (outfile (make-temp-file "smime-card-out"))
         (cert-on-card (and (string-match "^card:\\(.*\\)$" keyfile)
                            (match-string 1 keyfile)))
         (certfile (and cert-on-card (make-temp-file "smime-card-cert")))
         (args (append args
                       (list "-engine" "pkcs11"
                             "-keyform" "engine"
                             "-inkey" smime-card-key
                             "-in" infile "-out" outfile)))
         (process (start-process "openssl" " *openssl*" smime-openssl-program)))
    (unwind-protect
        (catch 'error
          (when certfile
            (unless (= (call-process "pkcs15-tool" nil nil nil
                                     "-r" cert-on-card "-o" certfile)
                       0)
              (message "pkcs15: Error")
              (throw 'error nil))
            (let ((args* args))
              (while (and args* (not (string= (car args*) "-signer")))
                (setq args* (cdr args*)))
              (setq args* (cdr args*))
              (when args*
                (setcar args* certfile))))
          (setq smime-card-process-output "")
          (set-process-filter process 'smime-card-process-filter)
          (unless (eq (smime-card-wait-for-prompt process) t)
            (message "OpenSSL: Error on startup")
            (throw 'error nil))
          (process-send-string process smime-card-engine-command)
          (unless (eq (smime-card-wait-for-prompt process) t)
            (message "OpenSSL: Error in pkcs11 loading")
            (throw 'error nil))
          (write-region b e infile nil 0)
          (process-send-string process
                               (concat (mapconcat 'identity args " ") "\n"))
          (let ((answer (smime-card-wait-for-prompt process)))
            (cond
             ((eq answer 'pin)
              (process-send-string process (concat (read-passwd "Smartcard PIN: ") "\n"))
              (unless (eq (smime-card-wait-for-prompt process) t)
                (message "OpenSSL: Error after passphrase")
                (throw 'error nil)))
             ((eq answer t)
              nil)
             (t
              (message "OpenSSL: Error in processing")
              (throw 'error nil))))
          (process-send-eof process)
          (with-current-buffer (car buf)
            (when (= (cadr (insert-file-contents outfile)) 0)
              (message "OpenSSL: Empty output")
              (throw 'error nil)))
          t)
      (delete-file infile)
      (delete-file outfile)
      (when certfile (delete-file certfile))
      (delete-process process)
      (kill-buffer " *openssl*"))))

;;; smime.el advices

(defadvice smime-sign-region (around smime-card-sign-region activate)
  (let ((smime-card-key (smime-card-key (ad-get-arg 2))))
    ad-do-it))

(defadvice smime-decrypt-region (around smime-card-decrypt-region activate)
  (let ((smime-card-key (smime-card-key (ad-get-arg 2))))
    ad-do-it))

(defadvice smime-call-openssl-region (around smime-card-openssl activate)
  (if smime-card-key
      (setq ad-return-value
            (apply 'smime-card-call-openssl-region (ad-get-args 0)))
    ad-do-it))

(defadvice smime-verify-region (around smime-card-verify-region activate)
  (if smime-card-fetch-certificates
      (let ((cert-ids '()))
        (with-temp-buffer
          (unless (= (call-process
                      "pkcs15-tool" nil t nil "--list-certificates")
                     0)
            (error "pkcs15: Certificate listing"))
          (goto-char (point-min))
          (while (re-search-forward "^[\t ]+ID[ ]+: \\([0-9]+\\) *$" nil t)
            (setq cert-ids (cons (match-string 1) cert-ids))))
        (let ((certfile (make-temp-file "smime-card")))
          (unwind-protect
              (progn
                (with-temp-file certfile
                  (when smime-CA-file
                    (insert-file-contents smime-CA-file))
                  (mapc (lambda (id)
                          (unless (= (call-process "pkcs15-tool" nil t nil
                                                   "-r" id)
                                     0)
                            (error "pkcs15: Certificat read")))
                        cert-ids))
                (let ((smime-CA-file certfile))
                  ad-do-it))
            (delete-file certfile))))
    ad-do-it))

(defadvice mml-smime-verify (around smime-card-mml-smime-verify activate)
  ;; If both smime-CA-directory and smime-CA-file are unset, `mml-smime-verify'
  ;; refuses to perform certificate verification.
  (let ((smime-CA-file (if smime-card-fetch-certificates
                           (or smime-CA-file "/dev/null")
                         smime-CA-file)))
    ad-do-it))

;;; Announce

(provide 'smime-card)

;;; smime-card.el ends here
