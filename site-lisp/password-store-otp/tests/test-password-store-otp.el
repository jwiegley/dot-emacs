;;; test-password-store-otp.el --- 
;; 
;; Filename: test-password-store-otp.el
;; Description: 
;; Author: Daniel Barreto
;; Maintainer: 
;; Created: Mon Aug 28 13:35:31 2017 (+0200)
;; Version: 
;; Package-Requires: ()
;; Last-Updated: 
;;           By: 
;;     Update #: 0
;; URL: 
;; Doc URL: 
;; Keywords: 
;; Compatibility: 
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Commentary: 
;; 
;; 
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Change Log:
;; 
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

(require 'buttercup)
(require 'dash)
(require 'password-store-otp)

(describe "get uri"
  :var (file-contents)

  (before-each
    (setq file-contents "thisisapassword!\n\nhttps://some-url.com\n%s"))

  (it "returns uri in file"
    (let ((uri "otpauth://totp/totp-secret?secret=AAAAAAAAAAAAAAAA&issuer=totp-secret"))
      (spy-on 'password-store--run-show :and-return-value (format file-contents uri))
      (expect (password-store-otp--get-uri "some-pass") :to-equal uri)))

  (it "returns only the first uri in file"
    (let ((uri "otpauth://first/secret\notpauth://second/secret"))
      (spy-on 'password-store--run-show :and-return-value (format file-contents uri))
      (expect (password-store-otp--get-uri "some-pass") :to-equal "otpauth://first/secret")))

  (it "throws error if no uri in file"
    (spy-on 'password-store--run-show :and-return-value (format file-contents ""))
    (expect (password-store-otp--get-uri "some-pass") :to-throw 'error)))

(describe "otp token"
  (it "calls `pass otp <entry>`"
    (let ((entry "some-entry")
          (token  "123456"))
      (spy-on 'password-store--run :and-return-value token)
      (expect (password-store-otp-token entry) :to-equal token)
      (expect 'password-store--run :to-have-been-called-with "otp" entry))))

(describe "otp uri"
  (it "calls `pass otp uri <entry>`"
    (let ((entry "some-entry")
          (uri   "otpauth://some/secret"))
      (spy-on 'password-store--run :and-return-value uri)
      (expect (password-store-otp-uri entry) :to-equal uri)
      (expect 'password-store--run :to-have-been-called-with "otp" "uri" entry))))

(describe "otp token copy"
  :var (entry token)

  (before-each
    (setq entry "some-entry")
    (setq token "12345")
    (spy-on 'message)
    (spy-on 'password-store--run :and-return-value token)
    (password-store-otp-token-copy entry))

  (it "calls `pass otp <entry>`"
    (expect 'password-store--run :to-have-been-called-with "otp" entry))

  (it "puts a token into the kill-ring"
    (expect (car kill-ring-yank-pointer) :to-equal token))

  (it "clears previous pass secrets and handles automatic deletion"
    (expect password-store-timeout-timer)))

(describe "otp uri copy"
  :var (entry uri)

  (before-each
    (setq entry "some-entry")
    (setq uri "otpauth://some/secret")
    (spy-on 'message)
    (spy-on 'password-store--run :and-return-value uri)
    (password-store-otp-uri-copy entry))

  (it "calls `pass otp uri <entry>`"
    (expect 'password-store--run :to-have-been-called-with "otp" "uri" entry))

  (it "puts the uri into the kill-ring"
    (expect (car kill-ring-yank-pointer) :to-equal uri))

  (it "clears previous pass secrets and handles automatic deletion"
    (expect password-store-timeout-timer)))

(describe "otp qrcode"
  :var (entry)

  (before-each
    (setq entry "some-entry"))

  (it "when called without TYPE, calls `pass otp uri -q <entry>`"
    (spy-on 'password-store--run)
    (password-store-otp-qrcode entry)
    (expect 'password-store--run :to-have-been-called-with "otp" "uri" "-q" entry))

  (it "when called with TYPE, calls `qrcode -o - -t<type> <uri at entry>`"
    (let ((file-contents "thisisapassword!\n\nhttps://some-url.com\n%s")
          (uri "otpauth://totp/totp-secret?secret=AAAAAAAAAAAAAAAA&issuer=totp-secret"))
      (spy-on 'shell-command-to-string :and-return-value "<the qr code>")
      (spy-on 'password-store--run-show :and-return-value (format file-contents uri))
      (expect (password-store-otp-qrcode entry "ASCII") :to-equal "<the qr code>")
      (expect 'password-store--run-show :to-have-been-called-with entry)
      (expect 'shell-command-to-string :to-have-been-called-with
              (format "qrencode -o - -tASCII %s"
                      (shell-quote-argument uri))))))

(describe "otp insert"
  (it "calls `pass otp insert -f <entry>`"
    (let* ((secret "otpauth://some/secret")
           (password-store-executable "pass")
           (entry "some-entry")
           (cmd (format "echo %s | %s otp insert -f %s"
                        (shell-quote-argument secret)
                        password-store-executable
                        (shell-quote-argument entry))))
      (spy-on 'shell-command-to-string)
      (spy-on 'message)
      (password-store-otp-insert entry secret)
      (expect 'shell-command-to-string :to-have-been-called-with cmd))))

(describe "otp append"
  (it "calls `pass otp append -f <entry>`"
    (let* ((secret "otpauth://some/secret")
           (password-store-executable "pass")
           (entry "some-entry")
           (cmd (format "echo %s | %s otp append -f %s"
                        (shell-quote-argument secret)
                        password-store-executable
                        (shell-quote-argument entry))))
      (spy-on 'shell-command-to-string)
      (spy-on 'message)
      (password-store-otp-append entry secret)
      (expect 'shell-command-to-string :to-have-been-called-with cmd))))

(describe "append from image"
  :var (entry uri qr-fname)

  (before-each
    (setq entry "some-entry")
    (setq uri "otpauth://some/secret")
    (spy-on 'call-process :and-return-value 0)
    (spy-on 'shell-command-to-string :and-return-value uri)
    (spy-on 'delete-file)
    (spy-on 'message))

  (it "throws error when clipboard image is unavailable"
    (spy-on 'call-process :and-return-value 1)
    (expect (password-store-otp-append-from-image "some-entry") :to-throw 'error))

  (describe "when `password-store-otp-screenshots-path` is not set,"
    (before-each
      (let ((password-store-executable "pass"))
        (spy-on 'call-process :and-call-fake (lambda (&rest _) (insert uri) 0))
        (password-store-otp-append-from-image entry)
        (setq qr-fname (car (last (spy-calls-args-for 'call-process 0))))))

    (it "uses a temporary image to save the screenshot"
      (expect (spy-calls-count 'call-process) :to-equal 2)
      ;; call-process -- import screenshot
      (expect (-butlast (spy-calls-args-for 'call-process 0)) :to-equal '("import" nil nil nil))
      (expect qr-fname :to-match (format "/tmp/%s.*\.png" entry))
      ;; zbarimg call
      (expect (spy-calls-args-for 'call-process 1)
              :to-equal
              `("zbarimg" nil t nil "-q" "--raw" ,qr-fname))
      ;; password-store-otp-append
      (expect (spy-calls-args-for 'shell-command-to-string 0)
              :to-equal
              (list (format "echo %s | pass otp append -f %s"
                            (shell-quote-argument uri)
                            (shell-quote-argument entry)))))

    (it "and deletes it at the end"
      (expect 'delete-file :to-have-been-called-with qr-fname)))

  (describe "when `password-store-otp-screenshots-path` is set,"
    (before-each
      (let ((password-store-executable "pass")
            (password-store-otp-screenshots-path "/home/test/path")
            (entry "some/entry"))
        (spy-on 'call-process :and-call-fake (lambda (&rest _) (insert uri) 0))
        (password-store-otp-append-from-image entry)
        (setq qr-fname (car (last (spy-calls-args-for 'call-process 0))))))

    (it "uses it to save the screenshot taken"
      (expect (spy-calls-count 'call-process) :to-equal 2)
      ;; call-process -- import screenshot
      (expect (-butlast (spy-calls-args-for 'call-process 0)) :to-equal '("import" nil nil nil))
      (expect qr-fname :to-match (format "/home/test/path/entry.*\.png" entry))
      ;; zbarimg call
      (expect (spy-calls-args-for 'call-process 1)
              :to-equal
              `("zbarimg" nil t nil "-q" "--raw" ,qr-fname))
      ;; password-store-otp-append
      (expect (spy-calls-args-for 'shell-command-to-string 0)
              :to-equal
              (list (format "echo %s | pass otp append -f %s"
                            (shell-quote-argument uri)
                            (shell-quote-argument "some/entry")))))

    (it "and doesn't delete the image at the end"
      (expect 'delete-file :not :to-have-been-called))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test-password-store-otp.el ends here
