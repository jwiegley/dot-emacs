;;; lui-autopaste.el --- Extension for lui for long text input

;; Copyright (C) 2012  Jorgen Schaefer <forcer@forcix.cx>

;; Author: Jorgen Schaefer <forcer@forcix.cx>

;; This file is part of Lui.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This extension for lui will intercept long input and replace it by
;; an URL to a paste service.

;; What is considered "long" is defined by `lui-autopaste-lines'. You
;; can configure which paste service to use by changing
;; `lui-autopaste-function'.

;; Run `enable-lui-autopaste' to enable this.

;;; Code:

(defgroup lui-autopaste nil
  "The Lui autopaste extension."
  :prefix "lui-autopaste-"
  :group 'lui)

(defcustom lui-autopaste-lines 3
  "Starting at this number of lines, Lui will ask to paste the input."
  :type 'integer
  :group 'lui-autopaste)

(defcustom lui-autopaste-function 'lui-autopaste-service-ixio
  "Which paste service to use.

This function will be called with some text as its only argument,
and is expected to return an URL to view the contents."
  :type '(choice (const :tag "ix.io" lui-autopaste-service-ixio)
                 (const :tag "ptpb.pw" lui-autopaste-service-ptpb-pw))
  :group 'lui-autopaste)

;;;###autoload
(defun enable-lui-autopaste ()
  "Enable the lui autopaste feature.

If you enter more than `lui-autopaste-lines' at once, Lui will
ask if you would prefer to use a paste service instead. If you
agree, Lui will paste your input to `lui-autopaste-function' and
replace it with the resulting URL."
  (interactive)
  (add-hook 'lui-pre-input-hook 'lui-autopaste))

;;;###autoload
(defun disable-lui-autopaste ()
  "Disable the lui autopaste feature."
  (interactive)
  (remove-hook 'lui-pre-input-hook 'lui-autopaste))

(defun lui-autopaste ()
  "Check if the lui input is too large. If so, paste it instead."
  (when (and (>= (count-lines (point-min) (point-max))
                 lui-autopaste-lines)
             (y-or-n-p "That's pretty long, would you like to use a paste service instead? "))
    (let ((url (funcall lui-autopaste-function
                        (buffer-substring (point-min)
                                          (point-max)))))
      (delete-region (point-min) (point-max))
      (insert url))))

(defun lui-autopaste-service-ptpb-pw (text)
  "Paste TEXT to ptpb.pw and return the paste url."
  (let ((url-request-method "POST")
        (url-request-extra-headers
         '(("Content-Type" . "application/x-www-form-urlencoded")))
        (url-request-data (format "c=%s" (url-hexify-string text)))
        (url-http-attempt-keepalives nil))
    (let ((buf (url-retrieve-synchronously "https://ptpb.pw/")))
      (unwind-protect
          (with-current-buffer buf
            (goto-char (point-min))
            (if (re-search-forward "^url: \\(.*\\)" nil t)
                (match-string 1)
              (error "Error during pasting to ptpb.pw")))
        (kill-buffer buf)))))

(defun lui-autopaste-service-ixio (text)
  "Paste TEXT to ix.io and return the paste url."
  (let ((url-request-method "POST")
        (url-request-extra-headers
         '(("Content-Type" . "application/x-www-form-urlencoded")))
        (url-request-data (format "f:1=%s" (url-hexify-string text)))
        (url-http-attempt-keepalives nil))
    (let ((buf (url-retrieve-synchronously "http://ix.io/")))
      (unwind-protect
          (with-current-buffer buf
            (goto-char (point-min))
            (if (re-search-forward "\n\n" nil t)
                (buffer-substring (point) (point-at-eol))
              (error "Error during pasting to ix.io")))
        (kill-buffer buf)))))

(provide 'lui-autopaste)
;;; lui-autopaste.el ends here
