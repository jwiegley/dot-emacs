;;; web-server-status-codes.el --- Emacs Web Server HTML status codes

;; Copyright (C) 2013-2014  Free Software Foundation, Inc.

;; This software is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This software is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Code:
(defvar ws-status-codes
  '((100 . "Continue")
    (101 . "Switching Protocols")
    (102 . "Processing")
    (200 . "OK")
    (201 . "Created")
    (202 . "Accepted")
    (203 . "Non-Authoritative Information")
    (204 . "No Content")
    (205 . "Reset Content")
    (206 . "Partial Content")
    (207 . "Multi-Status")
    (208 . "Already Reported")
    (226 . "IM Used")
    (300 . "Multiple Choices")
    (301 . "Moved Permanently")
    (302 . "Found")
    (303 . "See Other")
    (304 . "Not Modified")
    (305 . "Use Proxy")
    (306 . "Switch Proxy")
    (307 . "Temporary Redirect")
    (308 . "Permanent Redirect")
    (400 . "Bad Request")
    (401 . "Unauthorized")
    (402 . "Payment Required")
    (403 . "Forbidden")
    (404 . "Not Found")
    (405 . "Method Not Allowed")
    (406 . "Not Acceptable")
    (407 . "Proxy Authentication Required")
    (408 . "Request Timeout")
    (409 . "Conflict")
    (410 . "Gone")
    (411 . "Length Required")
    (412 . "Precondition Failed")
    (413 . "Request Entity Too Large")
    (414 . "Request-URI Too Long")
    (415 . "Unsupported Media Type")
    (416 . "Requested Range Not Satisfiable")
    (417 . "Expectation Failed")
    (418 . "I'm a teapot")
    (419 . "Authentication Timeout")
    (420 . "Method Failure")
    (420 . "Enhance Your Calm")
    (422 . "Unprocessable Entity")
    (423 . "Locked")
    (424 . "Failed Dependency")
    (424 . "Method Failure")
    (425 . "Unordered Collection")
    (426 . "Upgrade Required")
    (428 . "Precondition Required")
    (429 . "Too Many Requests")
    (431 . "Request Header Fields Too Large")
    (440 . "Login Timeout")
    (444 . "No Response")
    (449 . "Retry With")
    (450 . "Blocked by Windows Parental Controls")
    (451 . "Unavailable For Legal Reasons")
    (451 . "Redirect")
    (494 . "Request Header Too Large")
    (495 . "Cert Error")
    (496 . "No Cert")
    (497 . "HTTP to HTTPS")
    (499 . "Client Closed Request")
    (500 . "Internal Server Error")
    (501 . "Not Implemented")
    (502 . "Bad Gateway")
    (503 . "Service Unavailable")
    (504 . "Gateway Timeout")
    (505 . "HTTP Version Not Supported")
    (506 . "Variant Also Negotiates")
    (507 . "Insufficient Storage")
    (508 . "Loop Detected")
    (509 . "Bandwidth Limit Exceeded")
    (510 . "Not Extended")
    (511 . "Network Authentication Required")
    (520 . "Origin Error")
    (522 . "Connection timed out")
    (523 . "Proxy Declined Request")
    (524 . "A timeout occurred")
    (598 . "Network read timeout error")
    (599 . "Network connect timeout error"))
  "Possible HTML status codes with names.
From http://en.wikipedia.org/wiki/List_of_HTTP_status_codes.")

(provide 'web-server-status-codes)
;;; web-server-status-codes.el ends here
