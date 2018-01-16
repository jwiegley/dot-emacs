;;; uuidgen.el --- Provides various UUID generating functions

;; Copyright (C) 2010, 2011, 2014 Kan-Ru Chen

;; Author: Kan-Ru Chen <koster@debian.org>
;; Created: 08 Nov 2010
;; Version: 0.3
;; Keywords: extensions, lisp, tools

;; This file is NOT part of GNU Emacs.

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

;;; Commentary:
;;
;; This is a naive implementation of RFC4122 Universally Unique
;; IDentifier generation in elisp.  Currently implemented are UUID v1
;; v3, v4 and v5 generation.  The resolution of the time based UUID is
;; microseconds, which is 10 times of the suggested 100-nanosecond
;; resolution, but should be enough for general usage.
;;
;; Get development version from git:
;;
;;     git clone git://github.com/kanru/uuidgen-el.git

;;; TODO:
;;
;; * Simplify implementation and interfaces.
;; * Unpack time-based UUID.

;;; Code:

(require 'calc-ext)
(require 'sha1)

(defgroup uuidgen nil
  "UUID generation."
  :group 'extensions
  :group 'tools)

(defcustom uuidgen-suppress-network-info-warnings nil
  "Non-nil means suppress warning messages for missing\
`network-interface-list' or `network-interface-info' support."
  :type 'boolean
  :group 'uuidgen)

(defcustom uuidgen-cid-format-string
  "{ 0x%02x%02x%02x%02x, 0x%02x%02x, 0x%02x%02x, { 0x%02x, 0x%02x, 0x%02x, 0x%02x, 0x%02x, 0x%02x, 0x%02x, 0x%02x } }"
  "Format string used to output CID string."
  :type 'string
  :group 'uuidgen)

(defvar uuidgen-unix-epoch-delta (math-read-radix "1b21dd213814000" 16)
  "The interval between the UUID epoch and the Unix epoch.
That is the number of 100-nanoseconds between
1582-10-15 00:00:00 and 1970-01-01 00:00:00.")

(defcustom uuidgen-interface "eth0"
  "The default interface for time based UUID generation."
  :type 'string
  :group 'uuidgen)

;; Predefined namespace IDs
;; Ref: RFC4122 Appendix C

(defvar uuidgen-ns-dns "6ba7b810-9dad-11d1-80b4-00c04fd430c8"
  "For UUID name string which is a fully-qualified domain name.")

(defvar uuidgen-ns-url "6ba7b811-9dad-11d1-80b4-00c04fd430c8"
  "For UUID name string which is a URL.")

(defvar uuidgen-ns-oid "6ba7b812-9dad-11d1-80b4-00c04fd430c8"
  "For UUID name string which is an ISO OID.")

(defvar uuidgen-ns-x500 "6ba7b814-9dad-11d1-80b4-00c04fd430c8"
  "For UUID name string which is an X.500 DN (in DER or a text output format).")

(defun uuidgen--string-to-octets (string &optional start)
  "Convert UUID string to a list of integers.
STRING should contain a UUID string, the 8-4-4-4-12 format is
preferred.  If START is not nil, start search form START
position."
  (if (string-match "[0-9a-f]\\{2\\}" string start)
      (cons (string-to-number (match-string 0 string) 16)
            (uuidgen--string-to-octets string (match-end 0)))))

(defun uuidgen--decode (id)
  "Convert UUID string to binary representation.
ID should contain a UUID string, the 8-4-4-4-12 format is
preferred."
  (apply (if (fboundp 'unibyte-string)
            'unibyte-string
          'string)
        (uuidgen--string-to-octets id)))

(defun uuidgen--current-unix-clock ()
  "Get the current Unix time as a 100-nanosecond intervals."
  (let* ((unix-time (current-time))
         (high (nth 0 unix-time))
         (low (nth 1 unix-time))
         (micro (nth 2 unix-time)))
    (math-add
     (math-mul 10000000 (math-add (math-mul high #x10000) low))
       (* 10 micro))))

(defun uuidgen--system-clock ()
  "Get the 100-nanosecond intervals after UUID epoch."
  (math-add (uuidgen--current-unix-clock) uuidgen-unix-epoch-delta))

(defun uuidgen--random-clock ()
  "Get a random generated 60 bit clock."
  (calcFunc-random (math-power-of-2 60)))

(defun uuidgen--format-time-low (clock)
  "Format the time_low part of the UUID.
CLOCK should be a integer less than 60 bits."
  (format "%08x" (math-fixnum
                  (math-clip clock 32))))

(defun uuidgen--format-time-mid (clock)
  "Format the time_mid part of the UUID.
CLOCK should be a integer less than 60 bits."
  (format "%04x" (math-fixnum
                  (math-clip
                   (car (math-idivmod clock (math-power-of-2 32))) 16))))

(defun uuidgen--format-time-hi-version (clock &optional ver)
  "Format the time_hi_and_version part of the UUID.
CLOCK should be a integer less than 60 bits.
VER is the UUID variant number.  Valid VER are 1, 3, 4, 5."
  (let ((version (or ver 1)))
    (format "%01x%03x" ver
            (math-fixnum
             (math-clip
              (car (math-idivmod clock (math-power-of-2 48))) 12)))))

(defun uuidgen--format-clock-seq-low (clock)
  "Format the clock_seq_low part of the UUID.
CLOCK should be a integer less than 60 bits."
  (format "%02x" (logand #xFF clock)))

(defun uuidgen--format-clock-seq-hi-reserved (clock)
  "Format the clock_seq_hi_and_reserved part of the UUID.
CLOCK should be a integer less than 60 bits."
  (format "%02x" (logior #x80 (logand #x3F (lsh clock -8)))))

(defun uuidgen--random-address ()
  "Return a address formed by list of random numbers."
  (mapcar (lambda (n) (random 256)) (make-list 6 0)))

(defun uuidgen--random-multicast-address ()
  "Return a random multicast address."
  (let ((addr (uuidgen--random-address)))
    ;; Set multicast bit. RFC4122#4.1.6
    (cons (logior #x10 (car addr))
          (cdr addr))))

(defun uuidgen--get-interface (interfaces &optional default)
  "Return the interface for UUID node information.
The INTERFACES is the same format of `network-interface-list' output.
If DEFAULT is not nil, check whether interface DEFAULT exists first."
  (if (and default (network-interface-info default))
      default
    (let ((ifname (caar interfaces)))
      (if (string= ifname "lo")
          (uuidgen--get-interface (cdr interfaces))
        ifname))))

(defun uuidgen--get-ieee-address ()
  "Return the IEEE address from `network-interface-info'.
The return value is a array consist of the address number.
If there is no interface available then return a random
multicast address list."
  ;; Some platform doesn't have network-interface-* so we have to
  ;; check this.
  (if (and (fboundp 'network-interface-list)
           (fboundp 'network-interface-info))
      (let ((info (network-interface-info
                   (uuidgen--get-interface
                    (network-interface-list) uuidgen-interface))))
        (if (and info
                 (nth 3 info))
            (cdr (nth 3 info))
          (progn
            (or uuidgen-suppress-network-info-warnings
                (display-warning
                 '(uuid network-interface-info)
                 "`network-interface-info' returned nil address.

This means either your NIC has no MAC address or the
`network-interface-info' implementation on your platform is buggy.

Will use random multicast address instead. Although this is suggested
by RFC4122, the result might not be desired.

You can customize `uuidgen-suppress-network-info-warnings' to
disable this warning or by adding the entry (uuid network-interface-info)
to the user option `warning-suppress-types', which is defined in the
`warnings' library.\n"))
            (uuidgen--random-multicast-address))))
    (progn
      (or uuidgen-suppress-network-info-warnings
          (display-warning
           'uuid
           "Missing `network-interface-info' or `network-interface-list' support.

Use random multicast address instead. Although this is suggested
by RFC4122, the result might not be desired.

You can customize `uuidgen-suppress-network-info-warnings' to
disable this warning or by adding the entry (uuid network-interface-info)
to the user option `warning-suppress-types', which is defined in the
`warnings' library.\n"))
      (uuidgen--random-multicast-address))))

(defun uuidgen--format-ieee-address ()
  "Format the IEEE address based node name of UUID."
  (let ((address (uuidgen--get-ieee-address)))
    (mapconcat (lambda (var) (format "%02x" var))
               address "")))

(defun uuidgen--format-random-address ()
  "Format the IEEE address based node name of UUID."
  (let ((address (uuidgen--random-address)))
    (mapconcat (lambda (var) (format "%02x" var))
               address "")))

(defun uuidgen--from-time (clock seq ver addr-function)
  "Generate UUID based on various value.
CLOCK should be a integer less than 60 bits.  SEQ should be a
integer less than 14 bits.  VER is the UUID variant number.
Valid VER are 1, 3, 4, 5.  ADDR-FUNCTION is a function generating
the node information.  Pre-defined ADDR-FUNCTION are
`uuidgen--format-ieee-address' and `uuidgen--format-random-address'."
  (mapconcat 'identity
             (list
              (uuidgen--format-time-low clock)
              (uuidgen--format-time-mid clock)
              (uuidgen--format-time-hi-version clock ver)
              (concat (uuidgen--format-clock-seq-hi-reserved seq)
                      (uuidgen--format-clock-seq-low seq))
              (funcall addr-function))
             "-"))

(defun uuidgen-1 ()
  "Generate time based UUID, aka UUIDv1."
  (let ((clock (uuidgen--system-clock))
        (seq (random)))
    (uuidgen--from-time clock seq 1 'uuidgen--format-ieee-address)))

(defun uuidgen-4 ()
  "Generate UUID form random numbers, aka UUIDv4."
  (let ((clock (uuidgen--random-clock))
        (seq (random)))
    (uuidgen--from-time clock seq 4 'uuidgen--format-random-address)))

(defun uuidgen-from-hash (hash ver)
  "Generate name based UUID form hash HASH and version VER."
  (mapconcat 'identity
             (list
              (substring hash 0 8)
              (substring hash 8 12)
              (concat (number-to-string ver)
                      (substring hash 13 16))
              (format "%04x"
                      (logior #x8000 (logand #x3FFF
                                             (string-to-number (substring hash 16 20) 16))))
              (substring hash 20 32))
             "-"))

(defun uuidgen-3 (ns name)
  "Generate name based UUID using MD5 hash algorithm, aka UUIDv3.
NS should be a generated UUID or predefined namespaces,
`uuidgen-ns-dns', `uuidgen-ns-url', `uuidgen-ns-oid', `uuidgen-ns-x500'.
NAME is the node name string."
  (let ((hash (md5 (concat (uuidgen--decode ns) (string-as-unibyte name)))))
    (uuidgen-from-hash hash 3)))

(defun uuidgen-5 (ns name)
  "Generate name based UUID using SHA-1 hash algorithm, aka UUIDv5.
NS should be a generated UUID or predefined namespaces,
`uuidgen-ns-dns', `uuidgen-ns-url', `uuidgen-ns-oid', `uuidgen-ns-x500'.
NAME is the node name string."
  (let ((hash (sha1 (concat (uuidgen--decode ns) (string-as-unibyte name)))))
    (uuidgen-from-hash hash 5)))

(defun uuidgen-urn (uuid)
  "Return the string representation of a UUID as a URN."
  (concat "urn:uuid:" uuid))

(defun uuidgen-cid (&optional uuid)
  "Return UUID string in CID format that is suitable for COM definition.
If UUID is nil will generate UUIDGEN-4 automatically.
You customize `uuidgen-cid-format-string' to change the default format."
  (let ((raw (uuidgen--string-to-octets (or uuid
                                         (uuidgen-4)))))
    (apply 'format uuidgen-cid-format-string raw)))

;;;###autoload
(defun insert-uuid-cid (uuid)
  "Insert UUID string in CID format that is suitable for COM definition.
If UUID is nil will generate UUIDGEN-4 automatically.
You customize `uuidgen-cid-format-string' to change the default format."
  (interactive (list (read-string "UUID: " (uuidgen-4))))
  (insert (uuidgen-cid uuid)))

;;;###autoload
(defun uuidgen (time-based)
  "Insert UUIDv4 at point. If TIME-BASED is non-nil, insert UUIDv1 instead."
  (interactive "P")
  (if time-based
      (insert (uuidgen-1))
    (insert (uuidgen-4))))

(provide 'uuidgen)
;;; uuidgen.el ends here
