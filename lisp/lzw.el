;;; lzw --- LZW compression algorithm in Emacs Lisp

;; Copyright (C) 2011-2012 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 6 Aug 2011
;; Version: 1.0
;; Keywords: compression data lzw
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

;; This code has not been optimized, and I welcome any improvements.
;; As it is, the resulting conversion of a large Lisp form to a
;; base64-encoded string, using `lzw-compress-data', achieves a
;; compression ratio near 50% over just turning the data into a string
;; with `prin1-to-string'.

(defgroup lzw nil
  "LZW compression algorithm in Emacs Lisp"
  :group 'emacs)

;;; Code:

(eval-when-compile
  (require 'cl))

(defun lzw-compress-string (uncompressed)
  "Compress a string to a list of output symbols."
  ;; Build the dictionary.
  (let* ((dict-size 256)
         (dictionary
          (let ((dict (make-hash-table :size dict-size :test 'equal)))
            (dotimes (i dict-size)
              (puthash (char-to-string i) (char-to-string i) dict))
            dict)))
    (with-temp-buffer
      (let ((w ""))
        (dolist (c (string-to-list uncompressed))
          (let ((wc (concat w (char-to-string c))))
            (if (gethash wc dictionary)
                (setq w wc)
              (insert (gethash w dictionary))
              ;; Add wc to the dictionary.
              (puthash wc (char-to-string dict-size) dictionary)
              (setq dict-size (1+ dict-size)
                    w (char-to-string c)))))
        ;; Output the code for w.
        (if w
            (insert (gethash w dictionary))))
      (buffer-string))))

(defun lzw-decompress-string (compressed)
  "Decompress a list of output ks to a string."
  ;; Build the dictionary.
  (let* ((dict-size 256)
         (dictionary
          (let ((dict (make-hash-table :size dict-size :test 'equal)))
            (dotimes (i dict-size)
              (puthash (char-to-string i) (char-to-string i) dict))
            dict)))
    (with-temp-buffer
      (let* ((compr-list (string-to-list compressed))
             (w (char-to-string (pop compr-list))))
        (insert w)
        (dolist (k compr-list)
          (let ((entry
                 (or (gethash (char-to-string k) dictionary)
                     (if (= k dict-size)
                         (concat w (char-to-string (aref w 0)))
                       (error "Bad compressed k: %s" k)))))
            (insert entry)

            ;; Add w+entry[0] to the dictionary.
            (puthash (char-to-string dict-size)
                     (concat w (char-to-string (aref entry 0)))
                     dictionary)
            (setq dict-size (1+ dict-size)
                  w entry))))
      (buffer-string))))

(defun lzw-compress-data (data)
  (base64-encode-string
   (string-as-unibyte
    (lzw-compress-string
     (prin1-to-string data)))))

(defun lzw-decompress-data (str)
  (read
   (lzw-decompress-string
    (string-as-multibyte
     (base64-decode-string str)))))

(provide 'lzw)

;;; lzw.el ends here
