;;; hash-store --- Content-addressable file storage using SHA512 hashes -*- lexical-binding: t -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 19 May 2025
;; Version: 1.0
;; Keywords: files hash storage
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

;; This package provides a content-addressable file storage system using
;; SHA512 hashes (truncated to 256 bits). Files are stored in a directory
;; hierarchy based on their hash values.

;;; Code:

(require 'cl-lib)
(require 'cl-macs)

(defgroup hash-store nil
  "Content-addressable file storage using SHA512 hashes."
  :group 'files)

(defcustom hash-store-algorithm 'sha512_256
  "Default algorithm to use when hashing store entries."
  :type
  '(choice
    (const :tag "MD5, produces a 32-character signature" md5)
    (const :tag "SHA-1, produces a 40-character signature" sha1)
    (const :tag "SHA-2 (SHA-224), produces a 56-character signature" sha224)
    (const :tag "SHA-2 (SHA-256), produces a 64-character signature" sha256)
    (const :tag "SHA-2 (SHA-384), produces a 96-character signature" sha384)
    (const :tag "SHA-2 (SHA-512), produces a 128-character signature" sha512)
    (const :tag "SHA-2 (SHA512-256), produces a 64-character signature"
           sha512_256))
  :group 'hash-store)

(defcustom hash-store-directory "~/.emacs.d/hash-store"
  "*Directory where hash-store files are stored.
Files are organized in subdirectories based on their hash values.
For example, a file with hash
 08b8c2c0593d64e1fcd0da2e3d1ce380db4b86b339a260c4e05a47b2558bf2e1
would be stored at:
08/b8/c2c0593d64e1fcd0da2e3d1ce380db4b86b339a260c4e05a47b2558bf2e1"
  :type 'directory
  :group 'hash-store)

(defun hash-store-compute-hash (string &optional algorithm)
  "Compute ALGORITHM hash of STRING and return hash as hex string.
If algorithm is nil, use the value of `hash-store-algorithm'."
  (let* ((algo (or algorithm hash-store-algorithm))
         (hash (secure-hash (if (eq algo 'sha512_256) 'sha512 algo)
                            string)))
    (if (eq algo 'sha512_256) (substring hash 0 64) hash)))

(defun hash-store-compute-file-hash (file &optional algorithm)
  "Compute ALGORITHM hash of FILE and return hash as hex string.
If algorithm is nil, use the value of `hash-store-algorithm'."
  (with-temp-buffer
    (set-buffer-multibyte nil)
    (insert-file-contents-literally file)
    (hash-store-compute-hash (buffer-string) algorithm)))

(defun hash-store-hash-to-path (hash)
  "Convert HASH to the full path in the hash store."
  (let ((dir1 (substring hash 0 2))
        (dir2 (substring hash 2 4))
        (filename (substring hash 4)))
    (expand-file-name
     (concat dir1 "/" dir2 "/" filename)
     hash-store-directory)))

(defun hash-store-ensure-directory (hash)
  "Ensure the directory structure exists for HASH."
  (let* ((dir1 (substring hash 0 2))
         (dir2 (substring hash 2 4))
         (dir-path (expand-file-name
                    (concat dir1 "/" dir2)
                    hash-store-directory)))
    (make-directory dir-path t)))

(defun hash-store-add (file &optional move)
  "Add FILE to the hash store.
If MOVE is non-nil, move the file instead of copying it.
Returns the hash of the stored file."
  (unless (file-exists-p file)
    (error "File does not exist: %s" file))
  (let* ((hash (hash-store-compute-file-hash file))
         (dest-path (hash-store-hash-to-path hash)))
    (unless (file-exists-p dest-path)
      (hash-store-ensure-directory hash)
      (if move
          (rename-file file dest-path)
        (copy-file file dest-path))
      ;; Make the file read-only in the filesystem
      (set-file-modes dest-path (logand (file-modes dest-path)
                                        (lognot #o222))))
    hash))

(defun hash-store-save (contents)
  "Add CONTENTS to the hash store.
Returns the hash of the stored file."
  (let* ((hash (hash-store-compute-hash contents))
         (dest-path (hash-store-hash-to-path hash)))
    (unless (file-exists-p dest-path)
      (hash-store-ensure-directory hash)
      (with-temp-buffer
        (set-buffer-multibyte nil)
        (insert contents)
        (write-file dest-path))
      ;; Make the file read-only in the filesystem
      (set-file-modes dest-path (logand (file-modes dest-path)
                                        (lognot #o222))))
    hash))

(defun hash-store-get (hash &optional verify)
  "Return the full pathname of the file with HASH.
If VERIFY is non-nil, verify that the file contents match the hash.
Returns nil if the file doesn't exist or verification fails."
  (let ((path (hash-store-hash-to-path hash)))
    (when (file-exists-p path)
      (if verify
          (when (string= hash (hash-store-compute-file-hash path))
            path)
        path))))

(defun hash-store-verify-file (file)
  "Verify that FILE in the hash store matches its filename hash.
Returns t if valid, nil otherwise."
  (let* ((relative-path (file-relative-name file hash-store-directory))
         (parts (split-string relative-path "/"))
         (expected-hash (concat (nth 0 parts) (nth 1 parts) (nth 2 parts)))
         (actual-hash (hash-store-compute-file-hash file)))
    (string= expected-hash actual-hash)))

(defun hash-store-verify ()
  "Verify all files in the hash store match their filename hashes.
Returns a list of invalid files, or nil if all files are valid."
  (interactive)
  (let ((invalid-files '())
        (total-files 0)
        (valid-files 0))
    (dolist (dir1 (directory-files hash-store-directory t "^[0-9a-f][0-9a-f]$"))
      (when (file-directory-p dir1)
        (dolist (dir2 (directory-files dir1 t "^[0-9a-f][0-9a-f]$"))
          (when (file-directory-p dir2)
            (dolist (file (directory-files dir2 t "^[0-9a-f]+$"))
              (when (file-regular-p file)
                (setq total-files (1+ total-files))
                (if (hash-store-verify-file file)
                    (setq valid-files (1+ valid-files))
                  (push file invalid-files))))))))
    (if (called-interactively-p 'interactive)
        (if invalid-files
            (message "Hash store verification failed: %d/%d files invalid"
                     (length invalid-files) total-files)
          (message "Hash store verification passed: %d files valid" total-files)))
    invalid-files))

(defun hash-store-exists-p (hash)
  "Check if a file with HASH exists in the store."
  (file-exists-p (hash-store-hash-to-path hash)))

(defun hash-store-delete (hash)
  "Delete the file with HASH from the store.
Also removes empty parent directories."
  (let ((path (hash-store-hash-to-path hash)))
    (when (file-exists-p path)
      (delete-file path)
      ;; Try to remove parent directories if empty
      (ignore-errors
        (delete-directory (file-name-directory path))
        (delete-directory (file-name-directory
                           (directory-file-name
                            (file-name-directory path))))))))

(defun hash-store-list ()
  "Return a list of all hashes in the store."
  (let ((hashes '()))
    (dolist (dir1 (directory-files hash-store-directory t "^[0-9a-f][0-9a-f]$"))
      (when (file-directory-p dir1)
        (dolist (dir2 (directory-files dir1 t "^[0-9a-f][0-9a-f]$"))
          (when (file-directory-p dir2)
            (dolist (file (directory-files dir2 t "^[0-9a-f]+$"))
              (when (file-regular-p file)
                (let* ((relative-path (file-relative-name file hash-store-directory))
                       (parts (split-string relative-path "/"))
                       (hash (concat (nth 0 parts) (nth 1 parts) (nth 2 parts))))
                  (push hash hashes))))))))
    (nreverse hashes)))

(provide 'hash-store)

;;; hash-store.el ends here
