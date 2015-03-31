;;; tramp2-enc.el --- Remote file transfer support for TRAMP2

;; Copyright (C) 2001 Free Software Foundation, Inc.

;;; Commentary:

;; This file contains the support code for managing remote file encoding and
;; decoding in TRAMP2.

;; The test functions are called in an active tramp2 connection buffer and can
;; use the `tramp-send-command' interface to run commands on the remote
;; machine for testing the availablity of remote software.

;; Note that using `tramp2-run-command' here is unadvisable as it will *not*
;; do what you want. It will, rather, throw an ugly error at you. :)

;; The send and fetch functions are called in the context of a fully setup
;; connection and should transfer the data in the appropriate direction.

;;; Code:
(eval-when-compile
  (require 'tramp2)
  (defvar tramp2-base64-decode	nil)
  (defvar tramp2-base64-encode	nil))

(require 'base64)
(require 'tramp2-util)


(defconst tramp2-base64-test-value "hello world"
  "Data used to test the remote base64 coder.")


(defun tramp2-base64-supported-p ()
  "Ensure that this buffer is configured for base64 encoding support."
  (and (boundp 'tramp2-base64-decode) tramp2-base64-decode
       (boundp 'tramp2-base64-encode) tramp2-base64-encode))

(defun tramp2-base64-test (connect path)
  "Determine if the connection for PATH supports BASE64 encoding."
  ;; Test the coder for this connection, if any.
  (tramp2-base64-test-coder (tramp2-find-value (tramp2-connect-user connect)
							(tramp2-connect-host connect)
							tramp2-base64-coder)))
    

(defun tramp2-base64-test-coder (coder)
  "Test that CODER has valid and working encoder and decoder routines.
This also sets the current buffer base64 encoding specific data to the
valid encoder/decoder calls.

We return `nil' if any part of the coder does not succeed."
  (and (listp coder)
       (let ((enc (car-safe (cdr-safe (assoc 'encoder coder))))
	     (dec (car-safe (cdr-safe (assoc 'decoder coder))))
	     one)
	 (when (and enc dec)
	   ;; Test the encoder first.
	   (set (make-local-variable 'tramp2-base64-encode)
		(if (stringp enc)
		    (tramp2-base64-test-encoder enc)
		  (catch 'found
		    (while enc
		      (setq one (car enc)
			    enc (cdr enc))
		      (when (tramp2-base64-test-encoder one)
			(throw 'found one))))))
	   ;; Test the decoder.
	   (set (make-local-variable 'tramp2-base64-decode)
		(if (stringp dec)
		    (tramp2-base64-test-decoder dec)
		  (catch 'found
		    (while dec
		      (setq one (car dec)
			    dec (cdr dec))
		      (when (tramp2-base64-test-decoder one)
			(throw 'found one))))))
	   ;; Ensure that we got valid coders...
	   (and tramp2-base64-encode tramp2-base64-decode)))))

(defun tramp2-base64-test-encoder (coder)
  "Test that a base64 encoder works on the remote machine."
  (and (stringp coder)
       (save-match-data
	 ;; Test that the command runs successfully...
	 (and (= 0 (tramp2-send-command
		    (format "echo %s | %s"
			    (tramp2-shell-quote tramp2-base64-test-value)
			    coder)))
	      ;; Test that it's output decodes successfully...
	      (base64-decode-region (point-min) (point-max))
	      ;; Test that it's decoded output is what we put in...
	      (goto-char (point-min))
	      (looking-at (concat "^" tramp2-base64-test-value))))))
    

(defun tramp2-base64-test-decoder (coder)
  "Test that a base64 decoder works on the remote machine."
  (and (stringp coder)
       (save-match-data
	 ;; Test that the command runs successfully...
	 (and (= 0 (tramp2-send-command
		    (format "echo %s | %s"
			    (tramp2-shell-quote
			     (with-temp-buffer
			       (insert tramp2-base64-test-value)
			       (base64-encode-region (point-min) (point-max))
			       (buffer-string)))
			    coder)))
	      ;; Test that the output is what we expected...
	      (goto-char (point-min))
	      (looking-at (concat "^" tramp2-base64-test-value))))))


(defun tramp2-base64-write (source start end file append)
  "Write the data in the SOURCE buffer from START to END to FILE
on the remote machine. If APPEND, append to the file."
  (unless (tramp2-base64-supported-p)
    (tramp2-error "base64 send in non-base64 capable buffer!"))
  (unless (tramp2-util-shell-write file
				   tramp2-base64-decode
				   append
				   (tramp2-base64-encode source start end))
    (tramp2-error (list "base64 send failed"
					   (buffer-string)))))


(defun tramp2-base64-read (start end file)
  "Transfer the bytes from START to END of FILE to the local machine."
  (unless (tramp2-base64-supported-p) 
    (tramp2-error "base64 read in non-base64 capable buffer!"))
  ;; We can just use the shell reader directly. Yay.
  (tramp2-util-shell-read file
			  tramp2-base64-encode
			  #'base64-decode-region
			  start
			  end))


(defun tramp2-base64-encode (source start end)
  "Encode FILE (a local file) as base64 and return the base64 data
as a string."
  (with-temp-buffer
    ;; This shouldn't fail silently. If it does, we need to catch the error
    ;; a little more gracefully, I think.
    (insert-buffer-substring source start end)
    ;; Now, encode the buffer...
    (base64-encode-region (point-min) (point-max))
    ;; Return the encoded content as a string.
    (buffer-string)))


;; uuencode
(defun tramp2-uuencode-test (connect path)
  "Determine if the connection for PATH supports UUENCODE encoding."
  (debug))

(defun tramp2-uuencode-write (source start end file append)
  "Write the data in the SOURCE buffer from START to END to FILE
on the remote machine. If APPEND, append to the file."
  (debug))

(defun tramp2-uuencode-read (start end file)
  "Transfer the bytes from START to END of FILE to the local machine."
  (debug))


(provide 'tramp2-enc)

;; TODO:
;; * Implement the `uuencode' based functionality.
;;
;; * Implement `scp' based transfer functionality.

;;; tramp2-enc.el ends here
