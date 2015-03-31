;;; tramp2-util.el --- TRAMP2 utility functions

;; Copyright (C) 2001 by Daniel Pittman <daniel@localhost>

;;; Commentary:

;; This module contains routines that are likely to be valuable to
;; user-defined tramp2 code or that are used in multiple modules and don't
;; really fit into the main tramp2.el file.

;;; Code:
(eval-when-compile
  (require 'tramp2))

(require 'shell)

;; Special characters for various shells:
;; When enclosed in double quotes ("), only $, `, \ and " need to be quoted.
;; This is uber-cool and true of any shell I have met thus far...
(defun tramp2-shell-quote (text)
  "Return a string that will be identical to TEXT after Bourne
shell parsing."
  (save-match-data
    (let ((result text)
	  (start 0))
    (while (string-match "[$`\\\"]" result 0)
      (setq result (replace-match "\\\0" nil nil result)
	    start  (match-end 0)))
    (if (> (length result) 0)
	(concat "\"" result "\"")
      result))))

	

(defun tramp2-util-shell-write (file coder append data)
  "Write DATA to FILE on the remote machine, appending to it if
APPEND is not nil. DATA is the encoded data to transmit to the
remote machine and CODER is the executable to decode data on the
remote machine.

This routine returns t if the call succeeds and nil otherwise."
  (let ((end-of-data (format "end of data %x %x"
			     (mod (apply 'logxor (current-time)) (emacs-pid))
			     (apply 'logxor (current-time)))))
    ;; This is the critical operation. Breaking during a write can leave
    ;; god knows what corrupt data in flight to the remote machine...
    (debug)
    (condition-case nil
	(= 0 (tramp2-run-command file (format "%s <<'%s' %s %s\n%s\n%s\n"
					      coder
					      end-of-data
					      (if append ">>" ">")
					      (tramp2-shell-quote
					       (tramp2-path-remote-file file))
					      data
					      end-of-data)))
      (t
       ;; Kill this connection buffer. It's easier than trying to recover
       ;; any other way. We leak the temp file but, heck, it's hardly any
       ;; sort of real loss. Better to leak than to corrupt data.
       (unless tramp2-debug-preserve-evidence
	 (when (buffer-live-p (current-buffer))
	   (kill-buffer (current-buffer))))))))



(defun tramp2-util-shell-read (file encoder decoder start end)
  "Read the bytes from START to END from file on the remote machine.
Use ENCODER to encode it on the remote machine and DECODER to
decode it locally.

ENCODER must be a string, a shell command to run.
DECODER must be a function that accepts two arguments, the start
and end point of the encoded data in the current buffer."
  (when (and start end (> start end))
    (tramp2-error
		  (format "End of data %s less than start of data %s" end start)))
  (unless (and (stringp encoder)
	       (fboundp decoder))
    (tramp2-error
		  (format "Invalid coder specified" encoder decoder)))
  ;; Right, do the actual hacking...
  (tramp2-with-connection file
    (let ((cut (when (and start end tramp2-dd)
		 (format "{ 2>/dev/null %s bs=1 skip=%s count=%s } |"
			 tramp2-dd start (- end start)))))
      (when (= 0 (tramp2-run-command file (format "<%s %s %s"
						  (tramp2-shell-quote
						   (tramp2-path-remote-file file))
						  (or cut "") encoder)))
	;; Got the data, yay.
	(funcall decoder (point-min) (point-max))
	;; Did we clip with dd?
	(when (and start end (not tramp2-dd))
	  ;; Nope, clip ourselves. Sadness.
	  (delete-region (point-min) start)
	  (delete-region end (point-max)))
	;; Return the buffer with the decoded data...
	(current-buffer)))))
				       

(defun tramp2-temp-file-name ()
  "Return a file-name suitable for a temporary file.
FILE is used as a basis for making it unique and all."
  (let* ((dir (tramp2-temp-dir))
	 (prefix (or (and (boundp 'tramp2-temp-name-prefix) tramp2-temp-name-prefix)
		     "tramp2."))
	 ;; Generate the temporary name...
	 (path (funcall (or (and (fboundp 'make-temp-name) #'make-temp-name)
			    (and (fboundp 'make-temp-file) #'make-temp-file)
			    #'tramp2-temp-file-name-internal)
			(concat dir prefix))))
    path))

(defun tramp2-temp-file-name-internal (prefix)
  "If no suitable temp-name generator exists on this system, fake it."
  (apply 'format "%s.%s.%s%s%s" prefix (emacs-pid) (current-time)))
	  

(defun tramp2-getenv (path &optional name)
  "Get the value of the environment variable NAME.
If there is a local value, use that, otherwise try on the machine
at the end of PATH."
  (or (getenv name)
      (and path
	   (tramp2-with-connection path
	     (unless (= 0 (tramp2-run-command path (format "echo ${%s}" name)))
	       (tramp2-error "Unable to expand environment value" name))
	     (buffer-substring (tramp2-point-at-bol) (tramp2-point-at-eol))))))


(defun tramp2-case-insenitive-glob (name)
  "Take NAME and return a shell glob that will match it
in a case-insensitive fashion."
  (mapconcat #'tramp2-case-insenitive-glob-internal name ""))

(defun tramp2-case-insenitive-glob-internal (char)
  "Take char and return a string that is a case-insensitive shell
glob matching it."
  (let ((upper (upcase char))
	(lower (downcase char)))
    (if (eq upper lower)
	(tramp2-shell-quote (string char))
      (format "[%c%c]" upper lower))))


(provide 'tramp2-util)

;;; tramp2-util.el ends here
