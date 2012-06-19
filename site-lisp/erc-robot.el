;;; erc-robot.el --- A robot for ERC.

;; Author: David Edmondson (dme@dme.org)
;; Maintainer: David Edmondson (dme@dme.org)
;; Version: $Revision$
;; Keywords: ERC, IRC, chat, robot, bot

;; Copyright (C) 2002 David Edmondson.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; This code implements a simple robot for ERC.

;; Installation:

;; The robot uses hooks to gain access to ERC.  The following need to
;; be executed after ERC has loaded:

;;     (load-library "erc-robot")
;;     (add-hook 'erc-server-PRIVMSG-functions 'erc-robot-remote t)
;;     (add-hook 'erc-send-completed-hook 'erc-robot-local t)

;; It is particularly important that the remote robot function is added
;; to the tail of the PRIVMSG hook.

;; Robot commands are declared using the list "erc-robot-commands".
;; TODO: better description of the functions.
;; An example might be:

;; (setq erc-robot-commands
;;       '(
;; 	("cmds" t (lambda (args)
;; 		  (concat "commands available: "
;; 			  (mapconcat
;; 			   (lambda (e)
;; 			     (car e))
;; 			   erc-robot-commands " "))))
;; 	("hello" t (lambda (args) "hello to you too !"))
;; 	("zippy" t (lambda (args) (erc-replace-regexp-in-string "\n" " " (yow))))
;; 	("echo" t (lambda (args) args))
;;	; only i'm allowed to talk to my doctor !
;; 	("version" t (lambda (args) (erc-version)))
;;       ))

(require 'erc)
(require 'erc-stamp)

; compatability
(if (featurep 'xemacs)
    (defun erc-replace-regexp-in-string
      (regexp rep string &optional fixedcase literal subexp start)
      (replace-in-string string regexp rep literal))
  (defalias 'erc-replace-regexp-in-string 'replace-regexp-in-string))


(defface erc-robot-face '((t (:foreground "darkslateblue")))
  "Face used for your robot's output."
  :group 'erc-faces)

(defcustom erc-robot-commands nil
  "A list of robot commands and the functions which implement them."
  :group 'erc
  :type '(repeat (list string (choice (const nil) (const t) string) function))
  )

(defun erc-robot-remote (proc parsed)
  "Implements a simple robot for erc.  Messages to the robot are of the form:
\"nick: !command args\", where:
nick	- the nickname of the user who is the target of the command, i.e. the
	  person running the robot,
command	- the specific command,
args	- arguments to the command (optional)."
  (let* ((sspec (aref parsed 1))
         (nick (substring (nth 0 (erc-parse-user sspec)) 1))
         (tgt (car (aref parsed 4)))
         (msg (aref parsed 5)))
    (erc-robot-command proc nick tgt msg nil))
  nil)

(defun erc-robot-local (str)
  "Funnel text typed by the local user to the local robot.  See
\"erc-robot-remote\" for details of the command format."
  (erc-robot-command erc-process (erc-current-nick) (buffer-name) str t))

(defun erc-robot-command (proc from tgt msg locally-generated)
  "Robot worker."
  (let ((me (erc-current-nick)))
    (if (and erc-robot-commands
	     (string-match (concat "^" (regexp-quote me)
				   ": !\\([^ ]+\\) ?\\(.*\\)") msg))
					; this is a robot command to me.
	(let* ((cmd (substring msg (match-beginning 1) (match-end 1)))
	       (args (substring msg (match-beginning 2)))
	       (l (assoc cmd erc-robot-commands))
	       (allowed-users (nth 1 l))
	       (function (nth 2 l))
	       (permitted (or (eq t allowed-users)
			      (and (eq nil allowed-users) locally-generated)
			      (and (stringp allowed-users)
				   (string-match allowed-users
						 (regexp-quote from)))))
	       (reply
		(if permitted
		    (if l
			(funcall function args)
		      (concat "unknown command: " cmd
			      ": try \"cmds\""))
		  (concat "no access to command \"" cmd
			  "\" for " from ".")))
;; dme: this version allows you to cause the robot to do things, for
;;	example you can try "dme: !echo /kick fred", and it will send
;;	to the server "/kick fred", rather than "joe: /kick fred".
;; 	       (full-reply (if (string-match "^/" reply)
;; 			       reply
;; 			     (concat from ": " reply))))
	       (full-reply (concat from ": " reply)))
	  (erc-log (substring-no-properties full-reply))
	  (save-excursion
	    (set-buffer (erc-get-buffer tgt proc))
	    (let* ((inhibit-read-only t)
		   (lines (split-string full-reply "\n"))
		   (multiline-p (< 1 (length lines)))
		   p)
	      (mapc
	       (lambda (line)
		 (goto-char (point-max))
		 (setq p (re-search-backward (erc-prompt)))
		 (insert (erc-format-timestamp (current-time)
					       erc-timestamp-format)
			 "<" me "> ")
		 (erc-put-text-property 0 (length line) 'face
					'erc-robot-face line)
		 (insert line "\n")
		 (save-excursion
		   (save-match-data
		     (save-restriction
		       (narrow-to-region p (point))
		       (run-hook-with-args 'erc-send-modify-hook)
		       (run-hook-with-args 'erc-send-post-hook))))
		 (set-marker (process-mark erc-process) (point))
		 (set-marker erc-insert-marker (point))
		 (goto-char (point-max))

		 (erc-process-input-line (concat line "\n") t multiline-p))
	       lines)))))))

(provide 'erc-robot)
