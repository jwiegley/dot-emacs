;; pg-response.el  Proof General response buffer mode.
;;
;; Copyright (C) 1994-2002 LFCS Edinburgh. 
;; Authors:   David Aspinall, Healfdene Goguen, 
;;		Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Response buffer mode
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-and-compile
(define-derived-mode proof-universal-keys-only-mode fundamental-mode
    proof-general-name "Universal keymaps only"
    ;; Doesn't seem to supress TAB, RET
    (suppress-keymap proof-universal-keys-only-mode-map 'all)
    (proof-define-keys proof-universal-keys-only-mode-map 
		       proof-universal-keys)))

(eval-and-compile
(define-derived-mode proof-response-mode proof-universal-keys-only-mode
  "PGResp" "Responses from Proof Assistant"
  (setq proof-buffer-type 'response)
  (define-key proof-response-mode-map [q] 'bury-buffer)
  (easy-menu-add proof-response-mode-menu proof-response-mode-map)
  (easy-menu-add proof-assistant-menu proof-response-mode-map)
  (proof-toolbar-setup)
  (setq proof-shell-next-error nil)	; all error msgs lost!
  (erase-buffer)))

(easy-menu-define proof-response-mode-menu
		  proof-response-mode-map
		  "Menu for Proof General response buffer."
		  (cons proof-general-name 
			(append
			 proof-toolbar-scripting-menu
			 proof-shared-menu
			 proof-config-menu
			 proof-bug-report-menu)))


(defun proof-response-config-done ()
  "Complete initialisation of a response-mode derived buffer."
  (proof-font-lock-configure-defaults nil)
  (proof-x-symbol-configure))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; Multiple frames for goals and response buffers
;;
;;  -- because who's going to bother do this by hand?
;;

(defvar proof-shell-special-display-regexp nil
  "Regexp for special-display-regexps for multiple frame use.
Internal variable, setting this will have no effect!")

(defun proof-multiple-frames-enable ()
  (cond
   (proof-multiple-frames-enable
    (setq special-display-regexps
	  (union special-display-regexps 
		 (list proof-shell-special-display-regexp)))
    ;; If we're on XEmacs with toolbar, turn off toolbar and
    ;; menubar for the small frames to save space.
    ;; FIXME: this could be implemented more smoothly
    ;; with property lists, and specifiers should perhaps be set
    ;; for the frame rather than the buffer.  Then could disable
    ;; minibuffer, too.
    ;; FIXME: add GNU Emacs version here.
    (if (featurep 'toolbar) 
	(proof-map-buffers
	 (list proof-response-buffer proof-goals-buffer proof-trace-buffer)
	 (set-specifier default-toolbar-visible-p nil (current-buffer))
	 ;; (set-specifier minibuffer (minibuffer-window) (current-buffer))
	 (set-specifier has-modeline-p nil (current-buffer))
	 (set-specifier menubar-visible-p nil (current-buffer))
	 ;; gutter controls buffer tab visibility in XE 21.4
	 (and (boundp 'default-gutter-visible-p)
	      (set-specifier default-gutter-visible-p nil (current-buffer)))))
    ;; Try to trigger re-display of goals/response buffers,
    ;; on next interaction.  
    ;; FIXME: would be nice to do the re-display here, rather
    ;; than waiting for next re-display
    (delete-other-windows 
     (if proof-script-buffer
	 (get-buffer-window proof-script-buffer t))))
   (t
    ;; FIXME: would be nice to kill off frames automatically,
    ;; but let's leave it to the user for now.
    (setq special-display-regexps
	  (delete proof-shell-special-display-regexp 
		  special-display-regexps)))))




(provide 'pg-response)
;; pg-response.el ends here.
