;; proof.el Major mode for proof assistants Copyright (C) 1994,
;; 1995, 1996 LFCS Edinburgh. This version by Dilip Sequeira, by
;; rearranging Thomas Schreiber's code.

;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>
;; Time-stamp: <22 Nov 96 tms /home/tms/elisp/proof.el>
;; Thanks to David Aspinall, Robert Boyer, Rod Burstall,
;;           James McKinna, Mark Ruys, Martin Steffen, Perdita Stevens  


(require 'compile)
(require 'comint)
(require 'etags)

(autoload 'w3-fetch "w3" nil t)
(autoload 'easy-menu-define "easymenu")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;               Configuration                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar proof-shell-echo-input t
  "If nil, input to the proof shell will not be echoed")

(defvar proof-prog-name-ask-p nil
  "*If t, you will be asked which program to run when the inferior
 process starts up.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Variables used by proof mode, all auto-buffer-local             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro deflocal (var &optional value docstring)
 (list 'make-variable-buffer-local (list 'quote var))
 (list 'defvar var value docstring))

;; These should be set before proof-config-done is called

(deflocal proof-terminal-char)

(make-local-hook 'proof-pre-shell-start-hook)
(make-local-hook 'proof-post-shell-start-hook)

(deflocal proof-comment-start)
(deflocal proof-comment-end)

;; these should be set in proof-shell-start-hook

(deflocal proof-shell-prog-name)
(deflocal proof-shell-process-name)
(deflocal proof-shell-buffer-name)
(deflocal proof-shell-prompt-pattern)
(deflocal proof-shell-mode-is)

(deflocal proof-shell-abort-goal-regexp nil
  "*Regular expression indicating that the proof of the current goal
  has been abandoned.")

(deflocal proof-error-regexp nil
  "A regular expression indicating that the PROOF process has
  identified an error.") 

(deflocal proof-shell-proof-completed-regexp nil
  "*Regular expression indicating that the proof has been completed.")

(deflocal proof-shell-change-goal nil
  "*Command to change to the goal %s")

;; Supply these if you want

(make-local-hook 'proof-shell-safe-send-hook)
(make-local-hook 'proof-shell-exit-hook)

;; These get computed in proof-mode-child-config-done

(deflocal proof-terminal-string)
(deflocal proof-re-end-of-cmd) 
(deflocal proof-re-term-or-comment)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;               Bridging the emacs19/xemacs gulf                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar running-xemacs  nil)
(defvar running-emacs19 nil)

(setq running-xemacs  (string-match "XEmacs\\|Lucid" emacs-version))
(or running-xemacs
    (setq running-emacs19 (string-match "^19\\." emacs-version)))

;; courtesy of Mark Ruys 
(defun emacs-version-at-least (major minor)
  "Test if emacs version is at least major.minor"
  (or (> emacs-major-version major)
      (and (= emacs-major-version major) (>= emacs-minor-version minor)))
)

(defvar extended-shell-command-on-region
  (emacs-version-at-least 19 29)
  "Does `shell-command-on-region' optionally offer to output in an other buffer?")

;; in case Emacs is not aware of read-shell-command-map
(defvar read-shell-command-map
  (let ((map (make-sparse-keymap)))
    (if (not (fboundp 'set-keymap-parents))
        (setq map (append minibuffer-local-map map))
      (set-keymap-parents map minibuffer-local-map)
      (set-keymap-name map 'read-shell-command-map))
    (define-key map "\t" 'comint-dynamic-complete)
    (define-key map "\M-\t" 'comint-dynamic-complete)
    (define-key map "\M-?" 'comint-dynamic-list-completions)
    map)
  "Minibuffer keymap used by shell-command and related commands.")


;; in case Emacs is not aware of the function read-shell-command
(or (fboundp 'read-shell-command)
    ;; from minibuf.el distributed with XEmacs 19.11
    (defun read-shell-command (prompt &optional initial-input history)
      "Just like read-string, but uses read-shell-command-map:
\\{read-shell-command-map}"
      (let ((minibuffer-completion-table nil))
        (read-from-minibuffer prompt initial-input read-shell-command-map
                              nil (or history
                              'shell-command-history)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          A couple of small utilities                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun string-to-list (s separator) 
  "converts strings `s' separated by the character `separator' to a
  list of words" 
  (let ((end-of-word-occurence (string-match (concat separator "+") s)))
    (if (not end-of-word-occurence)
        (if (string= s "") 
            nil
          (list s))
      (cons (substring s 0 end-of-word-occurence) 
            (string-to-list 
             (substring s
                        (string-match (concat "[^" separator "]")
                                      s end-of-word-occurence)) separator)))))



(defun ids-to-regexp (l)
  "transforms a non-empty list of identifiers `l' into a regular
  expression matching any of its elements"
(mapconcat (lambda (s) (concat "\\<" s "\\>")) l "\\|"))

(defun w3-remove-file-name (address)
  "remove the file name in a World Wide Web address"
  (string-match "://[^/]+/" address)
  (concat (substring address 0 (match-end 0))
          (file-name-directory (substring address (match-end 0)))))

(defun occurence (STRING &optional LOWER-BOUND UPPER-BOUND)
  "Counts the number of occurences of STRING in the current buffer
   between the positions LOWER-BOUND and UPPER-BOUND.
   Optional first argument. nil is equivalent to (point-min).
   Optional second argument. nil is equivalent to (point-max)."
  (save-excursion
    (let ((LOWER-BOUND (or LOWER-BOUND (point-min))))
      (goto-char LOWER-BOUND)
      (let ((pos (search-forward STRING UPPER-BOUND t)))
	(if pos (+ 1 (occurence STRING pos UPPER-BOUND)) 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          A few random hacks                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-skip-comments ()
  (forward-comment (buffer-size))
  (point))

; Find the last real semicolon, or point-min, leaving the point after
; the semi and any junk.  Returns nil if we seemto be inside a comment

(defun proof-find-start-of-command ()
   (if (re-search-backward proof-re-term-or-comment nil t)
       (cond ((looking-at proof-terminal-string) 
              (forward-char)
	      (proof-skip-comments))
	     ((looking-at (substring proof-comment-start 0 1)) nil)
	     ((looking-at (substring proof-comment-end 0 1))
	      (if (search-backward proof-comment-start nil t)
		  (if (equal (point) (point-min)) 
		      (proof-skip-comments))
		    (backward-char)
		    (proof-find-start-of-command))
		(point)))
     (goto-char (point-min))
     (proof-skip-comments)))


;; there seems to be some duplication of work here, as one might
;; expect that the functionality of proof-find-end-of-command would be
;; required in proof-process-active-terminator
(defun proof-find-end-of-command (&optional COUNT)
  "Move to the end of the command. COUNT-1 end-of-command symbols
  `proof-terminal-string' are within comments"
  (interactive)
  (let ((point (point))
	(pos   (search-forward proof-terminal-string nil nil COUNT)))
    (and pos
 	;; an end of command has been found
	;; is pos within a comment relative to the starting point of
	;; the search?
	 (> (occurence proof-comment-start point (point))
	    (occurence proof-comment-end   point (point)))
	 (goto-char point)
	 (proof-find-end-of-command (if COUNT (+ 1 COUNT) 2)))))

(defun proof-shell-process ()
  (and (stringp proof-shell-process-name)
       (get-process proof-shell-process-name)))

(defun proof-shell-buffer () 
  (and (stringp proof-shell-buffer-name)
       (get-buffer proof-shell-buffer-name)))

(defun proof-display-buffer (buffer)
  (let ((tmp-buffer (current-buffer)))
    (display-buffer buffer)
    (display-buffer tmp-buffer)))

(defun proof-append-terminator (string)
  (or (and
       (string-match proof-re-end-of-cmd string)
       string)
      (setq string (concat string proof-terminal-string))))
        
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Comint-style stuff: sending input to the process etc    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-input-sender (proc string)
  "Function to actually send to the PROOF process `proc' the `string'
  submitted by the user. It then calls proof-shell-safe-send-hook if safe 
  to do so."
  (comint-simple-send proc string)
  (and (string-match proof-re-end-of-cmd string)
       (run-hooks 'proof-shell-safe-send-hook)))

(defun proof-interrupt-subjob ()
  (interactive)
  (and (proof-shell-process)
       (interrupt-process (proof-shell-process))))

(defun proof-simple-send (string &optional silent)
   "send `string' to the PROOF PROCESS.
    If `silent' is enabled then `string' should not be echoed."
  (or (proof-shell-process) (proof-start-shell))
  (let ((proof-buf (proof-shell-buffer)))
    (if proof-buf
	(save-excursion
	  (progn
	    (set-buffer proof-buf)
	    (goto-char (point-max))
	    (if (and proof-shell-echo-input (not silent))
		(progn
		  (princ string proof-buf)
		  (comint-send-input))
	      (proof-input-sender proof-shell-process-name string)
	      )))
      (message (format "No active %s process" proof-shell-process-name)))))

(defun proof-simulate-send-region (point1 point2 &optional terminator)
  "Send the area between point1 and point2 to the inferior shell running lego."
  (let (str)
    (setq str (buffer-substring point1 point2))
    (and terminator (setq str (proof-append-terminator str)))
    (proof-simple-send str)))

;; proof-send-command tries to figure out where commands start and end
;; without having to parse expressions. Actually needs re-writing.

(defun proof-send-command ()
  "Send current command to inferior shell."  

  (interactive)
  (let (start end)
    (save-excursion
      (setq start (proof-find-start-of-command))
      (if start
	  (setq end (search-forward proof-terminal-string nil t)))
      (if (not end)
	  (setq end (point-max))
	(backward-char))
      (proof-simulate-send-region start end t))))

(defun proof-send-line ()
  "Send current line to inferior shell running proof"
  (interactive)
  (save-excursion
    (let (start end)
      (beginning-of-line 1)
      (setq start (point))
      (end-of-line 1)
      (setq end (point))
      (proof-simulate-send-region start end)))
  (forward-line 1))
  
(defun proof-send-region ()
  "Sends the current region to the inferior shell running proof and
  appends a terminator if neccessary."
  (interactive)
  (let (start end)
    (save-excursion
      (setq end (point))
      (exchange-point-and-mark)
      (setq start (point)))
    (proof-simulate-send-region start end t)))

(defun proof-command (command &optional silent)
  (let ((str (proof-append-terminator command)))
  (proof-simple-send str silent)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Starting, stopping, and interrupting the lego shell             ;;
;;  There maybe more functionality here one day to support multiple ;;
;;  subprocesses                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-start-shell ()
  (run-hooks 'proof-pre-shell-start-hook)
  (let ((proof-buf (and proof-shell-process-name (proof-shell-buffer))))
    (if (comint-check-proc proof-buf)
        ()
      (save-excursion
        (and proof-prog-name-ask-p
             (setq proof-shell-prog-name
                   (read-shell-command "Run process: "
                                       proof-shell-prog-name))))
      (or proof-shell-process-name
          (setq proof-shell-process-name
                (concat
                 "Inferior "
                 (substring proof-shell-prog-name
                            (string-match "[^/]*$" proof-shell-prog-name)
                            (string-match "$" proof-shell-prog-name)))))
      (message (format "Starting %s process..." proof-shell-process-name))
      
      (proof-spawn-process proof-shell-prog-name 
			 proof-shell-process-name proof-shell-buffer-name)
      (run-hooks 'proof-post-shell-start-hook)
      (pbp-goals-init)
      (message 
       (format "Starting %s process... done." proof-shell-process-name)))))
  

(defun proof-spawn-process (prog-name process-name buffer-name)
  "Start a new shell in a new buffer"

  (set-buffer
   (let ((prog-name-list (string-to-list prog-name " ")))
     (apply 'make-comint 
	    (append (list process-name 
			  (car prog-name-list) nil)
		    (cdr prog-name-list)))))

  (erase-buffer)
  (funcall proof-shell-mode-is)
  (setq comint-prompt-regexp proof-shell-prompt-pattern)
  (setq comint-input-sender 'proof-input-sender)
  (and running-emacs19 (setq comint-scroll-show-maximum-output t))
  (proof-display-buffer buffer-name)
  (set-buffer buffer-name)
  )

(defun proof-shell-exit ()
  "Exit the PROOF process

  Runs proof-shell-exit-hook if non nil"

  (interactive)
  (save-excursion
    (let ((buffer (proof-shell-buffer)))
      (and buffer
	   (progn
	     (save-excursion
	       (set-buffer buffer)
	       (comint-send-eof))
	     (kill-buffer buffer)
	     
	     (run-hooks 'proof-shell-exit-hook)

             ;;it is important that the hooks are
	     ;;run after the buffer has been killed. In the reverse
	     ;;order e.g., intall-shell-fonts causes problems and it
	     ;;is impossilbe to restart the PROOF shell

	     (message 
	      (format "%s process terminated." proof-shell-process-name)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Active terminator minor mode                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar proof-active-terminator-minor-mode nil)
(make-variable-buffer-local 'proof-active-terminator-minor-mode)
(put 'proof-active-terminator-minor-mode 'permanent-local t)

(defun proof-active-terminator-minor-mode (&optional arg)
  "Toggle PROOF's Active Terminator minor mode.
With arg, turn on the Active Terminator minor mode if and only if arg
is positive.

If Active terminator mode is enabled, a terminator will process the
current command."

 (interactive "P")
 
;; has this minor mode been registered as such?
  (or (assq 'proof-active-terminator-minor-mode minor-mode-alist)
      (setq minor-mode-alist
            (append minor-mode-alist
                    (list '(proof-active-terminator-minor-mode " ;")))))

 (setq proof-active-terminator-minor-mode
        (if (null arg) (not proof-active-terminator-minor-mode)
          (> (prefix-numeric-value arg) 0)))
   (if (fboundp 'redraw-modeline) (redraw-modeline) (force-mode-line-update)))

(defun proof-active-terminator ()
  (interactive)
  (if proof-active-terminator-minor-mode 
      (proof-process-active-terminator)
    (self-insert-command 1)))
    
(defun proof-process-active-terminator ()
  "Process an active terminator key-press"  

  (interactive)
  (let (start)
    (and (re-search-backward "[^ ]" nil t)
	 (not (char-equal (following-char) proof-terminal-char)) 
	 (forward-char))
    (save-excursion
      (setq start (proof-find-start-of-command)))
    (if (not start)
	 (self-insert-command 1)
       (if (> start (point))
	   (setq start (point)))
       (proof-simulate-send-region start (point) t)
       (if (char-equal proof-terminal-char (following-char))
	   (forward-char)
	 (self-insert-command 1)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; font lock faces: declarations, errors, tacticals                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar font-lock-declaration-name-face 
(progn 
  (cond ((x-display-color-p)
	 ;notice that device-class does not exist in Emacs 19.30

	 (copy-face 'bold 'font-lock-declaration-name-face)

	 ;; Emacs 19.28 compiles this down to
	 ;; internal-set-face-1. This is not compatible with XEmacs
	 (dont-compile
	   (set-face-foreground
	    'font-lock-declaration-name-face "chocolate")))
	(t (copy-face 'bold-italic 'font-lock-declaration-name-face)))
  (if running-emacs19
      (setq font-lock-declaration-name-face
	    (face-name 'font-lock-declaration-name-face)))))

(defvar font-lock-tacticals-name-face
(if (x-display-color-p)
    (let ((face (make-face 'font-lock-tacticals-name-face)))
      (dont-compile
	(set-face-foreground face
			     "MediumOrchid3"))
      face)
  (copy-face 'bold 'font-lock-tacticals-name-face)))

(defvar font-lock-error-face
(if (x-display-color-p)
    (let ((face (make-face 'font-lock-error-face)))
      (dont-compile
	(set-face-foreground face
			     "red"))
      face)
  (copy-face 'bold 'font-lock-error-face)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof mode configuration                                         ;;
;; Eventually there will be some more                               ;;
;; functionality here common to both coq and lego.                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-derived-mode proof-mode fundamental-mode 
  "Proof" "Proof mode - not standalone"
  ())

(define-key proof-mode-map [(control c) (control e)]
  'proof-find-end-of-command)
(define-key proof-mode-map [(control c) (control j)] 'proof-send-line)
(define-key proof-mode-map [(control c) (control r)] 'proof-send-region)
(define-key proof-mode-map [(control c) (control c)] 'proof-interrupt-subjob)

(define-derived-mode proof-shell-mode comint-mode 
  "proof-shell" "Proof shell mode - not standalone"
  ())

;; the following callback is an irritating hack - there should be some
;; elegant mechanism for computing constants after the child has
;; configured.

(defun proof-config-done () 

;; calculate some strings and regexps for searching

  (setq proof-terminal-string (char-to-string proof-terminal-char))

  (make-local-variable 'comment-start)
  (setq comment-start (concat proof-comment-start " "))
  (make-local-variable 'comment-end)
  (setq comment-end (concat " " proof-comment-end))
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip 
    (concat (regexp-quote proof-comment-start) "+\\s_?"))

  (setq proof-re-end-of-cmd (concat "\\s_*" proof-terminal-string "\\s_*\\\'"))
  (setq proof-re-term-or-comment 
	(concat proof-terminal-string "\\|" (regexp-quote proof-comment-start)
		"\\|" (regexp-quote proof-comment-end)))

  (define-key proof-mode-map
    (vconcat [(control c)] (vector proof-terminal-char))
    'proof-active-terminator-minor-mode)

  (define-key proof-mode-map proof-terminal-char 'proof-active-terminator)

  )


(provide 'proof)
