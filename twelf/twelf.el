;; twelf.el  Proof General instance for Twelf
;;
;; Copyright (C) 2000 LFCS Edinburgh. 
;;
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;;

;; FIXME: PG needs a bit of tuning to get this to work 
;; properly, because of mixed syntax for comments.

;; We should introduce a proof-parse-to-next-command 
;; configurable setting, perhaps, which should skip
;; comments automatically.  

(require 'proof-easy-config)            ; easy configure mechanism

(require 'twelf-font)			; font lock configuration
;; (require 'twelf-old)			; port of parts of old code
;; FIXME: put parts of old code into twelf-syntax or similar

(proof-easy-config 
 'twelf "Twelf" 
 proof-prog-name		 "twelf-server"
 proof-assistant-home-page       "http://www.cs.cmu.edu/~twelf/"
 proof-terminal-char             ?\.
 proof-shell-auto-terminate-commands nil ; server commands don't end with .

 ;; FIXME: must also cope with single line comments beginning with %
 proof-comment-start             "%{\\|^%"
 proof-comment-end               "}%\\|^%.*\n"
 proof-comment-start-regexp	 "%[%{\t\n\f]"
 proof-comment-end		 ""

 ;; FIXME: these don't apply?
 proof-goal-command-regexp       "^%theorem"
 proof-save-command-regexp       "" ;; FIXME: empty?
 proof-goal-with-hole-regexp     "^%theorem\w-+\\(.*\\)\w-+:"
 proof-save-with-hole-regexp     "" ;; FIXME
 ;; proof-non-undoables-regexp      "undo\\|back"
 proof-goal-command              "%theorem %s."
 proof-save-command              "%prove "
 ;; proof-kill-goal-command         "Goal \"PROP no_goal_set\";"

;; proof-showproof-command         "pr()"
;; proof-undo-n-times-cmd          "pg_repeat undo %s;"

 proof-auto-multiple-files       t
 proof-shell-cd-cmd              "OS.chDir %s"
 proof-shell-prompt-pattern      "%% OK %%\n"
 proof-shell-interrupt-regexp    "interrupt"
;; proof-shell-start-goals-regexp  "Level [0-9]"
;; proof-shell-end-goals-regexp    "val it"

 proof-shell-annotated-prompt-regexp "%% [OA][KB]O?R?T? %%\n"
 proof-shell-error-regexp        "Server error:"
 proof-shell-quit-cmd            "quit"
 proof-shell-restart-cmd	 "reset"

 ;; unset
 ;; proof-shell-init-cmd  
 ;; "fun pg_repeat f 0 = () | pg_repeat f n = (f(); pg_repeat f (n-1));"
 ;; proof-shell-proof-completed-regexp "^No subgoals!"
 ;; proof-shell-eager-annotation-start   
 ;;"^\\[opening \\|^###\\|^Reading")
 )


;;
;; Syntax table
;;

;; Taken from old Emacs mode, renamed fns to be convention compliant
(defun twelf-set-syntax (char entry)
  (modify-syntax-entry char entry twelf-mode-syntax-table))
(defun twelf-set-word  (char) (twelf-set-syntax char "w   "))
(defun twelf-set-symbol (char) (twelf-set-syntax char "_   "))

(defun twelf-map-string (func string)
  (if (string= "" string)
      ()
    (funcall func (string-to-char string))
    (twelf-map-string func (substring string 1))))

;; A-Z and a-z are already word constituents
;; For fontification, it would be better if _ and ' were word constituents
(twelf-map-string 
 'twelf-set-word "!&$^+/<=>?@~|#*`;,-0123456789\\") ; word constituents
(twelf-map-string 'twelf-set-symbol "_'")         ; symbol constituents
;; Delimited comments are %{ }%, see 1234 below.
(twelf-set-syntax ?\ "    ")            ; whitespace
(twelf-set-syntax ?\t "    ")           ; whitespace
(twelf-set-syntax ?% "< 14")            ; comment begin
(twelf-set-syntax ?\n ">   ")           ; comment end
(twelf-set-syntax ?: ".   ")            ; punctuation
(twelf-set-syntax ?. ".   ")            ; punctuation
(twelf-set-syntax ?\( "()  ")           ; open delimiter
(twelf-set-syntax ?\) ")(  ")           ; close delimiter
(twelf-set-syntax ?\[ "(]  ")           ; open delimiter
(twelf-set-syntax ?\] ")[  ")           ; close delimiter
(twelf-set-syntax ?\{ "(}2 ")           ; open delimiter
(twelf-set-syntax ?\} "){ 3")           ; close delimiter
;; Actually, strings are illegal but we include:
(twelf-set-syntax ?\" "\"   ")          ; string quote
;; \ is not an escape, but a word constituent (see above)
;;(twelf-set-syntax ?\\ "/   ")         ; escape



;;
;; Syntax highlighting (from twelf-old.el, needs work)
;;

;; Automatically highlight Twelf sources using font-lock
;; (FIXME: this is not so good, should work with font-lock properly!)
(require 'twelf-font)
(add-hook 'twelf-mode-hook 'twelf-font-fontify-buffer)

(defun twelf-current-decl ()
  "Returns list (START END COMPLETE) for current Twelf declaration.
This should be the declaration or query under or just before
point within the nearest enclosing blank lines.
If declaration ends in `.' then COMPLETE is t, otherwise nil."
  (let (par-start par-end complete)
    (save-excursion
      ;; Skip backwards if between declarations
      (if (or (eobp) (looking-at (concat "[" *whitespace* "]")))
          (skip-chars-backward (concat *whitespace* ".")))
      (setq par-end (point))
      ;; Move forward from beginning of decl until last
      ;; declaration before par-end is found.
      (if (not (bobp)) (backward-paragraph 1))
      (setq par-start (point))
      (while (and (twelf-end-of-par par-end)
                  (< (point) par-end))
        (setq par-start (point)))
      ;; Now par-start is at end of preceding declaration or query.
      (goto-char par-start)
      (skip-twelf-comments-and-whitespace)
      (setq par-start (point))
      ;; Skip to period or consective blank lines
      (setq complete (twelf-end-of-par))
      (setq par-end (point)))
    (list par-start par-end complete)))

(defun twelf-next-decl (filename error-buffer)
  "Set point after the identifier of the next declaration.
Return the declared identifier or `nil' if none was found.
FILENAME and ERROR-BUFFER are used if something appears wrong."
  (let ((id nil)
        end-of-id
	beg-of-id)
    (skip-twelf-comments-and-whitespace)
    (while (and (not id) (not (eobp)))
      (setq beg-of-id (point))
      (if (zerop (skip-chars-forward *twelf-id-chars*))
          ;; Not looking at id: skip ahead
          (skip-ahead filename (current-line-absolute) "No identifier"
                      error-buffer)
        (setq end-of-id (point))
        (skip-twelf-comments-and-whitespace)
        (if (not (looking-at ":"))
            ;; Not looking at valid decl: skip ahead
            (skip-ahead filename (current-line-absolute end-of-id) "No colon"
                        error-buffer)
          (goto-char end-of-id)
          (setq id (buffer-substring beg-of-id end-of-id))))
      (skip-twelf-comments-and-whitespace))
    id))

(defconst twelf-syntax-menu
  '("Syntax Highlighting"
    ["Highlight Declaration" twelf-font-fontify-decl t]
    ["Highlight Buffer" twelf-font-fontify-buffer t]
    ;;(, (toggle "Immediate Highlighting" 'toggle-twelf-font-immediate
    ;;'font-lock-mode))
      )
  "Menu for syntax highlighting in Twelf mode.")

(defpgdefault menu-entries
  (cdr twelf-syntax-menu))

  

(provide 'twelf)