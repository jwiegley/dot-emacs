;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;;                       Font lock keywords
;;--------------------------------------------------------------------------;;

(defconst phox-font-lock-keywords
  (list
;commands
   '("(\\*\\([^*]\\|\\*+[^*)]\\)*\\(\\*+)\\|\\**$\\)"
    0 'font-lock-comment-face t)
   '("\"\\([^\\\"]\\|\\\\.\\)*\""
    0 'font-lock-string-face t)
    (cons (concat "\\([ \t]\\|^\\)\\("
       "Cst\\|"
       "Import\\|"
       "Use\\|"
       "Sort\\|"
       "new_\\(intro\\|elim\\|rewrite\\)\\|"
       "a\\(dd_path\\|uthor\\)\\|"
       "c\\(laim\\|ose_def\\|or\\(ollary\\)?\\)\\|"
       "d\\(e\\(f\\(_thlist\\)?\\|l\\)\\|ocuments\\|epend\\)\\|"
       "e\\(lim_after_intro\\|xport\\|del\\|show\\)\\|"
       "f\\(act\\|lag\\)\\|"
       "goal\\|"
       "in\\(clude\\|stitute\\)\\|"
       "lem\\(ma\\)?\\|"
       "p\\(ath\\|r\\(int\\(_sort\\)?\\|iority\\|op\\(osition\\)?\\)\\)\\|"
       "quit\\|"
       "s\\(ave\\|earch\\)\\|"
       "t\\(ex\\(_syntax\\)?\\|eheo\\(rem\\)?\\|itle\\)"
       "\\)[ \t\n\r.]")
      '(0 'font-lock-keyword-face t))
;proof command
    (cons (concat "\\([ \t]\\|^\\)\\("
       "a\\(b\\(bort\\|surd\\)\\|pply\\|xiom\\)\\|"
       "constraints\\|"
       "elim\\|"
       "from\\|"
       "goals\\|"
       "in\\(tros?\\|stance\\)\\|"
       "l\\(ocal\\|efts?\\)\\|"
       "next\\|"
       "r\\(e\\(write\\(_hyp\\)?\\|name\\)\\|mh\\)\\|"
       "slh\\|"
       "trivial\\|" 
       "u\\(se\\|n\\(do\\|fold\\(_hyp\\)?\\)\\)" 
       "\\)[ \t.]")
      '(0 'font-lock-type-face t))))

;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;;                       Sym-lock tables
;;--------------------------------------------------------------------------;;

(if proof-running-on-XEmacs (require 'phox-sym-lock))

;; to change this table, xfd -fn '-adobe-symbol-*--12-*' may be
;; used to determine the symbol character codes.
(defvar phox-sym-lock-keywords
  '((">=" 0 1 179)
    ("<=" 0 1 163)
    ("!=" 0 1 185)
    (":<" 0 1 206)
    ("[^:]\\(:\\)[^:= \n\t\r]" 1 7 206)
    ("\\\\/" 0 1 36)
    ("/\\\\" 0 1 34)
    ("\\<or\\>" 0 3 218) 
    ("&" 0 1 217) 
    ("<->" 0 1 171)
    ("-->" 0 1 222)
    ("->" 0 1 174)
    ("~" 0 1 216)
    ("\\\\" 0 1 108))
  "If non nil: Overrides default Sym-Lock patterns for PhoX.")

(defun phox-sym-lock-start ()
	(if (and (featurep 'sym-lock) phox-sym-lock)
	    (progn
	      (setq sym-lock-color
		    (face-foreground 'font-lock-function-name-face))
	      (if (not sym-lock-keywords)
		  (sym-lock phox-sym-lock-keywords)))))

(provide 'phox-font)
