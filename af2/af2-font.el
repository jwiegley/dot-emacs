;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;;                       Font lock keywords
;;--------------------------------------------------------------------------;;

(defconst af2-font-lock-keywords
  (list
;commands
   '("(\\*\\([^*]\\|\\*+[^*)]\\)*\\(\\*+)\\|\\**$\\)"
    0 'font-lock-comment-face t)
   '("\"\\([^\\\"]\\|\\\\.\\)*\""
    0 'font-lock-string-face t)
    (cons (concat "\\([ \t]\\|^\\)\\("
       "\\(Cst\\)\\|"
       "\\(Import\\)\\|"
       "\\(Use\\)\\|"
       "\\(Sort\\)\\|"
       "\\(new_\\(\\(intro\\)\\|\\(elim\\)\\|\\(rewrite\\)\\)\\)\\|"
       "\\(a\\("
       (concat
	"\\(dd_path\\)\\|"
	"\\(uthor\\)"
	"\\)\\)\\|")
       "\\(c\\("
       (concat
	"\\(laim\\)\\|"
	"\\(ose_def\\)\\|"
	"\\(or\\(ollary\\)?\\)"
	"\\)\\)\\|")
       "\\(d\\(\\(e\\(f\\|l\\)\\)\\|\\(ocuments\\)\\|\\(epend\\)\\)\\)\\|"
       "\\(e\\("
       (concat 
	"\\(lim_after_intro\\)\\|"
	"\\(xport\\)\\|"
	"\\(del\\)\\|"
	"\\(show\\)"
	"\\)\\)\\|")
       "\\(f\\("
       (concat
	"\\(act\\)\\|"
	"\\(lag\\)\\|"
	"\\)\\)\\|")
       "\\(goal\\)\\|"
       "\\(in\\("
       (concat
	"\\(clude\\)\\|"
	"\\(stitute\\)"
	"\\)\\)\\|")
       "\\(lem\\(ma\\)?\\)\\|"
       "\\(p\\("
       (concat
	"\\(ath\\)\\|"
	"\\(r\\("
	(concat
	 "\\(int_sort\\)\\|"
	 "\\(iority\\)\\|"
	 "\\(op\\(osition\\)?\\)"
	 "\\)\\)")
	"\\)\\)\\|")
       "\\(quit\\)\\|"
       "\\(s\\(\\(ave\\)\\|\\(earch\\)\\)\\)\\|"
       "\\(t\\(" 
       (concat
	"\\(ex\\(_syntax\\)?\\)\\|"
	"\\(eheo\\(rem\\)?\\)\\|"
	"\\(itle\\)"
	"\\)\\)")
       "\\)[ \t.]")
      '(0 'font-lock-keyword-face t))
;proof command
    (cons (concat "\\([ \t]\\|^\\)\\("
       "\\(a\\("
       (concat
	"\\(bort\\)\\|"
	"\\(bsurd\\)\\|"
	"\\(pply\\)\\|"
	"\\(xiom\\)"
	"\\)\\)\\|")
       "\\(constraints\\)\\|"
       "\\(elim\\)\\|"
       "\\(from\\)\\|"
       "\\(goals\\)\\|"
       "\\(in\\("
       (concat
	"\\(tros?\\)\\|"
	"\\(stance\\)"
	"\\)\\)\\|")
       "\\(l\\("
       (concat
	"\\(ocal\\)\\|"
	"\\(efts?\\)"
	"\\)\\)\\|")
       "\\(next\\)\\|"
       "\\(r\\(\\(ewrite\\(_hyp\\)?\\)\\|\\(ename\\)\\|\\(mh\\)\\)\\)\\|"
       "\\(slh\\)\\|"
       "\\(trivial\\)\\|" 
       "\\(u\\("       
       (concat
	"\\(se\\)\\|"
	"\\(ndo\\)\\|"
	"\\(nfold\\(_hyp\\)?\\)\\)\\)") 
       "\\)[ \t.]")
      '(0 'font-lock-type-face t))))

;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;;                       Sym-lock tables
;;--------------------------------------------------------------------------;;

(if proof-running-on-XEmacs (require 'sym-lock))

;; to change this table, xfd -fn '-adobe-symbol-*--12-*' may be
;; used to determine the symbol character codes.
(defvar af2-sym-lock-keywords
  '((">=" 0 1 179)
    ("<=" 0 1 163)
    ("!=" 0 1 185)
    (":<" 0 1 206)
    ("[^:]\\(:\\)[^:=]" 1 7 206)
    ("\\\\/" 0 1 36)
    ("/\\\\" 0 1 34)
    ("\\<or\\>" 0 3 218) 
    ("&" 0 1 217) 
    ("<->" 0 1 171)
    ("-->" 0 1 222)
    ("->" 0 1 174)
    ("~" 0 1 216))
  "If non nil: Overrides default Sym-Lock patterns for Af2.")

(defun af2-sym-lock-start ()
	(if (and (featurep 'sym-lock) af2-sym-lock)
	    (progn
	      (setq sym-lock-color
		    (face-foreground 'font-lock-function-name-face))
	      (if (not sym-lock-keywords)
		  (sym-lock af2-sym-lock-keywords)))))

(provide 'af2-font)
