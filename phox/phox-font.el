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
       "Data\\|"
       "I\\(mport\\|nductive\\)\\|"
       "Use\\|"
       "Sort\\|"
       "new_\\(intro\\|e\\(lim\\|quation\\)\\|rewrite\\)\\|"
       "a\\(dd_path\\|uthor\\)\\|"
       "c\\(l\\(aim\\|ose_def\\)\\|or\\(ollary\\)?\\)\\|"
       "d\\(e\\(f\\(\\(_thlist\\|rec\\)\\)?\\|l\\(_proof\\)\\)\\|ocuments\\|epend\\)\\|"
       "e\\(lim_after_intro\\|xport\\|del\\|show\\)\\|"
       "f\\(act\\|lag\\)\\|"
       "goal\\|"
       "in\\(clude\\|stitute\\)\\|"
       "lem\\(ma\\)?\\|"
       "p\\(ath\\|r\\(int\\(_sort\\)?\\|iority\\|op\\(osition\\)?\\|ove_claim\\)\\)\\|"
       "quit\\|"
       "s\\(ave\\|earch\\)\\|"
       "t\\(ex\\(_syntax\\)?\\|heo\\(rem\\)?\\|itle\\|ype\\)"
       "\\)[ \t\n\r.]")
      '(0 'font-lock-keyword-face t))
;proof command
    (cons (concat "\\([ \t]\\|^\\)\\("
       "a\\(bort\\|fter\\|nd\\|pply\\|ssume\\|xiom\\)\\|"
       "by\\(_absurd\\)?\\|"
       "constraints\\|"
       "elim\\|"
       "deduce\\|"
       "evaluate\\(_hyp\\)?\\|"
       "from\\|"
       "goals\\|"
       "in\\(tros?\\|stance\\)\\|"
       "l\\(oc\\(al\\|k\\)\\|e\\(t\\|fts?\\)\\)\\|"
       "next\\|"
       "of\\|"
       "prove\\|"
       "r\\(e\\(write\\(_hyp\\)?\\|name\\)\\|mh\\)\\|"
       "s\\(elect\\|how\\|lh\\)\\|"
       "t\\(hen\\|rivial\\)\\|" 
       "u\\(se\\|n\\(do\\|fold\\(_hyp\\)?\\|lock\\)\\)\\|" 
       "with"
       "\\)[ \t.]")
      '(0 'font-lock-type-face t))))

(provide 'phox-font)
