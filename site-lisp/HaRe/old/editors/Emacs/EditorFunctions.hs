module Emacs.EditorFunctions where

import GenEditorInterfacesAux
import LocalSettingsCabal

editor = Editor {
    editorName = "Emacs/XEmacs"

  , initScriptPars = \cname-> (cname,"","","",0)

  , duplicate =
      unlines
      [""
      ,"(defun haskell-refac-parseAnswers2 ()"
      ,"\"parseAnswers2\""
      ,"(interactive \"\")"
      ,"(progn"
      ,"(process-send-string \"haskell-refac-process\" (concat"
      ,"   \"parseAnswers \" (mapconcat 'identity (append"
	  ,""
      ,"    (list \"\")) \"  \")"
      ,"   \"\\n\"))"
      ,"(let ((F (read-from-minibuffer \"choice?\"))    )  "
      ,"(if (equal F  \"q\")"
      ,"   (process-send-string \"haskell-refac-process\" (concat"
      ,"    \"refacDupTrans \" (mapconcat 'identity (append"
	  ,"      (list \"\")) \" \")"
      ,"   \"\\n\"))"
      ,"   (progn"
      ,"    (process-send-string \"haskell-refac-process\" (concat"
      ,"     \"parseAnswers \" (mapconcat 'identity (append"
	  ,""
	  ,"        (list F)) \" \")"
      ,"     \"\\n\"))"
      ,"     (haskell-refac-parseAnswers2)"
      ,"     \"\\n\")))"
      ,   ")"
      ,")"  ]

  , scriptFun = \(cname,es,ep,ei,n) (Comment comment) ->
      unlines
      [""
      ,"(defun haskell-refac-"++cname++" ("++ep++")"
      ,"  \""++cname++"\""
      ,"  (interactive \""++ei++"\")"
      ,"  (let (modified)"
      ,"     (dolist (b (buffer-list) modified)"
      ,"       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))"
      ,"        (if (and (not (or (string= \" \" n1) (string= \"*\" n1))) (buffer-modified-p b))"
      ,"          (setq modified (cons (buffer-name b) modified)))))"
      ,"     (if modified (message-box (format \"there are modified buffers: %s\" modified))"
      ,"       (process-send-string \"haskell-refac-process\" "
      ,"         (concat"
      ,"         "++(unwords $ map show refactor_args)
      ,"         \""++cname++" \" (mapconcat 'identity (append "++es++") \" \")"
      ,"         \"\\n\"))"
      ,"     )"
      ,"  ) )"
      ]

  , optionParFun = \(cname,es,ep,ei,n) (OptionPar isList option ps) ->
      let optionString False prefix = "(list "++prefix++option++")"
          optionString True  prefix = prefix++option
      in (cname
         ,es++"\n\t\t"++optionString isList "haskell-refac-"
         ,ep
         ,ei
         ,n+1)

  , nameParFun = \(cname,es,ep,ei,n) (NamePar prompt ps) ->
      let name = "name"++show n
      in (cname
         ,es++"\n\t\t(list "++name++")"
         ,ep++" "++name
         ,ei++"s"++prompt++"\\n"
         ,n+1)

  , pathParFun = \(cname,es,ep,ei,n) (PathPar prompt def ps) ->
      let name = "pathname"++show n
      in (cname
         ,es++"\n\t\t"++"(if (eq (length "++name++") 0)"
            ++"\n\t\t\t(list "++show def++")"
            ++"\n\t\t\t(list "++name++"))"
         ,ep++" "++name
         ,ei++"s"++prompt++"["++(showNoQuotes def)++"]"++"\\n"
         ,n+1)

  , fileNameParFun = \(cname,es,ep,ei,n) (FileNamePar keepExt ps) ->
      let modifier = if keepExt then "" else "Base"
          filename = "file"++modifier++"Name"++show n
      in if keepExt
         then (cname
              ,es++"\n\t\t(list (if (buffer-file-name) (buffer-file-name) \"<missing filename>\"))"
              ,ep
              ,ei
              ,n+1)
         else (cname
              ,es++"\n\t\t(list (file-name-sans-extension (if (buffer-file-name) (buffer-file-name) \"<missing filename>\")))"
              ,ep
              ,ei
              ,n+1)

  , positionParFun = \(cname,es,ep,ei,n) (PositionPar ps) ->
      let line = "line"++show n
          col  = "column"++show n
      in (cname
         ,es++"\n\t\t(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))"
         ,ep
         ,ei
         ,n+1)

  , regionParFun = \(cname,es,ep,ei,n) (RegionPar ps) ->
      let start = "start"++show n
          end   = "end"++show n
      in (cname
         ,es++"\n\t\t(list (number-to-string (line-no-pos "++start++"))"
            ++"\n\t\t(number-to-string (+ 1 (current-column-pos "++start++")))"
            ++"\n\t\t(number-to-string (line-no-pos "++end++"))"
            ++"\n\t\t(number-to-string (+ 1 (current-column-pos "++end++"))))"
         ,ep++" "++start++" "++end
         ,ei++"r"
         ,n+1)

  , gen_interface = \cmds -> do
      let
        lineEnv = [("@@FUNCTIONS@@",map gen_function cmds)
                  ,("@@MENU_ENTRIES@@",map gen_menu_entry cmds)
                  ]
        gen_menu_entry (Menu name es)       = unlines
                          ["(\""++name++"\""
                          ,unlines (map gen_menu_entry es) ++ ")"
                          ]
        gen_menu_entry (Entry entry name c) =
                          "   [\""++entry++"\" haskell-refac-"++name++"  :active t]"
        gen_function (Entry _ _ c) = script c
        gen_function (Menu _ es)   = unlines $ map gen_function es

      template <- lines `fmap` readFile "haskell-refac.el.in"
      let file = concatMap (processLine wordEnv lineEnv) template
      writeFile "haskell-refac.el" $ unlines file

    -- we'd like menu tooptips as well, but ..
    -- Xemacs easy menu doesn't support menu tooltips
    -- "   [\""++entry++"\" haskell-refac-"++name++" :help \""++description c++"\"  :active t]"

  }
