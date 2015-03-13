module Vim.EditorFunctions where

import Data.Char(toUpper)
import GenEditorInterfacesAux

editor = Editor {
    editorName = "Vim"

  , initScriptPars = \cname-> (cname,"","","",0)
  , duplicate = ""
  , scriptFun = \(cname,vs,vl,aux,n) (Comment comment) ->
      unlines
      [""
      ,"function! Haskell_refac_"++cname++"()"
      ,vl
      ,"call Haskell_refac_client_cmd(\" "++cname++"\""++vs++")"
      ,"endfunction"
      ]

  , optionParFun = \(cname,vs,vl,aux,n) (OptionPar isList option ps) ->
      (cname
      ,vs++".\" \". g:haskell_refac_"++option
      ,vl
      ,aux
      ,n+1)

  , nameParFun = \(cname,vs,vl,aux,n) (NamePar prompt ps) ->
      let name = "name"++show n
      in (cname
         ,vs++".\" \"."++name
         ,vl++"\tlet "++name++" = Myinput("++show prompt++")\n"
         ,aux
         ,n+1)

  , pathParFun = \(cname,vs,vl,aux,n) (PathPar prompt def ps) ->
      let name = "pathname"++show n
      in (cname
         ,vs++".\" \"."++name
         ,vl++"\tlet "++name++" = Myinput("++show prompt++","++show def++")\n"
         ,aux
         ,n+1)

  , fileNameParFun = \(cname,vs,vl,aux,n) (FileNamePar keepExt ps) ->
      let modifier = if keepExt then "" else "Base"
          filename = "file"++modifier++"Name"++show n
      in if keepExt
         then (cname
              ,vs++".\" \"."++filename
              ,vl++"\tlet "++filename++" = expand(\"%:p\")\n"
              ,aux
              ,n+1)
         else (cname
              ,vs++".\" \"."++filename
              ,vl++"\tlet "++filename++" = expand(\"%:p:r\")\n"
              ,aux
              ,n+1)

  , positionParFun = \(cname,vs,vl,aux,n) (PositionPar ps) ->
      let line = "line"++show n
          col  = "column"++show n
      in (cname
         ,vs++".\" \"."++line++".\" \"."++col
         ,vl++"\tlet "++line++" = line(\".\")\n"++"\tlet "++col++" = col(\".\")\n"
         ,aux
         ,n+1)

  , regionParFun = \(cname,vs,vl,aux,n) (RegionPar ps) ->
      let start = "start"++show n
          end   = "end"++show n
      in (cname
         ,vs++".\" \"."++start++".\" \"."++end
         ,vl++"\tlet "++start++" = line(\"'<\").\" \".col(\"'<\")"
            ++"\n\tlet "++end++" = line(\"'>\").\" \".col(\"'>\")"
         ,aux
         ,n+1)

  , gen_interface = \cmds -> do
      let
        lineEnv = [("@@FUNCTIONS@@",map gen_function cmds)
                  ,("@@COMMANDS@@",map gen_command cmds)
                  ,("@@MENU_ENTRIES@@",map (gen_menu_entry "") cmds)
                  ]
        gen_function (Entry _ _ c) = script c
        gen_function (Menu _ es)   = unlines $ map gen_function es
        gen_command (Entry _ name c) = "command! "++capitalise name++" :echo Haskell_refac_"++name++"()"
        gen_command (Menu _ es)      = unlines $ map gen_command es
        gen_menu_entry prefix (Menu name es)       =
            unlines $ map (gen_menu_entry $ prefix++concatMap escape (capitalise name)++".") es
        gen_menu_entry prefix (Entry entry name c) =
            "\tamenu Haskell(Refac)."
          ++prefix
          ++concatMap escape (capitalise entry)++" :"++capitalise name++"<cr>"
          ++"\n\ttmenu Haskell(Refac)."
          ++prefix
          ++concatMap escape (capitalise entry)++description c
        capitalise (h:t) = (toUpper h):t
        escape ' ' = "\\ "
        escape  c  = [c]

      template <- lines `fmap` readFile "refactor.vim.in"
      let file = concatMap (processLine wordEnv lineEnv) template
      writeFile "refactor.vim" $ unlines file

  }
