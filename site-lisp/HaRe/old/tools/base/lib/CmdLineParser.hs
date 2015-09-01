module CmdLineParser where

data Cmd cmd = Null cmd
             | Args String ([String] -> cmd)

fileArgs = Args "<files>"
fileArg f = fileArgs (mapM_ f)

kwOption kw cmd =
  case cmd of
    Null f -> addKwArg id (null2args f)
    Args args f -> addKwArg (++' ':args) f
  where
    addKwArg rest f = Args (rest ("["++kw++"]")) f'
      where
        f' (a:as) | a==kw = f as True
	f' as             = f as False

    null2args f [] o = f o
    null2args f _  o = fail "superflous arguments"

doCmd (cmds,default_cmd) prg args =
  case args of
    [] -> default_cmd
    cmd:args ->
      case lookup cmd cmds of
	Nothing -> fail $ "Unknown command: "++cmd
	Just (cmd,_) ->
	  case (cmd,args) of
	    (Null   cmd,[]) -> cmd
	    (Args _ cmd,_ ) -> cmd args
	    _ -> fail "Malformed command"

usage prg cmds =
       unlines $
         ["Usage: "++prg++ " <command>",
          "  where <command> is one of:"]++
         map (("    "++).cmdusage) cmds
  where
    cmdusage (name,(cmd,res)) =
      case cmd of
        Null _      -> unwords [name,"--",res]
	Args args _ -> unwords [name,args,"--",res]
