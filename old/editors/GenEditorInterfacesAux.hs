module GenEditorInterfacesAux where

import Data.List
import System.IO(hPutStrLn,stderr)
import System.Exit(exitFailure)

import LocalSettings

data    Comment       = Comment String
data    FileNamePar f = FileNamePar Bool f
data    PathPar f     = PathPar String String f
newtype PositionPar f = PositionPar f
newtype RegionPar f   = RegionPar f
data    NamePar f     = NamePar String f
data    OptionPar f   = OptionPar Bool String f

comment c       = Comment c
fileNamePar     = FileNamePar True
fileNameBasePar = FileNamePar False
pathPar prompt  = PathPar prompt ""
pathDefaultPar  = PathPar
positionPar     = PositionPar
regionPar       = RegionPar
namePar         = NamePar
optionPar       = OptionPar

data Editor = Editor{
    editorName     :: String
  , initScriptPars :: String -> ScriptPars
  , duplicate      :: String
  , scriptFun      :: ScriptPars -> Comment -> String
  , fileNameParFun :: forall f . ScriptPars -> FileNamePar f -> ScriptPars
  , pathParFun     :: forall f . ScriptPars -> PathPar f -> ScriptPars
  , positionParFun :: forall f . ScriptPars -> PositionPar f -> ScriptPars
  , regionParFun   :: forall f . ScriptPars -> RegionPar f -> ScriptPars
  , nameParFun     :: forall f . ScriptPars -> NamePar f -> ScriptPars
  , optionParFun   :: forall f . ScriptPars -> OptionPar f -> ScriptPars
  , gen_interface  :: forall f . [Entry f] -> IO ()
  }

defaultEditor = Editor {
    editorName     = "none"
  , initScriptPars = undefined
  , duplicate      = "none"
  , scriptFun      = undefined
  , fileNameParFun = undefined
  , pathParFun     = undefined
  , positionParFun = undefined
  , regionParFun   = undefined
  , nameParFun     = undefined
  , optionParFun   = undefined
  , gen_interface  = undefined
  }

data Cmd f = Cmd{ cmd         :: f -> [String] -> IO ()
                , description :: String
                , script      :: String
                }

data Entry f = Entry String String (Cmd f)
             | Menu String [Entry f]

editParameters editFuns entry cname c ps = Entry entry cname
                                            Cmd{cmd=const $ cmd x c
                                               ,description=description x
                                               ,script=script x
                                               }
  where
    x = editPars editFuns (initScriptPars editFuns cname) ps

errorExit msg = hPutStrLn stderr msg >> exitFailure

type FunName  = String
type Bindings = String
type Aux      = String
type Params   = String

type ScriptPars = (FunName,Bindings,Params,Aux,Int)

class EditPars p f where
  editPars :: Editor -> ScriptPars -> p -> Cmd f

-- replace first occurrence of word (@@name@@) in line by value
substituteWord []   (word,value) = []
substituteWord line (word,value) =
  case span (/='@') line of
    (prefix,rest@('@':'@':line'))
      | word `isPrefixOf` rest -> prefix ++ value ++ (rest \\ word)
    (prefix,rest@('@':line'))
      -> prefix++"@"++substituteWord line' (word,value)
    (prefix,rest)
      -> prefix++rest

-- replace words (wordEnv) and lines (lineEnv) in line
processLine wordEnv lineEnv line | not $ '@' `elem` line = [line]
processLine wordEnv lineEnv line | '@' /= head line      = [foldl substituteWord line wordEnv]
processLine wordEnv lineEnv line | otherwise             = maybe [line] id $ lookup line lineEnv

-- words to be replaced by words in template file
-- taken from generated module LocalSettings.hs
wordEnv = [("@@HARE_VERSION@@",hare_version)
      ,("@@REFACTORER@@",refactorer)
      ,("@@REFACTORER_CLIENT@@",refactorer_client)
      ,("@@LIBRARIES_NOQ@@",showNoQuotes preludePath)
      ,("@@LIBRARIES@@",show preludePath)
      ,("@@REFACTOR_PRG@@",refactor_prg)
      ,("@@REFACTOR_ARGS@@",unwords refactor_args)
      ]
