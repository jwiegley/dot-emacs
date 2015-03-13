-- Pretty printing with Unicode (and other) options...

module PPU(module PPU,module PrettyPrint) where
import Prelude hiding (catch)
import PrettyPrint
import PrettyEnv
import UTF8Util
import MUtils(( # ))
import Data.List(isSuffixOf)
import AbstractIO

type PPOpts = (Bool,PPHsMode)
ppOpts0 = (False,defaultMode)

ppu :: Printable a => (Bool, PPHsMode) -> a -> String
ppu (u,opts) = (if u then utf8 else id) . pp . withPPEnv opts . ppi

ucatch u io = if u then io `catch` utf8err else io

getPPopts =
    do --u <- utf8env
       let u=False
       name <- getProgName
       (ppOpts,args) <- opts defaultMode{useUnicode=u} # getArgs
       return ((useUnicode ppOpts,ppOpts),name,args)
  where
    opts o ("+debug":args) = opts o{debugInfo =True } args
    opts o ("-debug":args) = opts o{debugInfo =False} args
    opts o ("+tinfo":args) = opts o{typeInfo  =True } args
    opts o ("-tinfo":args) = opts o{typeInfo  =False} args
    opts o ("+utf8" :args) = opts o{useUnicode=True } args
    opts o ("-utf8" :args) = opts o{useUnicode=False} args
    opts o args@(('l':'a':'y':'o':'u':'t':'=':lts):args1) =
      case reads lts of
	(lt,_):_ ->          opts o{layoutType=lt   } args1
	_        -> (o,args)
    opts o args   = (o,args)

{-	 
-- A quick hack. Find a better way to test if UTF-8 output is appropriate!
utf8env =
   do lang <- getEnv "LANG" `catch` const (return "")
      return (any (`isSuffixOf` lang) ["utf8","UTF-8"])
-}
