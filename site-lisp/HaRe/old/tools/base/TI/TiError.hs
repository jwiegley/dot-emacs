module TiError where
import PrettyPrint(Doc,Printable(..),($$),(<>),(<+>),ppiFSeq,vcat,nest,sep,modn)
import SrcLoc1
import SrcLocPretty
import HsName(ModuleName)

data Error i
  = InContext (ErrorContext i) (Error i)
  | Other Doc
  deriving Show

data ErrorContext i
  = AtPos SrcLoc (Maybe Doc)
  | DeclCtx [i]
  | ModuleCtx [ModuleName]
  | OtherCtx Doc [(Doc,SrcLoc)]
  deriving Show

instance Printable i => Printable (Error i) where
  ppi (InContext ctx e) = ctx<>":" $$ nest 2 e
  ppi (Other msg) = msg

instance Printable i => Printable (ErrorContext i) where
  ppi (AtPos loc Nothing) = ppi loc
  ppi (AtPos loc (Just msg)) = ppi loc<>":"<+>msg
  ppi (DeclCtx is) = "In the declaration of"<+>ppiFSeq is
  ppi (ModuleCtx [m]) = "In module"<+>modn m
  ppi (ModuleCtx ms) = "In modules"<+>ppiFSeq (map modn ms)
  ppi (OtherCtx msg locs) = sep [ppi msg,nest 4 (vcat (map ploc locs))]
    where ploc (d,loc) = sep [ppi d,nest 2 ("from"<+>loc)]
