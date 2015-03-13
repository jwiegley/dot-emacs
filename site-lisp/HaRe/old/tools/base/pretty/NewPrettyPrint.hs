-- Glue to the usual Huges/SimonPJ pretty printer
module NewPrettyPrint(pp,render,quickrender,module PrettyPrint2,module PrettyEnv) where
import PrettyPrint2
import PrettyDoc
import PrettyEnv
import PrettyStd
import qualified Text.PrettyPrint as P

pp x = render (ppi x)

render = P.renderStyle normalstyle . toPretty . runEnv defaultMode

quickrender = P.renderStyle qstyle . toPretty .
              runEnv defaultMode{layoutType=PPNoLayout}

qstyle      = normalstyle{P.mode=P.OneLineMode}
normalstyle = P.style{P.lineLength=80}

toPretty d =
  case d of
    Empty -> P.empty
    Char c -> P.char c
    Text s -> P.text s
    Attr _ d -> toPretty d
    Nest n d -> P.nest n (toPretty d)
    Group l ds -> group l (map toPretty ds)
      where
	group l =
	  case l of
	    Horiz Cat -> P.hcat
	    Horiz Sep -> P.hsep
	    Vert -> P.vcat
	    HorizOrVert Cat -> P.cat
	    HorizOrVert Sep -> P.sep
	    Fill Cat -> P.fcat
	    Fill Sep -> P.fsep

