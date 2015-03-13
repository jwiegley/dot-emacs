module TiPretty where
import TiTypes hiding (forall')
import TiNames
import TiKinds
import PrettyPrint
import SpecialNames
import PrettySymbols(forall',imp,el)
import Syntax(hsTyVar)
import HsDeclPretty(ppFunDeps,ppContext)
import MUtils(( # ),ifM)

instance (TypeId i,ValueId i)
      => Printable (Scheme i) where
  ppi (Forall [] [] qt) = ppi qt
  ppi (Forall aks vks qt@(_:=>t)) =
      ppIfUnicode (ppForall varnames) (ppForall asciinames)
    where
      ppForall names = sep [forall' <+> vs'' <+> ".",letNest qt'']
        where
          qt'' = ifM (debugInfo # getPPEnv) (ppi qt) (ppi qt')

          vs'' = ifM (debugInfo # getPPEnv) (asep (k vs)) (asep (k vs'))
	    where k vs = map ppKinded (zipTyped (vs:>:ks))
          vs' = map snd s
	  qt' = apply (S s) qt
	  s = [(v,hsTyVar (ltvar name) `asTypeOf` t) | (v,name) <- zip vs names]
	  vs:>:ks = unzipTyped (aks++vks) -- hmm
	  n = length aks
	  asep avs =
              if null as
	      then fsep vs
	      else braces (fsep as)<+>fsep vs
           where (as,vs) = splitAt n avs
      -- Infinite supplies of variables names:
      varnames = map single [alpha..omega]++asciinames
        where alpha='\x03b1'; omega='\x03c9'
      asciinames = map single letters++[a:show n|n<-[1..],a<-letters]
      single x = [x]
      letters = ['a'..'z']

ppKinded (x:>:k) = if k==kstar then ppi x else parens (x<>el<>k)

instance (IsSpecialName i,Printable i,Printable t)
      => Printable (Qual i t) where
  ppi ([]:=>t) = ppi t
  ppi (ps:=>t) = sep [ppiFTuple ps <+> imp, letNest t]

instance (Printable x,Printable t) => Printable (Typing x t) where
  ppi (x:>:t) = sep [wrap x <+> el,letNest t]
  ppiList xts = vcat xts

instance (ValueId i,TypeId i) => Printable (TypeInfo i) where
  ppi i =
      case i of
	Data -> ppi "data" -- <+> o
	Newtype -> ppi "newtype" -- <+> o
	Class super ps fundeps methods ->
	  "class" <+> sep [ppi (ppContext super<+>"_"<+>fsep (map ppKinded ps)),
			    ppFunDeps fundeps,
			    ppi "where", letNest methods]
	Synonym ps t -> 
	  "type" <+> appv (p:ps) <+> "=" <+> letNest t
	Tyvar -> ppi "type variable"
    where
      p =  localVal "_"
      appv = asType . appT . map tyvar

asType = id :: Type i -> Type i

instance (IsSpecialName i,Printable i) => Printable (Subst i) where
  ppi (S s) = ppi s
