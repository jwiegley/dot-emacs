module IsabelleDecl where
import IsabelleType(ConstsDecl,TypesDecl,DomainType,DomainDecl(..))
import IsabelleTerm(HMatches,FixrecDecl(..))
import IsabelleProp(PredDecl,PropDecl)
import Mixfix

-- For top level declarations:

data IsaDecl
  = IsaTypes TypesDecl
  | IsaDomain DomainDecl
  | IsaConsts ConstsDecl
  | IsaFixrec FixrecDecl
  | IsaPredDecl PredDecl
  | IsaPropDecl PropDecl
  | IsaComment String

data Module = Module (String, [String]) [IsaDecl]

------------------------------------------------------------

instance Show IsaDecl where
  showsPrec p x = case x of
    IsaTypes d -> shows d
    IsaDomain d -> shows d
    IsaConsts d -> shows d
    IsaFixrec d -> shows d
    IsaPropDecl d -> shows d
    IsaPredDecl d -> shows d
    IsaComment s -> showLR "(*\n" "*)\n" (showString s)

instance Show Module where
  showsPrec p (Module (name,imports) decls) =
    showString "theory " . showString name .
    showString "\nimports " . showSpaceSep (map showString imports) .
    showString "\nbegin\n\n" .
    showSep (showString "\n") (map shows decls) .
    showString "\nend\n"
  