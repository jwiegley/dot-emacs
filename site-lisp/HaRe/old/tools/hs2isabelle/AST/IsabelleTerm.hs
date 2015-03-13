module IsabelleTerm where
import IsabelleType
import Mixfix

type Pattern = Term

-- LCF terms in HOLCF
data Term
  = HVar String
  | HAbs [String] Term -- should probably be [Pattern]
  | HAbsTuple [String] Term
  | HApp Term Term
  | HInfix Term String Term
  | HTuple [Term]
  | HList [Term]
  | HLet [HMatch] Term
  | HIte Term Term Term -- if-then-else
  | HInt Integer
  | HCase Term [HAlt]
  | HConstrain Term Type
  | HMixfix String [Int] Int [Term]

data HAlt = HAlt Pattern Term

head_of_Term :: Term -> String
head_of_Term (HApp t _) = head_of_Term t
head_of_Term (HInfix _ s _) = s
head_of_Term (HVar s) = s

-- hIte = HMixfix "If _ then _ else _ fi" [0,0,0] 60
hApps t ts = foldl HApp t ts
hCon c ts = hApps (HVar c) ts

isHVar (HVar _) = True
isHVar _ = False

hAbs (HVar x) (HAbs xs t) = HAbs (x:xs) t
hAbs (HVar x) t = HAbs [x] t
hAbs (HTuple ts) t | all isHVar ts = HAbsTuple (map (\(HVar x) -> x) ts) t
hAbs p t = error ("hAbs: illegal pattern " ++ show p)

hAbss ps t = foldr hAbs t ps

nomatch = HVar "UU"

data HMatch
  = HMatch Pattern Term

head_of_HMatch :: HMatch -> String
head_of_HMatch (HMatch lhs rhs) = head_of_Term lhs

data HMatches
  = HMatches [HMatch]

head_of_HMatches :: HMatches -> String
head_of_HMatches (HMatches (m:ms)) = head_of_HMatch m

data FixrecDecl
  = FixrecDecl [HMatches]

------------------------------------------------------------

instance Show Term where
  showsPrec p x = case x of
    HVar s -> showString s
    HAbs xs t -> mixfix "LAM _. _"
                    [showSpaceSep (map showString xs), showsPrec 10 t] 10 p
    HAbsTuple xs t -> mixfix "LAM <_>. _"
                    [showCommaSep (map showString xs), showsPrec 10 t] 10 p
    HApp t t' -> mixfix "_$_" [showsPrec 999 t, showsPrec 1000 t'] 999 p
    HInfix t o t' -> mixfix "_ `_ _" [showsPrec 900 t, showString o, showsPrec 900 t'] 0 p
    HTuple ts -> showSpace . showAngles (showCommaSep (map shows ts))
    HList [] -> showString "[:]"
    HList ts -> showLR "[:" ":]" (showCommaSep (map shows ts))
    HIte b x y -> mixfix "If _ then _ else _ fi" [shows b, shows x, shows y] 60 p
    HInt n -> shows n -- mixfix "Def _" [shows n] 999 p
    HMixfix s ps p0 ts -> mixfix s (zipWith ($) (map showsPrec ps) ts) p0 p
    HCase t alts ->
            mixfix "case _ of _" [shows t, showBarSep (map shows alts)] 10 p
    HConstrain x t -> mixfix "_::_" [showsPrec 4 x, shows t] 3 p

instance Show HAlt where
  showsPrec p (HAlt lhs rhs) = mixfix "_ => _" [shows lhs, shows rhs] 10 p

instance Show HMatch where
  showsPrec p (HMatch lhs rhs) = mixfix "_ = _" [showsPrec 50 lhs, showsPrec 51 rhs] 50 p

instance Show HMatches where
  showsPrec p (HMatches ms) = showAll (map (showLR "  \"" "\"\n" . shows) ms)

instance Show FixrecDecl where
  showsPrec _ (FixrecDecl blocks) =
    showString "fixrec\n" . (showSep (showString "and\n") (map shows blocks))
