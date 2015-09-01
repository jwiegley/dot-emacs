module IsabelleType where
import Mixfix
import Char(isAlpha)

data Sort = Sort [String] | DefaultSort

tVar a = TVar a DefaultSort

data Type
  = TVar String Sort
  | TType String [Type]
  | TCfun Type Type
  | TFfun Type Type
  | TCprod Type Type
  | TSprod Type Type
  | TSsum Type Type

tApp (TType s ts) t = TType s (ts ++ [t])

foldr1' :: (a -> a -> a) -> a -> [a] -> a
foldr1' f z [] = z
foldr1' f z xs = foldr1 f xs

tCprods = foldr1' TCprod (TType "unit" [])
tSprods = foldr1' TSprod (TType "one" [])
tSsums  = foldr1' TSsum  (TType "unit" [])
tFfuns ts t = foldr TFfun t ts
tCfuns ts t = foldr TCfun t ts

tList t = TType "list" [t]

type TypePattern = Type

-- Datatype declarations

data TypesDecl = TypesDecl TypePattern Type

data TypeSig = TypeSig String Type
data ConstsDecl = ConstsDecl [TypeSig]

data Strictness = Lazy | Strict
data DomainArg = DomainArg Strictness String Type
data DomainCons = DomainCons String [DomainArg]
data DomainType = DomainType TypePattern [DomainCons]
data DomainDecl = DomainDecl [DomainType]

------------------------------------------------------------

instance Show Sort where
  showsPrec p DefaultSort = id
  showsPrec p (Sort xs) = showString "::" . case xs of
    [x] -> showString x
    xs -> showBraces (showCommaSep (map showString xs))

instance Show Type where
  showsPrec p x = case x of
    TVar a s -> showChar '\'' . showString a . shows s
    -- special case for list constructor
    TType "[]" [t] -> showSquares (shows t)
    -- special case for tuple constructors
    TType ('(':_) ts -> showSpace . showAngles (showCommaSep (map shows ts))
    TType c [] -> showTypeName c
    TType c [t] -> shows t . showSpace . showTypeName c
    TType c ts -> showParens (showCommaSep (map shows ts)) .
                  showSpace . showTypeName c
    TCfun  t t' -> mixfix "_ -> _" [showsPrec 1 t, showsPrec 0 t'] 0 p
    TFfun  t t' -> mixfix "_ => _" [showsPrec 1 t, showsPrec 0 t'] 0 p
    TCprod t t' -> mixfix "_ * _"  [showsPrec 21 t, showsPrec 20 t'] 20 p
    TSprod t t' -> mixfix "_ ** _" [showsPrec 21 t, showsPrec 20 t'] 20 p
    TSsum  t t' -> mixfix "_ ++ _" [showsPrec 11 t, showsPrec 10 t'] 10 p
    where showTypeName c = showString c -- ('H':c)

instance Show TypesDecl where
  showsPrec p (TypesDecl lhs rhs) =
    mixfix "types _ = _\n" [shows lhs, showQuotes (shows rhs)] 1000 p

instance Show TypeSig where
  showsPrec _ (TypeSig name typ) = if isAlpha (head name)
    then showString name . showString " :: " . showQuotes (shows typ)
    else showQuotes (showString ('`':name)) . showString " :: " .
      showQuotes (shows typ) . showString ("  (infixl \"`" ++ name ++ "\" 90)")

instance Show ConstsDecl where
  showsPrec _ (ConstsDecl sigs) =
    showString "consts\n" . showAll (map (showLR "  " "\n" . shows) sigs)
    
instance Show DomainArg where
  showsPrec _ (DomainArg str name t) = case (str,name) of
    (Strict, "") -> show_t
    (Strict, s)  -> showParens (showString s . showString "::" . show_t)
    (Lazy,   "") -> showParens (showString "lazy " . show_t)
    (Lazy,   s)  -> showParens
      (showString "lazy " . showString s . showString "::" . show_t)
    where show_t = showQuotes (shows t)

instance Show DomainCons where
  showsPrec _ (DomainCons s []) = showString s
  showsPrec _ (DomainCons s args) =
    showString s . showSpace . showSpaceSep (map shows args)

instance Show DomainType where
  showsPrec _ (DomainType t cons) =
    shows t . showString " = " . showBarSep (map shows cons)

instance Show DomainDecl where
  showsPrec _ (DomainDecl ds) =
    showString "domain\n" .
    showSep (showString "and\n") (map (showLR "  " "\n" . shows) ds)

------------------------------------------------------------
-- for testing
a' = tVar "a"
b' = tVar "b"
c' = tVar "c"
d' = tVar "d"
--a' = TVar "a" (Sort ["cpo"])

{-
domain 'a tree = Leaf (value :: "'a") | Node (children :: "'a forest")
and 'a forest = Empty | Trees (head :: "'a tree") (tail :: "'a forest")
-}

tree_forest :: DomainDecl
tree_forest = DomainDecl [tree, forest]
  where
    a_tree = TType "tree" [a']
    a_forest = TType "forest" [a']
    tree = DomainType a_tree [leaf, node]
    leaf = DomainCons "Leaf" [DomainArg Lazy "value" a']
    node = DomainCons "Node" [DomainArg Lazy "children" a_forest]
    forest = DomainType a_forest [empty, trees]
    empty = DomainCons "Empty" []
    trees = DomainCons "Trees"
      [DomainArg Lazy "" a_tree, DomainArg Strict "" a_forest]
