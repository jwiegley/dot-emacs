{-# LANGUAGE DeriveDataTypeable #-}

{-

Playing with uniplate zippers, based on the paper: Michael D. Adams.
Scrap Your Zippers: A Generic Zipper for Heterogeneous Types, Workshop
on Generic Programming 2010.

Reference: http://hackage.haskell.org/packages/archive/uniplate/1.6.10/doc/html/Data-Generics-Uniplate-Zipper.html

Terminology/function names

Original : uniplate version
toZipper : zipper
         : zipperBi
fromZipper : fromZipper

left : left
right : right
up : up
down : down

query :: GenericQ b → Zipper a → b    : hole?
trans :: GenericT → Zipper a → Zipper a : replaceHole
transM :: (Monad m) => GenericM m → Zipper a → m (Zipper a) : ?

-}




import Data.Maybe

import Data.Generics as SYB

import Language.Haskell.Refact.Utils
import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.TypeUtils

import Data.Generics.Uniplate.Zipper
import Data.Generics.Uniplate.Data

-- ---------------------------------------------------------------------

data Term = Var String 
          | Lambda String Term 
          | App Term Term 
          | If Term Term Term
          deriving (Show,SYB.Data,SYB.Typeable)

fac = Lambda "n" (If (App (App (Var "=") (Var "n")) (Var "0")) 
                     (Var "1") 
                     (App (App (Var "+") (Var "n")) 
                          (App (Var "fac") 
                               (App (Var "pred") (Var "n")))))


zz = zipper fac

zr z = fromJust $ right z
zl z = fromJust $ left z
zd z = fromJust $ down z
zu z = fromJust $ up z

-- ---------------------------------------------------------------------

data Dept     = D Manager [Employee] deriving (Show, Typeable, Data)
data Employee = E Name Salary deriving (Show, Typeable, Data)
type Salary   = Float 
type Manager  = Employee 
type Name    = String


dept :: Dept 
dept = D agamemnon [menelaus, achilles, odysseus]

agamemnon, menelaus, achilles, odysseus :: Employee
agamemnon = E "Agamemnon" 5000 
menelaus  = E "Menelaus" 3000 
achilles  = E "Achilles" 2000 
odysseus  = E "Odysseus" 2000

zg = zipper dept

zgb :: Maybe (Zipper Dept (Dept,Int))
zgb = zipperBi dept

zb = fromJust $ (zipperBi dept :: Maybe (Zipper Dept Employee))

vall x = [(n,v) | E n v <- universeBi x]

extractSals :: (Data a) => a -> [(Name,Salary)]
extractSals x = [(n,v) | E n v <- (universeBi x)]

------------------------------------------------------------------------

data Expr = Var2 String
          | Lit Int
          | Call String [Expr]
            deriving (Data, Typeable)

data Stmt = While Expr [Stmt]
          | Assign String Expr
          | Sequence [Stmt]
            deriving (Data,Typeable)

extractLits :: Data a => a -> [Int]
extractLits x = [y | Lit y <- universeBi x]
