{-# LANGUAGE DeriveDataTypeable #-}

import Data.Generics.Zipper
import Data.Data
import Data.Typeable

main = putStrLn "hello"

{- 

Based on example in "Scrap your zippers: a generic zipper for
heterogeneous types" by Michael Adams

-}

data Dept     = D Manager [Employee] deriving (Show, Typeable, Data)
data Employee = E Name Salary        deriving (Show, Typeable, Data)

type Salary = Float 
type Manager = Employee 
type Name = String


dept :: Dept 
dept = D agamemnon [menelaus, achilles, odysseus]

agamemnon, menelaus, achilles, odysseus :: Employee
agamemnon = E "Agamemnon" 5000 
menelaus  = E "Menelaus" 3000 
achilles  = E "Achilles" 2000 
odysseus  = E "Odysseus" 2000

----------------------------

g1 = toZipper dept

q1 = query cast g1 :: Maybe Dept

g2 =
 let Just g2' = down g1 
 in getHole g2' :: Maybe [Employee]

g3 =
 let 
  Just g2' = down g1 
  Just g3' = left g2'
 in getHole g3' :: Maybe Employee

-- Just (E "Agamemnon" 5000.0)
