module Monad where

import AST

----------------------------------------------------------------------
-- Values
----------------------------------------------------------------------

type EnvFrag = [(Name,M Value)]

data Value
  = 
--- scalars
    Z Integer
  | BV Bool
--- CBN functions
  | FV (M Value -> M Value)
--- Generic structured data
  | Tagged Name [M Value]
--- values for all tuples:
  | TupleVal [M Value]

data Fix a = Fix (Fix a -> a)
fix = \ f -> (\ (Fix x) -> 
                   (f (\ a -> x (Fix x) a)))
                      (Fix (\ (Fix x) -> (f (\ a -> x (Fix x) a))))

showValue :: Value -> String
showValue (Z i) = show i
showValue (BV i) = show i
showValue (FV _) = "(function)"
showValue (Tagged n arglist) = "(Tagged Value)"

instance Show Value where
  show = showValue

----------------------------------------------------------------------
-- Errors
----------------------------------------------------------------------

data Error a = Ok a | Err String

----------------------------------------------------------------------
-- Error monad
----------------------------------------------------------------------


errUnit :: a -> Error a
errUnit = Ok


errBind :: Error a -> (a -> Error b) -> Error b
errBind x f = case x of
                     (Ok v) -> f v
                     (Err msg) -> (Err msg)

instance Monad Error where
  return = errUnit
  (>>=) = errBind

showEC x =
       case x of
            (Ok v) -> show v
            (Err msg) -> show msg

showError :: Show a => Error a -> String
showError x =
       case x of
            (Ok v) -> show v
            (Err msg) -> show msg

instance Show a => Show (Error a) where
    show = showError

raise0 = Err

----------------------------------------------------------------------
-- Environments
----------------------------------------------------------------------

type Env = Name -> M Value

----------------------------------------------------------------------
-- M = Environment+Error 
----------------------------------------------------------------------

newtype M a = M (Env -> (Error a))

mUnit :: a -> M a
mUnit a = M (\rho -> return a)


mBind :: M a -> (a -> M b) -> M b
mBind x f =
        M (\rho -> 
                 do { v <- (deM x) rho ; deM (f v) rho })

instance Monad M where
  return = mUnit
  (>>=) = mBind

deM (M x) = x

lift :: Error a -> M a
lift ec = M (\ _ ->  ec)

----------------------------------------------------------------------
-- Non-standard Morphisms
----------------------------------------------------------------------

raise :: String -> M a
raise = \msg -> lift (raise0 msg)

rdEnv :: M Env
rdEnv = M (\rho -> return rho)

tweek f x y = \ z -> if x == z then y else f z

xEnv :: Env -> Name -> M Value -> Env
xEnv rho n phi = tweek rho n phi

inEnv :: Env -> M a -> M a
inEnv rho (M x) = M (\ _ -> x rho)
