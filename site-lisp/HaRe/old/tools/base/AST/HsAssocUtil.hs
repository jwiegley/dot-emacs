module HsAssocUtil where
import Data.Maybe(fromMaybe)
import HsAssocStruct

{-
class InfixEnv i env | env->i where
    extend :: env -> (i,HsFixity) -> env
    extend2 :: env -> env -> env
    defaultOps :: env -> [i] -> env
    lookUp :: env -> i -> Maybe HsFixity
-}
    
newtype OperatorEnv i = OperatorEnv [(i,HsFixity)] deriving (Show)

unOE (OperatorEnv e) = e
emptyOE = OperatorEnv []

--instance Eq i => InfixEnv i (OperatorEnv i) where
extend (OperatorEnv env) i = OperatorEnv (i: env)
extend2 (OperatorEnv env1) (OperatorEnv env2) = OperatorEnv (env2++env1)
defaultOps (OperatorEnv env) ns =
      OperatorEnv [f|f@(i,_)<-env,i `notElem` ns]
lookUp (OperatorEnv env) n = lookup n env

getFixity env = fromMaybe defaultFixity . lookUp env 
defaultFixity = HsFixity HsAssocLeft 9 -- See Haskell 98 Report, Section 4.4.2

-- Dubious functions, should be removed:
--getPrec env name  = case getFixity env name of HsFixity a p->p
--getAssoc env name = case getFixity env name of HsFixity a p->a
{- old verions:
getPrec env name  =
    case (lookUp env name) of 
      Just (HsFixity a p) -> p
      Nothing            -> 9 -- See the Report, section 4.4.2

getAssoc env name =
    case lookUp env name of 
      Just (HsFixity a p)  -> a
      Nothing             -> HsAssocLeft -- See the Report, section 4.4.2
-}
