DOES NOT WORK

> module TypeInfer where
>
> import MonadTransformers
> import StateMTRefs
> import InstsST
> import System(getArgs)


This module contains a type inference algorithm for the simply-typed
lambda calculus ala Curry.

The syntax of types and terms is as follows:

> data Type s = TyVar (TyVarName s) | Type s :-> Type s
> data Term = Var Id | Abs Id Term | App Term Term 

Identifiers are just plain strings.  Type variable names are a little
more complicated.   The reason for this is that the type inference algorithm 
makes use of _unification_.   As a result, variables may be identified
with other types.  This is why we model them as pointers.

> type Id = String
> type TyVarName s = STRef s (Either Id (Type s))

The typing environment is a finite map from term variables to their 
corresponding types.  We model it a list.

> type TyEnv s = [(Id,Type s)]

The type inference monad:

> type TypeInfM s
>   = WithEnv (TyEnv s)     -- typing environment
>   ( WithState [Id]        -- identifier supply
>   ( WithExcept String     -- error detection
>   ( ST s
>   )))

Making a new type variable.

> newTyVar :: TypeInfM s (Type s)
> newTyVar = do
>   x:_ <- updSt tail
>   n <- newRef (Left x)
>   return (TyVar n)


Looking up the type of an identifier.

> -- lookupVar :: Id -> TypeInfM s (Type s)
> lookupVar x = do
>   bindings <- getEnv
>   case lookup x bindings of
>       Nothing -> raise $ "Free variable: " ++ x
>       Just t  -> return t 

> hasType :: Id -> Type s -> TyEnv s -> TyEnv s
> (x `hasType` t) bindings = (x,t) : bindings

> typeOf :: Term -> TypeInfM s (Type s)
> typeOf (Var x) = lookupVar x 
> typeOf (Abs x e) = do
>   t  <- newTyVar
>   t' <- inModEnv (x `hasType` t) (typeOf e) 
>   return (t :-> t')
> typeOf (App e1 e2) = do
>   t  <- typeOf e1
>   t' <- typeOf e2
>   x  <- newTyVar 
>   unify t (t' :-> x)
>   return x


> unify :: Type s -> Type s -> TypeInfM s ()
> unify (TyVar x) t = x |-> t
> unify t (TyVar x) = x |-> t
> unify (s :-> s') (t :-> t') = unify s t >> unify s' t'


> (|->) :: TyVarName s -> Type s -> TypeInfM s ()
> x |-> t = follow t >>= bindTo
>   where
>   bindTo (TyVar y)
>       | x == y = return ()
>   bindTo t = do
>       occurs <- x `occursIn` t
>       if occurs then raise "Occurs check!" 
>                 else writeRef x (Right t)

> follow it@(TyVar x) = readRef x >>= either (const (return it)) follow
> follow it = return it

> occursIn :: TyVarName s -> Type s -> TypeInfM s Bool
> x `occursIn` t = do
>   t' <- follow t
>   case t' of
>       TyVar y -> return (x == y)
>       a :-> b -> do
>           inA <- x `occursIn` a
>           inB <- x `occursIn` b
>           return (inA || inB)


-- tests ---------------------------------------------------------------------

> test :: Term -> Either String String
> test t = runST
>   ( removeExcept
>   $ removeState_ names 
>   $ removeEnv []
>   $ typeOf t >>= showType      
>   )

> showType it = do
>   t <- follow it 
>   case t of
>       TyVar x -> do Left x <- readRef x; return x
>       a :-> b -> do
>           a' <- showType a
>           b' <- showType b
>           return $ "(" ++ a' ++ ") -> (" ++ b' ++ ")"

> names :: [Id]
> names = concat [ map (:d) ['a'..'z'] | d <- ["", "'"] ++ map show [1..] ]

> tId = Abs "x" $ Var "x"
> tK  = Abs "x" $ Abs "y" $ Var "x"
> tApp = Abs "f" $ Abs "x" $ App (Var "f") (Var "x")
> tS  = Abs "f" $ Abs "g" $ Abs "x" $ App (App (Var "f") (Var "x"))
>                                         (App (Var "g") (Var "x"))
> tSApp = Abs "x" $ App (Var "x" ) (Var "x")
> tO    = App tSApp tSApp

> tests = [tId, tK, tApp, tS, tSApp, tO]

> main = getArgs >>= putStrLn . show . test . (tests !!) . read . head

