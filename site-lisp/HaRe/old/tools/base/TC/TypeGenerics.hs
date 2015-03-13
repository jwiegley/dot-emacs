module TypeGenerics where

data GT s k r
  = S (s (GT s k r))
  | TVar (Int,r (Maybe (GT s k r))) k
  | TGen Int

data GErrType = MatchErr | OccursErr | ShapeErr | KindErr | GenErr
    deriving Show

type Map s k r = r[(Int,(Int,Ptr s k r),k)]
type Ptr s k r = (r(Maybe(GT s k r)))



data A s k a r m =
  A { sameVarA :: forall x . r x -> r x -> Bool
    , writeVarA :: forall x . r x -> x -> m()
    , readVarA :: forall x . r x -> m x
    , newVarA :: forall x . x -> m(r x)
    , nextA :: m Int
    , zeroA :: a
    , unionA :: [ a ] -> a
    , genErrA :: forall x. GErrType -> GT s k r -> GT s k r -> m x
    , seqA :: forall x . s(m x) -> m(s x)
    , mapA :: forall x y . (x -> y) -> s x -> s y
    , accA :: forall x y . (x -> y -> y) -> s x -> y -> y
    , matchA :: forall x . s x -> s x -> Maybe[(x,x)]
    , kindofA :: GT s k r -> m k
    , samekindA :: k -> k -> Bool
    }

data B s k a r m =
  B { unifyGT :: GT s k r -> GT s k r -> m a
    , matchGT :: GT s k r -> GT s k r -> m()
    , equalGT :: GT s k r -> GT s k r -> Bool
    , freshGT :: k -> m (GT s k r)
    , occursGT :: Ptr s k r -> GT s k r -> m Bool
    , colGT :: GT s k r -> m(GT s k r)
    , pruneGT :: GT s k r -> m(GT s k r)
    , substGT :: [GT s k r] -> GT s k r -> m(GT s k r)
    , genmapGT :: (Ptr s k r -> m Bool) -> Map s k r ->
                  GT s k r -> m(GT s k r)
    , genAnyGT :: forall x . (Map s k r -> x -> m x) -> x -> m([k],[GT s k r],x)
    , genGT :: (Ptr s k r -> m Bool) -> GT s k r -> m([k],[GT s k r],GT s k r)
    }

makeUnify :: Monad m => A s k a r m -> B s k a r m -- x
makeUnify lib =
  B { unifyGT = genericUnify
    , matchGT = match
    , equalGT = equal
    , freshGT = freshVar
    , occursGT = occursIn
    , colGT = col
    , pruneGT = prune
    , substGT = inst
    , genmapGT = tvar2tgen
    , genAnyGT = genAny
    , genGT = \ generic -> genAny (tvar2tgen generic)
    }
  where freshVar k = do { r <- newVarA lib Nothing
                        ; n <- nextA lib 
                        ; return (TVar (n,r) k) }
        prune (typ @ (TVar (n,ref) k)) =
          do { m <- readVarA lib ref
             ; case m of
                 Just t -> do { newt <- prune t
                              ; writeVarA lib ref (Just newt)
                              ; return newt }
                 Nothing -> return typ}
        prune x = return x
        col x =
          do { x' <- prune x
             ; case x' of
                (S y) -> do { t <- seqA lib (mapA lib col y)
                            ; return (S t)}
                (TVar (n,r) k) -> return(TVar (n,r) k)
                (TGen n) -> return(TGen n)}
        occursIn v t =
          do { t2 <- prune t
             ; case t2 of
                 S w -> do { s <- seqA lib (mapA lib (occursIn v) w)
                           ; return $ accA lib (||) s False }
                 TVar (m,z) k2 -> return $ sameVarA lib v z
                 TGen n    -> return False }
        varBind (r1 @ (n,r)) k1 t2 =
          do { b <- occursIn r t2
             ; k2 <- kindofA lib t2
             ; if b
                  then genErrA lib OccursErr (TVar r1 k1) t2
                  else if not(samekindA lib k1 k2)
                          then genErrA lib KindErr (TVar r1 k1) t2
                          else do { writeVarA lib r (Just t2); return (zeroA lib)}}
        genericUnify tA tB =
          do { t1 <- prune tA
             ; t2 <- prune tB
             ; case (t1,t2) of
                (TVar (n,r1) k1,TVar (m,r2) k2) ->   -- Both are Variables
                  if sameVarA lib r1 r2
                     then return (zeroA lib)
                     else do { writeVarA lib r1 (Just t2); return (zeroA lib)}
                (TVar r1 k1,_) -> varBind r1 k1 t2
                (_,TVar r2 k2) -> genericUnify t2 t1
                (TGen n,TGen m) -> if n==m then return(zeroA lib)
                                      else genErrA lib GenErr t1 t2
                (S x,S y) ->
                  case matchA lib x y of
                    Nothing -> genErrA lib MatchErr t1 t2
                    Just pairs -> do { cs <- mapM (uncurry genericUnify) pairs
                                     ; return (unionA lib cs)
                                     }
                (_,_) -> genErrA lib ShapeErr t1 t2                         
             }
        match tA tB =
          do { t1 <- prune tA
             ; t2 <- prune tB
             ; case (t1,t2) of
                 (TVar (n,r1) k1,_) ->
                    do { k2 <- kindofA lib t2
                       ; if samekindA lib k1 k2
                            then genErrA lib KindErr t1 t2
                            else do { writeVarA lib r1 (Just t2); return ()}

                       }
                 (TGen n,TGen m) -> if n==m then return()
                                      else genErrA lib GenErr t1 t2
                 (S x,S y) ->
                    case matchA lib x y of
                      Nothing -> genErrA lib ShapeErr t1 t2
                      Just pairs -> do { mapM_ (uncurry match) pairs
                                       ; return ()
                                       }
                 (_,_) -> genErrA lib ShapeErr t1 t2
             }
        equal x y =
          case (x,y) of
            (TVar (n,r1) k1,TVar (m,r2) k2) -> sameVarA lib r1 r2
            (TGen n,TGen m) -> m==n
            (S x,S y) -> case matchA lib x y of
                          Nothing -> False
                          Just pairs -> all (uncurry equal) pairs
            (_,_) -> False
        inst sub x =
          do { x' <- prune x
             ; case x' of
                 TVar r k -> return(TVar r k)
                 TGen n -> return (sub !! n)
                 S x -> do { x' <- seqA lib (mapA lib (inst sub) x)
                           ; return (S x')
             }             }
        findFresh nextN ((new, (n,oldvar),k2):rest) (m,ref) k env =
          if sameVarA lib ref oldvar
             then return (TGen new)
             else findFresh nextN rest (m,ref) k env
        findFresh nextN [] ref k env =
          do { old <- readVarA lib env
             ; writeVarA lib env ((nextN,ref,k):old)
             ; return (TGen nextN)
             }
        tvar2tgen generic env t =
          do { t2 <- prune t
             ; case t2 of
                 S x    -> do { x' <- seqA lib (mapA lib (tvar2tgen generic env) x)
                              ; return(S x') }
                 TGen n -> return t2
                 TVar (n,r) k -> -- Because of prune, "r" is NEVER of
                                 -- the form (TyVar (ref (Just t)) k)
                    do { b <- generic r
                       ; if b then (do { env' <- readVarA lib env
                                       ; findFresh (length env') env' (n,r) k env })
                              else return t2
                       }
             }
        genAny gen x =
            do { free <- newVarA lib []
               ; x' <- gen free x
               ; theta <- readVarA lib free
               ; let three (n,r,k) = k
                     g(n,r,k) = TVar r k
               ; return (map three theta,map g theta, x')
               }




           