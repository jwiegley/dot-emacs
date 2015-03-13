-----------------------------------------------------------------------------
-- |
-- Module      :  RefacUnGuard
-- Copyright   :  (c) Jose Proenca 2005
-- License     :  GPL
--
-- Maintainer  :  jproenca@di.uminho.pt
-- Stability   :  experimental
-- Portability :  portable
--
-- Refactoring that tries to convert guards to if then else, after merging
--  necessary matches.
--
-----------------------------------------------------------------------------

module RefacUnGuard(
    -- * The refactoring
    guardToIte, -- won't appear in report because no type information was given

{- | The main goal of this refactoring is to convert a function declaration
where guards can be found into another with no guards, and with /if then else/
expressions instead. But the biggest problem aboarded in this transformation is how to
remove this guards if they afect more than one match that can be merged into
a single one, where different name for the variables is used and some line swapping may
be needed.

This refactoring is then divided into three different sub-problems, that will
be explained in more detail in this document:

    * Check which matches can be converted and swaped with matches defined
      bellow, without changing the function behaviour;

    * Merge the similar matches with guards to a single match, renaming the
      needed variables;

    * In each match replace the guards by /if then else/ when possible.
-}

    -- * Stages of the refactoring
    -- ** Consistency check
{- | Before any other evaluation each match is compared with the matches below
on the same declaration by 'isConsist'. It is then associated with a boolean
that states if the declaration has any inconsitency below. A match is said to
be inconsitent with a second one below it if the patterns are not disjoint and
if a constant value is found in the a pattern of the second match where a
variable was in the first one. All possibles patterns were contemplated.

-}
    findConsist,
    isConsist,
    
    -- ** Merge of matches
{- | After knowing which matches can be manipulated and swaped, the next step
is to try to merge matches using all possible combinations.

Because there are sometimes the need to create fresh variables, a name that is
not the prefix of any of the variable names (in this case is the smaller
sequence of x's) is used as the base name and a counter is added to the
variable name. The 'mergeMatches' is a function that uses a state monad with
partiality, whith the base name and the conter inside the state, and that
fails when the merging of two matches is not possible.

Before trying to merge matches, the declarations of the consistent matches are
passed to inside the guards and to the main expressions, using the function 'declsToLet',
since after the merging the declarations will afect more than the original
expressions. This will duplicate the declarations inside the where clause.

-}

    getInitSt,
    dmerge,

{- | In the merge of two matches all the possible patterns were contemplated.
In some cases there is more than way to merge patterns. Each case will now be
explained in more detailed.

[Similar patterns]  If the two patterns are equivalent according to the
function 'similar', then no transformation is applied. Since this is the first
test to be performed, the patterns are considered to be different in the
remaing tests;

[Variables] When two different varibles are found they are replaced by a fresh
variable, in the pattern, in the guards and in the main expression;

[Parentisis] They are initialy ignored, and in the end they are placed back;

[WildCard (underscore)] Can only be matched with a variable. In this case a
fresh variable will replace both the wild card and the variable, in every
important place of the match;

[var \@ pattern] If both matches have this construction, then the variable and
the associated pattern are splited into two different patterns, and after the
recursive evaluation the resulting variable is \"glued\" back to the resulting
pattern. If only one match have this construction, then the variable is
replaced by a fresh variable, so that the same variable can also be assigned
to the second pattern; 

[Irrefutable pattern] When a irrefutable pattern is found, it is replaced by a
fresh variable, and inside the guards and in the main expression a /let/
constructor is added, assigning the irrefutable pattern to take the value of
the fresh variable. This way the fact that haskell uses lazy evaluation allows
the behaviour of the function to be the same as before;


[Constructors with fields] Whenever a constructor with fields is found, it is
converted into a pattern where the constructor is applied to the different
variable, using wild cards to when a variable name is not assigned;

[Application] When in both matches a application of a constructor is found,
and the constructors are similar (according to the 'similar' function), then
the list of arguments are added to the remaining patterns to be merged, and in
the end they are extracted and \"glued\" with constructor again;

[Infix application] Same approach to normal application was taken.

[Tupples and lists] Each pattern inside the tupple or list is added to the
remaining patterns to be merged, and in the end they are \"glued\" again with
the tuple or list constructor.

-}
    mergeMatches,



    -- ** Conversion from guards to /if then else/'s
{- | The final stage is the most simple one, since there are not many cases to
evaluate. The function 'guards2ifs' is applied to each match with a guard and
with the consisty check mark. When the /otherwise/ guard is not found
the /else/ of the resultig expression issues an error message. 
-} 
    guards2ifs,

    -- * Auxiliary functions
{-| In this section some of the auxiliary functions used in this
refactoring are presented. This functions may be of some use in later refactorings.
-}
    similar,
    differ,
    replaceExp,
    declsToLet,
    pRecToPApp
    
    -- * Future work
{- | This refactoring tries to be as complete as possible, but it is still
possible to improve some cases. A possible improvement would be to infer the /otherwise/
case, as presented in the following example:

@
f x | x > 0 = 1
f x = 0
@

that could be initialy converted to

@
f x | x > 0 = 1
f x | otherwise = 0
@

but instead it does nothing to avoid overriding the last expression. This is
not very easy because a single expression in the end may be used to merge with
more then one group of matches above.

Another improvement would be to check if the declarations could also be merged
before converting them into /if then else/'s.
-}

    ) where

import RefacUtils
import PrettyPrint (pp)
import Data.Maybe 
import Control.Monad.State 

type Match = HsMatchI PNT (HsExpI PNT) (HsPatI PNT) [HsDeclI PNT]

guardToIte args  
 = do let fileName = ghead "filename" args       
          row      = read (args!!1)::Int        
          col      = read (args!!2)::Int        
      modInfo@(_,exps, mod, _)<-parseSourceFile fileName  
      let pn =locToPN fileName (row, col) mod                                 
          decls = definingDecls [pn] (hsModDecls mod) False False
      if decls /= []
         then do r <- applyRefac (replaceGuards (head decls)) (Just modInfo) fileName
                 writeRefactoredFiles False [r]      
         else error "\nInvalid cursor position!"  



-- | Applies the transformation to a given declaration, using the auxiliary functions
--  defined bellow
replaceGuards d@(Dec (HsFunBind loc matches)) (_,_,mod)
    = do let newMs1 = findConsist matches -- :: [(Bool,Match)]
             initSt = getInitSt [m | (b,m) <- newMs1, b]
             newMs2 = map declsToLet' newMs1
             newMs3 = dmerge newMs2 initSt
             newMs4 = map guards2ifs newMs3 
         update d
                -- to see intermediate results use this line with the desired number 
                --(error (show [(b,pp m) | (b,m)<-newMs1]))
                --(Dec (HsFunBind loc (map snd newMs1)))
                (Dec (HsFunBind loc newMs4))
                mod
replaceGuards decl (_,_,mod) = return mod

-- | Convert a match with guards to another match where the guards are
--   translated to /if then else/'s
guards2ifs :: (Bool,HsMatchP) -> HsMatchP
guards2ifs (True, HsMatch l i p (HsGuard lst) ds) = HsMatch l i p (HsBody $ g2i lst) ds
     where
        -- the empty list should never occur
        g2i [] = error "empty list of guards!"
        g2i [(loc,cond,exp)] 
            | isOtherwise cond = exp
            | otherwise = mkIte cond exp undefError
        g2i ((loc,cond,exp):xs) = mkIte cond exp (g2i xs)

        isOtherwise (Exp (HsId (HsVar (PNT (PN (UnQual "otherwise")
            (G (PlainModule "Prelude") "otherwise"
            (N (Just _)))) Value (N (Just _))))))
                      = True
        isOtherwise _ = False

        mkIte e1 e2 e3 = Exp (HsIf e1 e2 e3)

        undefError = (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "error")
                     (G (PlainModule "Prelude") "error" 
                     (N (Just loc0)))) Value (N (Just loc0)))))) (Exp
                     (HsLit loc0 (HsString "UnMatched Pattern")))))

guards2ifs (_,x) = x

     


--------------------------
--- Consistency check ---- 
--------------------------

-- | Given a set of matches, checks which ones have guards that can be
--  removed without afecting the program's behaviour. This implies going throw
--  every pattern to check if each pair is similar, disjoint or inconsistent.
--  It uses the binary function 'isConsist'.
findConsist :: [HsMatchP] -> [(Bool,HsMatchP)]
findConsist [] = []
findConsist (m:ms) 
       = let ms' = findConsist ms
         in case m of
            (HsMatch _ _ pats (HsGuard _) _)
                    -> (and $ map (checkGuard m) $ map (isConsist pats . getPats) ms
                       , m) : ms'
            _ -> (False,m) : ms'
  where
    getPats (HsMatch _ _ pats _ _) = pats

    -- if a match is consistent with every match below, but not disjoint, then
    --  the guard can only be removed if it exists
    checkGuard (HsMatch _ _ _ (HsGuard _) _) Nothing = True
    checkGuard (HsMatch _ _ _ _ _) Nothing = False
    checkGuard _ (Just x) = x
    

-- | Checks if two lists of patterns are consistents. Possible results are:
--
--  - Just True  - if disjoint patterns are found
--
--  - Just False - if an incongruence is found and there are no disjoint patterns
--
--  - Nothing    - if no incongruence nor disjoint patterns are found
isConsist :: [HsPatP] -> [HsPatP] -> Maybe Bool
isConsist [] _ = Nothing
isConsist _ [] = Nothing
-- similar values -> continue
isConsist (p1:pats1) (p2:pats2) | p1 `similar` p2
    = isConsist pats1 pats2
-- different constants -> True 
isConsist (k1:pats1) (k2:pats2) | isConstant k1 && isConstant k2
    = if k1 `differ` k2  then Just True
                         else isConsist pats1 pats2
-- var - const -> False
isConsist ((Pat (HsPId (HsVar _))):pats1) (k:pats2) | isConstant k
        = case isConsist pats1 pats2 of
             Just True -> Just True
             _         -> Just False
-- const - var -> False
isConsist (k:pats1) ((Pat (HsPId (HsVar _))):pats2) | isConstant k
        = case isConsist pats1 pats2 of
             Just True -> Just True
             _         -> Just False
-- var - var -> continue
isConsist ((Pat (HsPId (HsVar _))):pats1) ((Pat (HsPId (HsVar _))):pats2)
    = isConsist pats1 pats2

---- const - _ -> Continue
--isConsist (k:pats1) (_:pats2) | isConstant k
--        = isConsist pats1 pats2
---- _ - var -> Continue
--isConsist (_:pats1) ((Pat (HsPId (HsVar _))):pats2)

--      = isConsist pats1 pats2
-- x - y -> unfold x and y, and check if they are consistent before continuing
isConsist (pat1:pats1) (pat2:pats2)
      = case  isConsist (unfoldPat pat1) (unfoldPat pat2) of
           Just True -> Just True
           Nothing   -> isConsist pats1 pats2
           _         -> case isConsist pats1 pats2 of
                           Just True -> Just True
                           _         -> Just False


-- Only used in the consistency check.
-- For each complex pattern, it is decomposed into a list of more simple patterns,
--   that will be checked for consistency.
unfoldPat :: HsPatP  -> [HsPatP]
unfoldPat (Pat HsPWildCard)    = [nameToPat "_"] -- name is not important
unfoldPat (Pat (HsPIrrPat p))  = [nameToPat "irr"] -- name is not important
unfoldPat (Pat (HsPAsPat i p)) = unfoldPat p
unfoldPat  (Pat (HsPApp i ps))
    = (Pat $ HsPId $ HsCon i) : (map unparen ps)
unfoldPat (Pat (HsPInfixApp p1 i p2))
    = (Pat $ HsPId (HsCon i)) : (map unparen [p1,p2])
unfoldPat (Pat prec@(HsPRec constr fields))
    = unfoldPat (Pat $ pRecToPApp prec)
unfoldPat (Pat (HsPList _ lst))
    = (Pat $ HsPId $ HsCon $ nameToPNT "(:)"):lst -- the name is not important
unfoldPat (Pat (HsPTuple _ lst)) 
    = (Pat $ HsPId $ HsCon $ nameToPNT "(tup)"):lst -- the name is not important
unfoldPat x@(Pat _) = [unparen x]

unparen (Pat (HsPParen m)) = unparen m
unparen x = x



                   

-------------------------
--- merge of matches ---- 
-------------------------

-- To create fresh variables a partial State monad is used, to store the base name and the seed.
type ST = StateT St Maybe

data St = St {baseName :: String,
              seed :: Int}

getSt :: ST St
getSt = do sd <- gets seed
           bn <- gets baseName
           return $ St bn sd

getSeed :: ST Int
getSeed = do n <- gets seed
             modify (\s -> s {seed = n+1})
             return n

getFreshVar :: ST String
getFreshVar = do s <- getSeed
                 n <- gets baseName
                 return (n++"_"++(show s))


-- | To get an initial state it is necessery to find a base name that is not prefix of any of the used names.
-- In this case it will be 'x' replicated until it is not a prefix. The
-- counter is initiated to zero.
getInitSt :: [HsMatchP] -> St
getInitSt ms
  = let xs = (runIdentity $ applyTU strat ms) :: [Int]
        base = replicate (maximum xs) 'x'
    in St base 0
 where strat = full_tdTU ((constTU [1]) `adhocTU` getNumberX)
       getNumberX :: HsIdentI PNT -> Identity [Int]
       getNumberX (HsVar pnt) =
            let name = pNTtoName pnt
                n = length $ takeWhile (=='x') name
            in return $ [n+1]
       getNumberX _ = return []



-- | Distributes the binary function 'mergeMatches'.
--
-- The state of each evaluation of 'mergeMatches' as to be extracted to be
--  passed to further calls. It doesn't make sense to put the same state
--  inside 'dmerge', because it would fail when the first 'mergeMatches' failed,
--  which is not desired.  
dmerge :: [(Bool,HsMatchP)] -> St -> [(Bool,HsMatchP)]
dmerge [] _ = []
dmerge [x] _ = [x]
dmerge ((False,h):rest) st = (False,h):(dmerge rest st)
dmerge ((True,h):rest) st 
    = case dmerge2 h rest st of
        Just (st',newMs) -> dmerge newMs st'
        Nothing -> (True,h) : (dmerge rest st)

dmerge2 h [] _ = fail "end"
dmerge2 h ((False,t):rest) st
  = do (st',newMs) <- dmerge2 h rest st
       return (st',(False,t):newMs)
dmerge2 h ((True,t):rest) st
  = case tryMergeMatches h t st of
        Just (st',newM)
           -> return (st',(True,newM):rest)
        _  -> do (st',newMs) <- dmerge2 h rest st
                 return (st',(True,t):newMs)

tryMergeMatches h t st
    = evalStateT
         (do newM <- mergeMatches h t
             st' <- getSt
             return (st',newM))
         st
                 


{- | Tries to merge two matches with guards, using a state monad to create
fresh variables whith partiality to fail when no merging is possible.
-}
mergeMatches :: HsMatchP
             -> HsMatchP
             -> ST HsMatchP

-- no more patterns
mergeMatches (HsMatch l1 i1 [] (HsGuard lst1) ds) (HsMatch l2 i2 [] (HsGuard lst2) _)
    = return $ HsMatch l1 i1 [] (HsGuard (lst1++lst2)) ds

-- similar values
mergeMatches (HsMatch l1 i1 (p1:pats1)  e1 [])
             (HsMatch l2 i2 (p2:pats2)  e2 []) 
    | p1 `similar` p2 
     = do HsMatch l i ps e _ <- mergeMatches (HsMatch l1 i1 pats1 e1 [])
                                             (HsMatch l2 i2 pats2 e2 [])
          return $ HsMatch l i (p1:ps) e []

-- parentisis
mergeMatches (HsMatch l1 i1 ((Pat (HsPParen p1)):ps1) e1 [])
             (HsMatch l2 i2 ((Pat (HsPParen p2)):ps2) e2 []) 
    = do HsMatch l i (p:ps) e _ <- mergeMatches (HsMatch l1 i1 (p1:ps1) e1 [])
                                                (HsMatch l2 i2 (p2:ps2) e2 [])
         return $ HsMatch l i ((Pat (HsPParen p)):ps) e []
mergeMatches (HsMatch l1 i1 ((Pat (HsPParen p1)):ps1) e1 []) m2 
    = do HsMatch l i (p:ps) e _ <- mergeMatches (HsMatch l1 i1 (p1:ps1) e1 []) m2
         return $ HsMatch l i ((Pat (HsPParen p)):ps) e []
mergeMatches m1 (HsMatch l2 i2 ((Pat (HsPParen p2)):ps2) e2 [])
    = do HsMatch l i (p:ps) e _ <- mergeMatches m1 (HsMatch l2 i2 (p2:ps2) e2 [])
         return $ HsMatch l i ((Pat (HsPParen p)):ps) e []

-- WildCard
{-mergeMatches (HsMatch l1 i1 ((Pat HsPWildCard):ps1) e1 [])
             (HsMatch l2 i2 ((Pat HsPWildCard):ps2) e2 [])
    = do HsMatch l i (p:ps) e _ <- mergeMatches (HsMatch l1 i1 ps1 e1 [])
                                                (HsMatch l2 i2 ps2 e2 [])
         return $ HsMatch l i ((Pat HsPWildCard):ps) e []-}
mergeMatches (HsMatch l1 i1 ((Pat HsPWildCard):ps1) e1 [])
             (HsMatch l2 i2 ((Pat (HsPId (HsVar var))):ps2) e2 [])
    = do v <- getFreshVar
         let e2' = replaceRhs var v Nothing e2
         HsMatch l i ps e _ <- mergeMatches (HsMatch l1 i1 ps1 e1 [])
                                            (HsMatch l2 i2 ps2 e2' [])
         return $ HsMatch l i ((Pat $ HsPId $ HsVar $ changeName var v):ps) e []
mergeMatches (HsMatch l1 i1 ((Pat (HsPId (HsVar var))):ps1) e1 [])
             (HsMatch l2 i2 ((Pat HsPWildCard):ps2) e2 [])
    = do v <- getFreshVar
         let e1' = replaceRhs var v Nothing e1
         HsMatch l i ps e _ <- mergeMatches (HsMatch l1 i1 ps1 e1' [])
                                            (HsMatch l2 i2 ps2 e2 [])
         return $ HsMatch l i ((Pat $ HsPId $ HsVar $ changeName var v):ps) e []

-- x @ pat
mergeMatches (HsMatch l1 i1 ((Pat (HsPAsPat var1 p1)):ps1) e1 [])
             (HsMatch l2 i2 ((Pat (HsPAsPat var2 p2)):ps2) e2 [])
    = do HsMatch l i ((Pat (HsPId (HsVar var))):p:ps) e _ <-
                 mergeMatches (HsMatch l1 i1 ((Pat $ HsPId $ HsVar var1):p1:ps1) e1 [])
                              (HsMatch l2 i2 ((Pat $ HsPId $ HsVar var1):p2:ps2) e2 [])
         return $ HsMatch l i ((Pat $ HsPAsPat var p):ps) e []
mergeMatches (HsMatch l1 i1 ((Pat (HsPAsPat var p1)):ps1) e1 [])
             (HsMatch l2 i2 ps2 e2 [])
    = do v <- getFreshVar
         let e1' = replaceRhs var v Nothing e1
             var' = changeName var v
         HsMatch l i (p:ps) e _ <- mergeMatches (HsMatch l1 i1 (p1:ps1) e1' [])
                                                (HsMatch l2 i2 ps2 e2 [])
         return $ HsMatch l i ((Pat $ HsPAsPat var' p):ps) e []
mergeMatches (HsMatch l1 i1 ps1 e1 [])
             (HsMatch l2 i2 ((Pat (HsPAsPat var p2)):ps2) e2 [])
    = do v <- getFreshVar
         let e2' = replaceRhs var v Nothing e2
             var' = changeName var v
         HsMatch l i (p:ps) e _ <- mergeMatches (HsMatch l1 i1 ps1 e1 [])
                                                (HsMatch l2 i2 (p2:ps2) e2' [])
         return $ HsMatch l i ((Pat $ HsPAsPat var' p):ps) e []


-- ~ pat
mergeMatches (HsMatch l1 i1 ((Pat (HsPIrrPat p1)):ps1) e1 [])
             (HsMatch l2 i2 ps2 e2 [])
    = do v <- getFreshVar
         let e1' = addLet p1 (nameToExp v)  e1
             p1' = nameToPat v
         mergeMatches (HsMatch l1 i1 (p1':ps1) e1' [])
                      (HsMatch l2 i2 ps2 e2 [])
mergeMatches (HsMatch l1 i1 ps1 e1 [])
             (HsMatch l2 i2 ((Pat (HsPIrrPat p2)):ps2) e2 [])
    = do v <- getFreshVar
         let e2' = addLet p2 (nameToExp v) e2
             p2' = nameToPat v
         mergeMatches (HsMatch l1 i1 ps1 e1 [])
                      (HsMatch l2 i2 (p2':ps2) e2' [])

-- C { ...}
mergeMatches (HsMatch l1 i1 (Pat (r@(HsPRec _ _)):ps1) e1 [])
             (HsMatch l2 i2 ps2 e2 [])
    = mergeMatches (HsMatch l1 i1 ((Pat (pRecToPApp r)):ps1) e1 [])
                   (HsMatch l2 i2 ps2 e2 [])
mergeMatches (HsMatch l1 i1 ps1 e1 [])
             (HsMatch l2 i2 (Pat (r@(HsPRec _ _)):ps2) e2 [])
    = mergeMatches (HsMatch l1 i1 ps1 e1 [])
                   (HsMatch l2 i2 ((Pat (pRecToPApp r)):ps2) e2 [])
                    

-- 2 variables (different)
mergeMatches (HsMatch l1 i1 ((Pat (HsPId (HsVar var1))):pats1)  e1 [])
             (HsMatch l2 i2 ((Pat (HsPId (HsVar var2))):pats2)  e2 [])
    = do v <- getFreshVar
         let e1' = replaceRhs var1 v Nothing     e1
             e2' = replaceRhs var2 v (Just var1) e2
         HsMatch l i ps e _ <- mergeMatches (HsMatch l1 i1 pats1 e1' [])
                                            (HsMatch l2 i2 pats2 e2' [])
         return $ HsMatch l i ((Pat $ HsPId $ HsVar $ changeName var1 v):ps) e []

-- application
mergeMatches (HsMatch l1 i1 ((Pat (HsPApp pnt1 lst1)):pats1)  e1 [])
             (HsMatch l2 i2 ((Pat (HsPApp pnt2 lst2)):pats2)  e2 [])
   | pnt1 `similar` pnt2
    = do let n = length lst1 -- assuming equal lengths
         HsMatch l i ps e _ <- mergeMatches (HsMatch l1 i1 (lst1++pats1) e1 [])
                                            (HsMatch l2 i2 (lst2++pats2) e2 [])
         let (lst',ps') = splitAt n ps
         return $ HsMatch l i ((Pat (HsPApp pnt1 lst')):ps') e []

-- infix application
mergeMatches (HsMatch l1 i1 ((Pat (HsPInfixApp pl1 op1 pr1)):pats1)  e1 [])
             (HsMatch l2 i2 ((Pat (HsPInfixApp pl2 op2 pr2)):pats2)  e2 [])
   | op1 `similar` op2
    = do HsMatch l i (pl:pr:ps) e _ <- 
                  mergeMatches (HsMatch l1 i1 (pl1:pr1:pats1) e1 [])
                               (HsMatch l2 i2 (pl2:pr2:pats2) e2 [])
         return $ HsMatch l i ((Pat (HsPInfixApp pl op2 pr)):ps) e []

-- tuples
mergeMatches (HsMatch l1 i1 ((Pat (HsPList loc1 lst1)):pats1)  e1 [])
             (HsMatch l2 i2 ((Pat (HsPList loc2 lst2)):pats2)  e2 [])
    = do let n = length lst1 -- assuming equal lengths
         HsMatch l i ps e _ <- mergeMatches (HsMatch l1 i1 (lst1++pats1) e1 [])
                                            (HsMatch l2 i2 (lst2++pats2) e2 [])
         let (lst',ps') = splitAt n ps
         return $ HsMatch l i ((Pat (HsPList loc1 lst')):ps') e []

-- lists
mergeMatches (HsMatch l1 i1 ((Pat (HsPTuple loc1 lst1)):pats1)  e1 [])
             (HsMatch l2 i2 ((Pat (HsPTuple loc2 lst2)):pats2)  e2 [])
    = do let n = length lst1 -- assuming equal lengths
         HsMatch l i ps e _ <- mergeMatches (HsMatch l1 i1 (lst1++pats1) e1 [])
                                            (HsMatch l2 i2 (lst2++pats2) e2 [])
         let (lst',ps') = splitAt n ps
         return $ HsMatch l i ((Pat (HsPTuple loc1 lst')):ps') e []

-- merge is not possible
mergeMatches m1 m2 
    = fail "no merge possible"



---------------------------
--- Auxiliary functions ---
---------------------------

-- puts declarations inside an expression by the use of let
declsToLet' :: (Bool,HsMatchP) -> (Bool,HsMatchP)
declsToLet' (False,m) = (False,m)
declsToLet' (True,HsMatch l i p rhs ds)
    =  (True,HsMatch l i p (declsToLet rhs ds) [])

-- | Places declarations inside an expression by the use of the /let/
--   constructor
declsToLet :: RhsP -> [HsDeclP] -> RhsP
declsToLet x [] = x
declsToLet (HsBody e) ds    = HsBody (Exp (HsLet ds e))
declsToLet (HsGuard lst) ds = HsGuard $ map aux lst
    where aux (l,e1,e2) = (l,Exp (HsLet ds e1) , Exp (HsLet ds e2))

addLet :: HsPatP -> HsExpP -> RhsP -> RhsP
addLet pat exp1 (HsBody exp2) 
    = HsBody $ Exp (HsLet [Dec $ HsPatBind loc0 pat (HsBody exp1) []] exp2)
addLet pat exp1 (HsGuard lst) =  HsGuard $ map aux lst
    where aux (l,e1,e2) = (l,
                           Exp (HsLet [Dec $ HsPatBind loc0 pat (HsBody exp1) []] e1),
                           Exp (HsLet [Dec $ HsPatBind loc0 pat (HsBody exp1) []] e2))


-- | Relplaces a variable by another, without checking if it will become bounded or not
--  (should be used fresh variables for that).
replaceRhs u v l (HsBody e) = HsBody (replaceExp u v l e)
replaceRhs u v lc (HsGuard lst) = HsGuard $
                               map (\(l,e1,e2)->(l,replaceExp u v lc e1,replaceExp u v lc e2))
                               lst


-- | Replaces a variable name (given a PNT) by changing the name to a new name
--  and, when another PNT is passed, also changes the source location to the
--  same the second PNT.
replaceExp :: Term t => PNT -> String -> Maybe PNT -> t -> t
--replaceExp pnt@(PNT (PN (UnQual "x") _) _ _) str l exp =
--  error $ "trying to replace "++ show pnt ++" by \""++str++"\" with possible location "++show l ++" in expression "++show exp--pp exp
replaceExp pnt str locPnt exp
    = let exp1 = evalState (renamePN (pNTtoPN pnt) Nothing str False exp)
                undefined --(([],undefined),undefined)
          exp2 = let loc1 = getLoc pnt
                     loc2 = getSLoc $ fromJust locPnt
                 in replaceSLoc loc1 loc2 exp1
      in if isJust locPnt then exp2 
                          else exp1
  where
    getLoc = useLoc
    getSLoc (PNT (PN _ (S loc)) _ _) = loc

    replaceSLoc loc1 loc2 exp = runIdentity $ applyTP strat exp
        where strat = full_tdTP (adhocTP idTP replace)
              replace (S loc) | loc == loc1 = return $ S loc2
              replace x = return x


-- changes the name of a PNT, preserving the remaining information
changeName (PNT (PN (Qual mod  v) orig) a b) nv
   = (PNT (PN (Qual mod nv) orig) a b)
changeName (PNT (PN (UnQual  v) orig) a b)   nv
   = (PNT (PN (UnQual nv) orig) a b)

-- |Checks if two terms are similar, by using the defined equality, and after some
--  simplifications to the term:
--
--       * all locations are converted to the \"unknown\" location (are ignored)
--
--       * the origin location of the PN's is set to a null position in a file
--          with the same name that the variable, because two PN's are considered
--          to be equal if they have the same origin location, but in this case two
--          PN's  should be similar if they have the same name.
similar :: (Eq t1, Term t1) => t1 -> t1 -> Bool
similar x y = unLocate x == unLocate y
  where
   unLocate = runIdentity . applyTP strat
      where strat = full_buTP (idTP `adhocTP` getIdName `adhocTP` eraseLoc `adhocTP` unparenP `adhocTP` unparenE)
            getIdName (PN v@(UnQual str) id) = return $ PN v (S (SrcLoc str 0 0 0))
            getIdName (PN v@(Qual m str) id) = return $ PN v (S (SrcLoc (pp m ++ str) 0 0 0))
            eraseLoc (SrcLoc _ _ _ _) = return loc0
            unparenP :: HsPatI PNT -> Identity (HsPatI PNT)
            unparenP (Pat (HsPParen p)) = return p
            unparenP x = return x
            unparenE :: HsExpI PNT -> Identity (HsExpI PNT)
            unparenE (Exp (HsParen e)) = return e
            unparenE x = return x

-- | Checks if two terms differ by negating the 'similar' definition
differ :: (Eq t1, Term t1) => t1 -> t1 -> Bool
differ x = not . similar x

-- | Checks if a given pattern is a constant. The possible constants are
--   constructors, literals and negations.
isConstant :: HsPatP -> Bool
isConstant (Pat (HsPId (HsCon _))) = True
isConstant (Pat (HsPLit _ _)) = True
isConstant (Pat (HsPNeg _ _)) = True
isConstant _ = False

-- | Converts a constructor with fields in a pattern to the corresponding patterns
--   with the same constructor but without the fields (ex: C {x = myx} --> C myx _)
pRecToPApp (HsPRec constr fields)
                = let fieldsNames = getInfo constr
                      patFields = buildFields fieldsNames fields
                  in HsPApp constr patFields
   where
            getInfo x@(PNT _ --(PN name _)
                           (ConstrOf _ (TypeInfo {constructors = constrs})) _)
              = let name = pNTtoName x -- case name of UnQual n -> n; Qual _ n -> n
                    fields = findFields constrs

                    findFields [] = Nothing
                    findFields ((ConInfo {conName = PN n _ , conFields = f}):tl)
                        | n == name = f
                        | otherwise  = findFields tl

                    getFieldNames Nothing = error $ "No fields were found for the constructor "++ name
                    getFieldNames (Just fs) = [str | (PN str _) <- fs]
                in getFieldNames fields

            buildFields fNames usedFields = map (update usedFields) fNames
               where update lst name =
                        case findName name lst of
                            Just pat -> pat
                            Nothing  -> Pat HsPWildCard --nameToPat name -- the name doesn't matter, because is only to check consistency
                     findName _ [] = Nothing
                     findName name ((HsField pnt pat):fs)
                          | pNTtoName pnt == name = Just pat
                          | otherwise = findName name fs
