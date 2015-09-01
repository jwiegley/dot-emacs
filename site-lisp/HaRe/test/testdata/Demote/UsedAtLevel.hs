{-# LANGUAGE ScopedTypeVariables #-}
module Demote.UsedAtLevel where

foo :: IO ()
foo = do
  let xx = uses declaredPns []
  return ()
    where
          ---find how many matches/pattern bindings use  'pn'-------
          -- uses :: [GHC.Name] -> [GHC.LHsBind GHC.Name] -> [Int]
          uses pns t2
               = concatMap used t2
                where

                  used :: LHsBind Name -> [Int]
                  used (L _ (FunBind _n _ (MatchGroup matches _) _ _ _))
                     = usedInMatch pns matches

          usedInMatch _ _ = []


data HsBind a = FunBind a Int (MatchGroup a) Int Int Int
               | PatBind String String Int Int a
data Name = N String
data Located a = L Int a
data MatchGroup a = MatchGroup [LMatch a] a
type LMatch a = Located (Match a)
data Match a = Match String Int a
data Renamer = Renamer
type LHsBind a = Located (HsBind a)
declaredPns = undefined
