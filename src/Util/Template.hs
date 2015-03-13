module Util.Template ( substs
                     ) where

import Data.List (isPrefixOf)

-- Simple templating system
-- most of the existing tools are either too complicated
-- or use $ (or even ${}) chars for variables, which is unfortunate
-- for use with [ba]sh templates.

type Substitution = (String, String)

-- substitute all  occurences of FROM to TO
subst :: Substitution -> String -> String
subst _ [] = []
subst phi@(from, to) input@(x:xs)
    | from `isPrefixOf` input = to ++ subst phi (drop (length from) input)
    | otherwise               = x:subst phi xs

-- multi version of subst
substs :: [Substitution] -> String -> String
substs phis str = foldr subst str phis
