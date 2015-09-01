-- $Id: Main.hs,v 1.1 2001/03/19 17:55:45 moran Exp $

module Main where

import Syntax
import Translate


nil = ExpId (Var "nil")
appendNil = ExpEval $
	    App (ExpEval $ App (ExpId (Var "append"))
		               (ExpId (Var "xs")))
                nil
	        

appendNilUnit = Prop $ All (Var "xs") (Prop (appendNil `Equiv` nil))

main = print $ translateProp [] [] appendNilUnit