-- $Id: SVCOps.hs,v 1.1 2001/07/19 22:36:04 wlh Exp $

module SVCOps (getHOLTyCon, getSVCOp) where

--- Now the first bit in "(tf, string)" means: is it an
--- *interpreted* function symbol? N.b., all operators are
--- prefix in SVC.
svcOps = [ ("True",  (True, "true")),
           ("False", (True, "false")),
           ("+",     (True, "+")), 
           ("*",     (True, "*")), 
           ("not",   (False, "not")),
           ("&&&",   (False, "and")),
           ("|||",   (False, "or")),
           ("==>",   (False, "=>")),
	   ("===",   (False, "="))
         ]

-- lookup n db = filter ((== n) . fst) db

getSVCOp :: String -> Maybe (Bool, String)
getSVCOp n = lookup n svcOps

--- Probably not needed for SVC:
getHOLTyCon :: String -> Maybe String
getHOLTyCon con = lookup con holTyCons

holTyCons = [ ("[]",  "list"),
              ("()",  "unit"),
              ("Int", "int"),
              ("Nat", "num")
            ]
