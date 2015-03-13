-- $Id: HOLOps.hs,v 1.3 2001/07/19 22:17:37 wlh Exp $

module HOLOps (getHOLTyCon, getHOLOp) where

holOps = [ ("===",   (True, "=")),
           ("==>",   (True, "==>")),
           ("&&&",   (True, "/\\")),
           ("|||",   (True, "\\/")),
           (".",     (True, "o")),
           ("==",    (True, "=")),
           ("$",     (False, "(\\ f . \\ x . f x)")),
           ("True",  (False, "true")),
           ("False", (False, "false"))
         ]

holTyCons = [ ("[]",  "list"),
              ("()",  "unit"),
              ("Int", "int"),
              ("Nat", "num")
            ]

-- lookup n db = filter ((== n) . fst) db

getHOLTyCon :: String -> Maybe String
getHOLTyCon con = lookup con holTyCons

getHOLOp :: String -> Maybe (Bool, String)
getHOLOp n = lookup n holOps
