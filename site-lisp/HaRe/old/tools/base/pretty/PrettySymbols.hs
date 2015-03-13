module PrettySymbols where
import PrettyPrint

kwIfUnicode a u = kw (ppIfUnicode a u)

-- Smileys and other useful symbols:
happy   = kwIfUnicode '\x263a' ":-)"
sad     = kwIfUnicode '\x2639' ":-("
forall' = kwIfUnicode '\x2200' "forall"
all     = kwIfUnicode '\x2200' "All"
exist   = kwIfUnicode '\x2203' "Exist"
--el      = kwIfUnicode '\x220a' "::" -- looks ugly in times
el      = kwIfUnicode '\x2208' "::"
imp     = kwIfUnicode '\x21d2' "=>"
lambda  = kwIfUnicode '\x03bb' "\\"
larrow  = kwIfUnicode '\x2190' "<-"
rarrow  = kwIfUnicode '\x2192' "->"
and     = kwIfUnicode '\x2227' "/\\"
or      = kwIfUnicode '\x2228' "\\/"
not     = kwIfUnicode '\x00ac' "-/"
implies = kwIfUnicode '\x21d2' "==>"
equiv   = kwIfUnicode '\x21d4' "<==>"
mu      = kwIfUnicode '\x03bc' "Lfp"
nu      = kwIfUnicode '\x03bd' "Gfp"
--star    = kwIfUnicode '\x2605' "*" -- not present in times
--moon    = kwIfUnicode '\x263e' "C" -- not present in times
star    = kw "*"
moon    = kw "C"
