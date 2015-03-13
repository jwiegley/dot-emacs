module RegExpOps where
import RegExp
import List

{-+
"" =~ r <==> nullable r
-}
nullable r =
  case r of
    Zero -> False
    One -> True
    S _ -> False
    r1 :& r2  -> nullable r1 && nullable r2
    r1 :! r2  -> nullable r1 || nullable r2
    r1 :-! r2 -> nullable r1 && not (nullable r2)
    Many re -> True
    Some re -> nullable re

--nullR r = if nullable r then e else z

{-+
For all i in first r, there exists an is such that i:is =~ r
-}
first r =
  case r of
    Zero -> []
    One -> []
    S i -> [i]
    r1 :& r2  -> first r1 `union` (if nullable r1 then first r2 else [])
    r1 :! r2  -> first r1 `union` first r2
--  r1 :-! r2 -> first r1 \\ first r2         -- this is wrong!
    r1 :-! r2 -> first r1 -- `union` first r2
    Many re -> first re
    Some re -> first re

{-+
i:is =~ r <==> is =~ follow i r
-}
follow i r =
  case r of
    Zero -> Zero
    One -> Zero
    S i' -> if i'==i then One else Zero
    r1 :& r2  -> follow i r1 & r2 ! (if nullable r1 then follow i r2 else Zero) 
    r1 :! r2  -> follow i r1 ! follow i r2
    r1 :-! r2 -> follow i r1 -! follow i r2
    Many re -> follow i re & Many re
    Some re ->  follow i re & Many re

factors r = (nullable r,[(i,r')|i<-sort (first r),let r'=follow i r,r'/=Zero])

factorsR (n,fs) = (if n then e else z) ! alts [S i & r|(i,r)<-fs]


{-+
Inspired by:

comp.compilers, comp.theory
http://compilers.iecc.com/comparch/article/93-10-022

The Equational Approach: (1) Regular Expressions -> DFA's.
markh@csd4.csd.uwm.edu (Mark)
Computing Services Division, University of Wisconsin - Milwaukee
Sat, 2 Oct 1993 17:47:13 GMT
-}
