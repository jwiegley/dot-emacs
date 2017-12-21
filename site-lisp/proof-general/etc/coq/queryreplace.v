(* STATUS: Solved.  This was caused by the anyway faulty
   proof-zap-commas-region failing to save the match data.
   See comments in proof-syntax.el about that function.
*)

(*
From: 	Cuihtlauac ALVARADO <cuihtlauac.alvarado@francetelecom.com>
To: 	David Aspinall <da@dcs.ed.ac.uk>
Subject: 	broken query-replace
Date: 	09 Jul 2002 11:09:03 +0200	

BTW, there's something stange I've forgot to post.

In FSF-emacs PG & global-font-lock-mode does not play well together. Add 

(global-font-lock-mode t)

in your .emacs an then try to query-replace "dom" by "foo" in

*)

Record t : Type := make {
  dom : Set;
  null : dom;
  inv : dom->dom;
  op : dom->dom->dom;
  null_l : (x:dom)x=(op null x);
  null_r : (x:dom)x=(op x null);
  inv_l : (x:dom)null=(op (inv x) x);
  inv_r : (x:dom)null=(op x (inv x));
  assoc : (x,y,z:dom)(op x (op y z))=(op (op x y) z);
  inv_null : null=(inv null);
  inv_inv : (x:dom)x=(inv (inv x));
  assoc_inv_l : (x,y:dom)y=(op (inv x) (op x y));
  assoc_inv_r : (x,y:dom)y=(op x (op (inv x) y));
  inv_op : (x,y:dom)(op (inv y) (inv x))=(inv (op x y))
 }.


(*

assoc, assoc_inv_l, assoc_inv_r and inv_op occurences of "dom" are
replaced by "fooom" instead of "dom", quite strange is'n it ?

Query-replacing "dom" by "bar" leads to "barom", which make me thinks
only the first letter of the pattern is replaced...

I've seen this strange behaviour for a while, it was present in
earlier versions of PG & emacs.
 
*)
