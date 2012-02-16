


(* ** DATATYPES ** *)


type farg =
   Fint of int
 | Fstring of string
 | Fterm of term
 | Ftype of hol_type
 | Fthm of finfo
 | Fpair of farg * farg
 | Flist of farg list
 | Ffn of finfo

and finfo =
   string option                     (* Function's name *)
 * farg list;;                       (* Function's args *)


(* finfo_as_meta_arg *)

let finfo_as_meta_arg (info:finfo) =
  match info with
    (x_, ((_::_) as args))
       -> Ffn (x_, front args)
  | _  -> failwith "finfo_as_meta_arg: Unexpected empty rule arg list";;


(* Atomic tests *)

let is_atomic_farg arg =
  match arg with
    Fthm (_,(_::_)) | Fpair _ -> false
  | _ -> true;;

let is_atomic_finfo ((x_,args):finfo) = (is_empty args);;


(* active_info *)

let active_info = (Some "...", []);;


(* The 'xthm' datatype *)

(* This couples a theorem with an 'finfo' representation of its proof.  For   *)
(* named ML objects, this 'finfo' will simply be the ML name of the theorem.  *)
(* For rule applications, it will capture the rule and its arguments.         *)

type xthm = thm * finfo;;

type xconv = term -> xthm;;


(* Constructors and destructors *)

let mk_xthm (xth:thm*finfo) : xthm = xth;;

let mk_xthm0 x th = mk_xthm (th, (Some x, []));;

let dest_xthm ((th,x):xthm) : thm * finfo = (th,x);;

let xthm_thm ((th,_):xthm) = th;;

let xthm_proof ((_,prf):xthm) = prf;;



(* ** WRAPPER FUNCTIONS ** *)


(* Theorem wrapper *)

let theorem_wrap (x:string) (th:thm) : xthm =
  (th, (Some x, []));;


(* Rule wrappers *)

(* Lots of rule wrappers are required because there are many different type   *)
(* shapes for rules.                                                          *)

let rule_wrap0 finfo (r:'a->thm) (arg:'a) : xthm =
  let th' = r arg in
  mk_xthm (th',finfo);;

let conv_wrap x (r:term->thm) (tm:term) : xthm =
  rule_wrap0 (Some x, [Fterm tm]) r tm;;

let thm_conv_wrap x (r:thm->term->thm) (thx:xthm) tm : xthm =
  let (th,prf) = dest_xthm thx in
  rule_wrap0 (Some x, [Fthm prf; Fterm tm]) (r th) tm;;

let thmlist_conv_wrap x (r:thm list->term->thm) thxs (tm:term) : xthm =
  let (ths,prfs) = unzip (map dest_xthm thxs) in
  rule_wrap0 (Some x, [Flist (map (fun prf -> Fthm prf) prfs); Fterm tm])
             (r ths) tm;;

let rule_wrap x (r:thm->thm) (thx:xthm) : xthm =
  let (th,prf) = dest_xthm thx in
  rule_wrap0 (Some x, [Fthm prf]) r th;;

let drule_wrap x (r:thm->thm->thm) (thx1:xthm) (thx2:xthm) : xthm =
  let (th1,prf1) = dest_xthm thx1 in
  let (th2,prf2) = dest_xthm thx2 in
  rule_wrap0 (Some x, [Fthm prf1; Fthm prf2]) (r th1) th2;;

let prule_wrap x (r:thm*thm->thm) ((thx1:xthm),(thx2:xthm)) : xthm =
  let (th1,prf1) = dest_xthm thx1 in
  let (th2,prf2) = dest_xthm thx2 in
  rule_wrap0 (Some x, [Fpair(Fthm prf1, Fthm prf2)]) r (th1,th2);;

let trule_wrap x (r:thm->thm->thm->thm)
                 (thx1:xthm) (thx2:xthm) (thx3:xthm) : xthm =
  let (th1,prf1) = dest_xthm thx1 in
  let (th2,prf2) = dest_xthm thx2 in
  let (th3,prf3) = dest_xthm thx3 in
  rule_wrap0 (Some x, [Fthm prf1; Fthm prf2; Fthm prf3]) (r th1 th2) th3;;

let term_rule_wrap x (r:term->thm->thm) tm (thx:xthm) : xthm =
  let (th,prf) = dest_xthm thx in
  rule_wrap0 (Some x, [Fterm tm; Fthm prf]) (r tm) th;;

let termpair_rule_wrap x (r:term*term->thm->thm) (tm1,tm2) (thx:xthm) : xthm =
  let (th,prf) = dest_xthm thx in
  rule_wrap0 (Some x, [Fpair(Fterm tm1,Fterm tm2); Fthm prf]) (r (tm1,tm2)) th;;

let termthmpair_rule_wrap x (r:term*thm->thm->thm) (tm,thx0) (thx:xthm) : xthm =
  let (th0,prf0) = dest_xthm thx0 in
  let (th,prf) = dest_xthm thx in
  rule_wrap0 (Some x, [Fpair(Fterm tm, Fthm prf0); Fthm prf]) (r (tm,th0)) th;;

let termlist_rule_wrap x (r:term list->thm->thm) tms (thx:xthm) : xthm =
  let (th,prf) = dest_xthm thx in
  rule_wrap0 (Some x, [Flist (map (fun tm -> Fterm tm) tms); Fthm prf])
             (r tms) th;;

let terminst_rule_wrap x (r:(term*term)list->thm->thm) theta (thx:xthm) : xthm =
  let (th,prf) = dest_xthm thx in
  rule_wrap0 (Some x,
              [Flist (map (fun (tm1,tm2) -> Fpair(Fterm tm1, Fterm tm2)) theta);
               Fthm prf])
             (r theta) th;;

let typeinst_rule_wrap x (r:(hol_type*hol_type)list->thm->thm)
                         theta (thx:xthm) : xthm =
  let (th,prf) = dest_xthm thx in
  rule_wrap0 (Some x,
              [Flist (map (fun (tm1,tm2) -> Fpair(Ftype tm1, Ftype tm2)) theta);
               Fthm prf])
             (r theta) th;;

let thmlist_rule_wrap x (r:thm list->thm->thm) thxs (thx:xthm) : xthm =
  let (ths,prfs) = unzip (map dest_xthm thxs) in
  let (th,prf) = dest_xthm thx in
  rule_wrap0 (Some x, [Flist (map (fun prf -> Fthm prf) prfs); Fthm prf])
             (r ths) th;;


(* Meta rule wrappers *)

(* This works by ... *)
(* Fails to give a meta argument if it never gets executed.                   *)

let meta_rule_wrap0 finfo0 (mr:('a->thm)->'b->thm)
                           (xr:'a->xthm) (arg:'b) : xthm =
  let temp = ref ((Some "???", []) : finfo) in
  let r arg0 = let thx = xr arg0 in
               let (th,finfo) = dest_xthm thx in
               ((match finfo with
                   (x_, (_::_ as args))
                      -> (temp := (x_, front args))
                 | _  -> ());
                th) in
  let th' = mr r arg in
  let (x_,args0) = finfo0 in
  let finfo' = (x_, (Ffn !temp)::args0) in
  (th',finfo');;

let conv_conv_wrap x (mc:conv->conv) (c:term->xthm) (tm:term) : xthm =
  meta_rule_wrap0 (Some x, [Fterm tm]) mc c tm;;



(* ** INSTALL PRINTERS ** *)


let print_xthm ((th,info):xthm) = print_thm th;;

#install_printer print_xthm;;

