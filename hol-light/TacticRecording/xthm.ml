


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


type label =
   Tactical of finfo
 | Label of string;;


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

let dest_xthm ((th,info):xthm) : thm * finfo = (th,info);;

let xthm_thm ((th,_):xthm) = th;;

let xthm_proof ((_,info):xthm) = info;;



(* ** INSTALL PRINTERS ** *)


let print_xthm ((th,info):xthm) = print_thm th;;

#install_printer print_xthm;;

