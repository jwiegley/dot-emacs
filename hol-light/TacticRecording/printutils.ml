(* ========================================================================== *)
(* PRINTER UTILITIES (HOL LIGHT)                                              *)
(* - Various basic utilities used in writing the exporters                    *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Univeristy of Edinburgh, 2012                                *)
(* ========================================================================== *)


(* Basics *)

let print_string_if b x = if b then print_string x;;

let print_fstring x = print_string ("\"" ^ String.escaped x ^ "\"");;

let print_fterm tm = print_string ("`" ^ string_of_term tm ^ "`");;

let print_ftype ty = print_string ("`" ^ string_of_type ty ^ "`");;

let print_goalid id = print_int id;;

let print_indent d = print_string (String.make d ' ');;


(* Printer for 'finfo' *)

let rec print_farg x0 br arg =
  match arg with
    Fint n       -> print_int n
  | Fstring x    -> print_fstring x
  | Fterm tm     -> print_fterm tm
  | Ftype ty     -> print_ftype ty
  | Fthm prf     -> print_finfo "<rule>" br prf
  | Fpair (arg1,arg2)
       -> let sep = if (forall is_atomic_farg [arg1;arg2]) then "," else ", " in
          (print_string_if br "(";
           print_farg x0 false arg1;
           print_string sep;
           print_farg x0 false arg2;
           print_string_if br ")")
  | Flist args 
       -> let sep = if (forall is_atomic_farg args) then ";" else "; " in
          (print_string "[";
           print_seplist (print_farg x0 false) sep args;
           print_string "]")
  | Ffn f
       -> (print_finfo x0 br f)

and print_finfo x0 br ((x_,args):finfo) =
  (print_string_if (br & not (is_empty args)) "(";
   print_option x0 x_;
   do_list (fun arg -> print_string " "; print_farg x0 true arg) args;
   print_string_if (br & not (is_empty args)) ")");;


(* Printer for labels *)

let print_label l =
  match l with
    Tactical (Some x, _) | Label x  -> print_fstring x
  | Tactical (None, _)              -> print_fstring "<tactical>";;
