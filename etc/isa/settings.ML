(* 
   Simple test for variable setting mechanism ML -> PG. 
   This kind of protocol is included in PGIP for setting config variables.
   Here we can use it for executing arbitrary elisp, in fact (eek!)
*)

fun pg_setvar var exp = writeln ("Proof General, please set the variable " ^ var ^ " to: #" ^ exp ^ "#.");

pg_setvar "wag" "(+ 33 44)";   (* C-h v wag RET gives 77 *)

fun pgset var = pg_setvar var "t";
fun pgreset var = pg_setvar var "nil";

pgset "isa-show-types";    (* sets show-types in menu *)

(* What might be nice is to override 'set' 'reset' fuctions to mirror
   settings in PG automatically, but then we'd need to retrieve the
   names of the ML values from the 'set' and 'reset' functions... *)

(* test failure case: prints a debug message if proof-show-debug-messages<>nil *)
pg_setvar "wig" "blah 12 x12"
