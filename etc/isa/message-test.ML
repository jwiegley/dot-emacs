(* Testing different kinds of markup in Isabelle output *)

(* ordinary output between prompts *)
print "ordinary";
print "ordinary\n";   (* final newline no difference *)

(* eager annotation: displayed as soon as it's seen *)
writeln "eager to be seen!";

print "more ordinary\n";

Goal "P-->P";

(* C-c RET to here should show eager annotation, as well as
   updating goals buffer properly. *)
error "something went wrong";  
