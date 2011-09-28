(* Testing samples for MMM *)

header {* This is edited in LaTeX mode *}

theory MMMtests imports Main begin

text {*
  This is a test of MMM support.
  This region is edited in \LaTeX{} mode.
*}

subsection {* and this one. *}


ML {*
  (* Whereas this region is edited in SML mode.  For that to work, you
  need to have installed SML mode in your Emacs, otherwise MMM mode
  won't bother.  See Stefan Monnier's page at
  http://www.iro.umontreal.ca/~monnier/elisp/. *)
  
  fun foo [] = 0
    | foo (x::xs) = x * foo xs
*}

ML_val {* (* and this one *) *}

ML_command {* (* and this one *) *}

print_translation {* [] (* and even this one *) *}

text {* 
  You can enter the text for a MMM region conveniently 
  using the dedicated insertion commands. For example, I inserted
  this region by typing \texttt{C-c \% t}  --- see the MMM menu or
  \texttt{C-c \% h}  for a list of commands.  

  Notice that font locking for different modes tends to interact
  badly with mode switches between lines.  Best stick to
  separate lines as in these examples.
*}
