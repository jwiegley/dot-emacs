(* 
  Some test cases for closing off unsaved goals, 
  and the setting proof-completed-proof-behaviour.

  David Aspinall, November 1999.

  Things work fairly well in lego with 

       proof-completed-proof-behaviour='closeany

  In that case, undoing/redoing later declarations 
  (E and F) following the completed proof works okay, and
  in the absence of declarations, things work fine.
    
  Declarations in LEGO are global, and forgetting a
  declaration when a proof is still open (even if complete)
  aborts the proof!  So a proper handling would need to
  trigger a *further* retraction when the "Forget D" is
  issued undoing the definition of D.  Never mind.

  With proof-completed-proof-behaviour='closegoal or 'extend,
  undoing the first goal doesn't forget the declarations.

  This file even causes internal errors in LEGO!

     Warning: forgetting a finished proof

     LEGO detects unexpected exception named "InfixInternal"

  Test with undoing and redoing, and various settings
  for proof-completed-proof-behaviour
*)
   


Module unsaved Import lib_logic;

Goal {A,B:Prop}(and A B) -> (and B A);
intros;
Refine H;
intros;
andI;
Immed;
[D = Type];
[E = Type];
[F = Type];

Goal {A,B:Prop}(and A B) -> (and B A);
intros;
Refine H;
intros;
andI;
Immed;

