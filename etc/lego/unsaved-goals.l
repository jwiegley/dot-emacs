(* 
  test case for closing off unsaved goals:
  P.G. should close Goal->Immed even though there
  is no Save.  Pred definition should not be
  part of closed region  
  (test with undoing and redoing) 
*)
   


Module unsaved Import lib_logic;

Goal {A,B:Prop}(and A B) -> (and B A);
intros;
Refine H;
intros;
andI;
Immed;

[Pred = [s:Type]s->Prop];

Goal {A,B:Prop}(and A B) -> (and B A);

