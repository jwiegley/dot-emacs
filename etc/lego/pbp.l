(* How to prove a sample theorem by PBP. *)

(* All using middle-clicks.
  
   1. Click on  ->        (Intros A B)
   2. Click on  -> again  (Intros H; Try Refine H)
   3. Click on A          (Intros H1; Try Refine H1)
   4. Click on B          (Intros H2; Try Refine H2)
   5. Click on A in A/\B  (Refine pair; Try Assumption)
   6. Click on final B    (Try Assumption)
   QED!!
*)

Module pbp Import lib_logic;

Goal {A,B:Prop}(A /\ B) -> (B /\ A);
Intros A B; 
Intros H; Try Refine H; 
Intros H1; Try Refine H1; 
Intros H2; Try Refine H2; 
Refine pair; Try Assumption; 
Try Assumption; 
Save and_comms;





