(* How to prove a sample theorem by PBP. *)

(* All using middle-clicks.
  
   1. Click on  ->          (Pbp 0 3 1: Intros A B)
   2. Click on left (A/\B)  (Pbp 1 2 1: Intros H; Try Refine H)
   3. Click on A            (Pbp 4 2 1: Intros H1; Try Refine H1)
   4. Click on B            (Pbp 5 2 1: Intros H2; Try Refine H2)
   5. Click on A in A/\B    (Pbp 6 2 1: Refine pair; Try Assumption)
   6. Click on final B      (Pbp 10:    Try Assumption)
      OR:
      Click on assumption B (PbpHyp H2: Try Refine H2)
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





