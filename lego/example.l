Module Walkthrough Import lib_logic;

Goal and_commutes: {A,B:Prop}(and A B) -> (and B A);
intros; andI;
Refine H; intros; Immed; Refine H; intros; Immed;
Save and_commutes;


