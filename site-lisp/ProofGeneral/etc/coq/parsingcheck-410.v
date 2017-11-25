Require Export Coq.Lists.List. 
Notation "[ ]" := nil : list_scope. 
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.
