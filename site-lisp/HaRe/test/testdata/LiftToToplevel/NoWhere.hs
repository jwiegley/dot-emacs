module LiftToToplevel.NoWhere where

liftToTopLevel' modName pn = do
  renamed <- getRefactRenamed
  return []
    where
       {-step1: divide the module's top level declaration list into three parts:
         'parent' is the top level declaration containing the lifted declaration,
         'before' and `after` are those declarations before and after 'parent'.
         step2: get the declarations to be lifted from parent, bind it to liftedDecls 
         step3: remove the lifted declarations from parent and extra arguments may be introduce.
         step4. test whether there are any names need to be renamed.
       -}
       liftToMod = ['a'] -- do

getRefactRenamed :: IO String
getRefactRenamed = undefined
