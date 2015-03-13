
module RefacSwapArgs(swapArgs) where
import RefacUtils

swapArgs args  
 = do let fileName = ghead "filename" args       
          row      = read (args!!1)::Int        
          col      = read (args!!2)::Int        
      modInfo@(_,exps, mod, toks)<-parseSourceFile fileName  
      let pnt =locToPNT fileName (row, col) mod     
      if isFunPNT pnt mod   
       then do r<-applyRefac (doSwap pnt) (Just modInfo) fileName
               rs <-if isExported pnt exps 
                      then  applyRefacToClientMods (doSwap pnt) fileName
                      else  return []
               writeRefactoredFiles False (r:rs)      
       else error "\nInvalid cursor position!"  

-- Inside a single module.
doSwap pnt (_ , _, mod) = applyTP (full_buTP (idTP `adhocTP`  inMatch 
                                                   `adhocTP`  inExp
                                                   `adhocTP`  inDecl)) mod
  where 
    -- In the define site.
    inMatch ((HsMatch loc fun pats rhs ds)::HsMatchP)
      | fun == pnt   
      = case pats of    
         (p1:p2:ps) -> do  pats''<-update p2 p1 =<< update p1 p2 pats
                           return (HsMatch loc fun pats'' rhs ds)
         _          -> error "Insufficient arguments to swap." 
    inMatch m = return m  

    -- In the call-site.
    inExp exp@((Exp (HsApp (Exp (HsApp e e1)) e2))::HsExpP)
      | expToPNT e == pnt     
      = update e2 e1 =<< update e1 e2 exp     
    inExp e = return e 
 
    -- In the type signature,.
    inDecl (decl@(Dec (HsTypeSig loc is c tp))::HsDeclP)
      |isTypeSigOf pnt decl 
      = if length is ==1 
         then do let (t1:t2:ts)= tyFunToList tp 
                 update t2 t1 =<< update t1 t2 decl
         else error "This type signature defines the type of more than one identifiers."
    inDecl d = return d 

    tyFunToList (Typ (HsTyFun t1 t2)) = t1:(tyFunToList t2)
    tyFunToList t = [t]
 
