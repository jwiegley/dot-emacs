

module RefacCase(ifToCase) where

import RefacUtils 



ifToCase ::
  forall ds ext qn m1 b b1 b2 i1.
  (ReAssoc.HasInfixDecls Names.QName ds,
   ReAssoc.ReAssoc
     (SN HsName.HsName)
     (HsModuleI (SN HsName.ModuleName) (SN HsName.HsName) ds),
   QualNames qn m1 [Char],
   NameMaps.SeqNames
     (IxOutputM.OutputM
        ((NameMaps.Role (), TypedIds.NameSpace),
         PIdent,
         ScopeModule.Scope))
     b
     HsModuleP,
   NameMaps.MapNames
     ScopeModule.SPName
     b1
     (IxOutputM.OutputM ScopeModule.XRefInfo PNT)
     b,
   NameMaps.MapNames
     (SN i1)
     (HsModuleI (SN HsName.ModuleName) Names.QName ds)
     (PN i1)
     b2,
   DefinedNames.DefinedNames (SN qn) ds,
   ScopeNames.ScopeNames
     (PN HsName.HsName)
     (FiniteMap1.FiniteMap
        (HsIdentI HsName.HsName)
        [(HsIdentI (PN HsName.HsName), IdTy (PN [Char]))])
     b2
     b1) =>
  [String]
  -> IxStateMT.WithState
       (PFE0.PFE0State
          (SN [Char]) Names.QName ds (PFE2.PFE2Info (SN [Char]), ext))
       IO
       ()

ifToCase args  
  = do let fileName = args!!0              
           beginPos = (read (args!!1), read (args!!2))::(Int,Int)
           endPos   = (read (args!!3), read (args!!4))::(Int,Int)
       modInfo@(_, _, mod, toks) <- parseSourceFile fileName 
       let exp = locToExp beginPos endPos toks mod
       case exp of 
           (Exp (HsIf _ _ _))   
                -> do refactoredMod <- applyRefac (ifToCase exp) (Just modInfo) fileName          
                      writeRefactoredFiles False [refactoredMod]
           _   -> error "You haven't selected an if-then-else  expression!"
    where 

     ifToCase exp (_, _, mod)= applyTP (once_buTP (failTP `adhocTP` inExp)) mod
       where 
         inExp exp1@((Exp (HsIf  e e1 e2))::HsExpP)
           | sameOccurrence exp exp1       
           = let newExp =Exp (HsCase e [HsAlt loc0 (nameToPat "True") (HsBody e1) [],
                                        HsAlt loc0 (nameToPat "False")(HsBody e2) []])
             in update exp1 newExp exp1
         inExp _ = mzero

                           



