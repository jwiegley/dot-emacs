

module RefacDeForest(deforest) where

import PrettyPrint
import PosSyntax hiding(moduleName)
import Data.Maybe
import TypedIds
import ScopeModule
import UniqueNames hiding (srcLoc)
import PNT 
import TiPNT 
import PFE0
import Data.List  
import RefacUtils
import AbstractIO
import Prelude hiding(putStrLn,putStr)

-- this refactoring trys to eliminate intermeidate list.
deforest args
 = do let fileName= ghead "filename" args     
      modName <- fileNameToModName fileName 
      (inscps, exps, mod, tokList) <- parseSourceFile fileName
      let (newDecs,oldPNs,newPNs) = unzip3( head(getHsMatch mod) )   	
      (mod',((tokList',m),_)) <- doFuseCurrent mod tokList newDecs oldPNs newPNs fileName        
      clients<-clientModsAndFiles modName  
      let (clientsMod,clientFiles)= unzip clients         
      refactoredClients <- mapM (doFuseInClient tokList newDecs oldPNs newPNs ) clients
      writeRefactoredFiles False $ ((fileName,m),(tokList',mod')):refactoredClients

  where
	
    simpDec mod = fromJust ( applyTP ( full_tdTP ( idTP `adhocTP` simplifyDecl) ) mod)

    fil x mod = filter notInUsed x where
		notInUsed:: HsDeclP -> Bool
		notInUsed t = not (isDeclaredIn (getPN t) mod )


    getHsMatch  m = applyTU (full_tdTU (constTU [] `adhocTU`  special ) ) m where
		    special x = do  p <- simplifyDecl x
				    convertDec p 
		    simpDec m = applyTP (full_tdTP (idTP `adhocTP` simplifyDecl) ) m
	

    doFuseInClient tokList newDecs oldPNs newPNs (modName,fileName)
      = do (inscps, exps, mod, tokList) <- parseSourceFile fileName
  	   (mod',((tokList',m),_)) <- doFuseClient mod tokList newDecs oldPNs newPNs fileName 
	   return ( (fileName,True),(tokList',mod'))

    doFuseCurrent  mod tokList  newDecs oldPNs newPNs fileName 
      =runStateT (fus mod) (( tokList,unmodified), (-1000, 0)) where
	fus mod =do mod' <- addDecl mod Nothing (fil newDecs mod , Nothing )True 
		    replaceFold mod' oldPNs newPNs  
			
			--replace all :  foldr f n (fb) -> fb_workder f n 


    doFuseClient  mod tokList  newDecs oldPNs newPNs  fileName
	= runStateT ( replaceFold mod  oldPNs newPNs  )  (( tokList,unmodified), (-1000, 0))


    replaceFold mod  oldPNs newPNs 
       = applyTP ( full_tdTP (idTP `adhocTP` convertFold) ) mod 
      where
	convertFold  a@(Exp(HsApp(Exp(HsApp (Exp(HsApp fol f )) n ) ) exp  ) ) 
	  | (isFunc fol "foldr") && (findPNs  oldPNs (strip exp) ) -- can be fused
	   = do newExp <-  melt exp p newP f n
		update a newExp a 
	  | otherwise = return a
           where
	     p = getPNFromExp (strip(exp))
	     newP = newPNs !!  ( fromJust ( elemIndex p oldPNs))

	     convertFold a = return a

	     melt exp pn newPn f n = ( applyTP (full_tdTP (idTP `adhocTP` changeF)) exp)
               where
		changeF exp@(Exp(HsId(HsVar(PNT pName a b ) ) )) 
		   | (pName== pn)= return (Exp(HsApp (Exp(HsApp (Exp(HsId(HsVar(PNT newPn a b)))) f )) n ))
	   	   | otherwise = return exp
		changeF exp = return exp
	     

    getCataFun = applyTU (full_tdTU ( constTU[] `adhocTU` recToCata) ) 	


strip (Exp(HsApp exp1 exp2 ) ) = strip exp1
strip a@(Exp(_)) = a
                        

build [] = nameToExp "n"
build (x:xs) = Exp(HsApp (Exp(HsApp (nameToExp "c") x))  (build xs) )

--get PN from a Decl 
getPN ( Dec(HsFunBind t ( (HsMatch src (PNT pn _ _) pat body loc):xs))) = pn 


colListCons :: HsIdentI PNT -> [ [HsIdentI PNT]]
colListCons x = if (isListCons x) then  return [x] else return []

-- takes an Exp and return itself if it is an (:) list constructor 
isListCons  (HsCon (PNT (PN (UnQual ":") (G (PlainModule "Prelude") ":"_ )) _ _))    = True
isListCons _ = False


--check if this Exp has a fun call `name` 
isFunc f@(Exp (HsId (HsVar (PNT (PN (UnQual fName) _) _  _)))) name = (fName == name)
isFunc _ _= False



bodyHasCons (HsBody(e)) =  expHasCons e


expHasCons (Exp (HsInfixApp _ cons _ )) =  isListCons cons
expHasCons (Exp ( HsApp (Exp(HsApp (Exp(HsId(cons)))  exp1 )) exp2   ) ) = isListCons cons
expHasCons (Exp(HsList _)) = True
expHasCons _ = False



modBody (HsBody e) = (HsBody (modExp e))

modExp  (Exp (HsInfixApp exp1 cons exp2)) = (addWrapper exp1 exp2)
modExp  (Exp ( HsApp (Exp(HsApp cons  exp1)) exp2 ) ) = (addWrapper exp1 exp2)
modExp  (Exp(HsList x )) = build x
modExp a = a


addWrapper exp1 exp2 = Exp (HsApp (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "c") (S loc0)) Value (N (Just loc0)))))) (  exp1  ))) (exp2  ))


getPnFromPNT (PNT pn _ _ ) = pn

getPNFromExp exp =  ( fromJust $ applyTU ( once_tdTU ( failTU `adhocTU` idPN) ) exp) where
    idPN :: PName -> Maybe PName
    idPN a = Just a


--convertDec takes a Dec check if we can convert it into cata form if not simply return itself
--convertDec :: HsDeclP ->  [ [ (HsDeclP,HsName,HsName) ] ] 

convertDec d@( Dec(HsFunBind t [m@(HsMatch src pnt pat body loc)]))= 
	if isFormed body then return [ ( (Dec (HsFunBind t [convertMatch m] ) ), getPnFromPNT pnt, getPnFromPNT $ change pnt)]
	else return []  where
		isFormed ((HsBody (Exp (HsCase exp1 alt) ))) = checkAltL alt where
			checkAltL [] = True
			checkAltL (x:xs) = (checkAlt x) && (checkAltL xs) where
				checkAlt (HsAlt src p bo d) = bodyHasCons bo
			
		 
		isFormed ((HsBody(e@(Exp( HsIf e1 e2 e3) ) ))) = checkIfExp e where
			checkIfExp (Exp(HsIf e1 e2 e3 )) = expHasCons e2  && checkIfExp e3
			checkIfExp e = expHasCons e
			--checkIfExp _ = True

			
		isFormed _ = False
	
		-- add "_worker" to the function name in PNT
		change p@(PNT ( PN (UnQual f) (G v1 f1 v2 ) )v3  pat )    = PNT (PN(UnQual (f++"_worker")) (G v1  (f++"_worker") v2 )) v3 pat   
		change p = p

		convertMatch (HsMatch src pnt pat body loc) = HsMatch src (change pnt) ([nameToPat "c",nameToPat "n"] ++ pat) (convertBody body) loc	where
			
			convertBody (HsBody(Exp (HsCase exp alt))) = (HsBody(Exp(HsCase exp (convertAlt alt))))
			convertBody (HsBody(Exp (HsIf e1 e2 e3))) = (HsBody(Exp( HsIf e1 e2' e3'))) where
				e2' = modIfExp e2 
				e3' = modIfExp e3 
				modIfExp (Exp(HsIf a1 a2 a3 )) = (Exp(HsIf a1 (changeFToF (modExp a2) pnt) (modIfExp a3) ))
				modIfExp e = changeFToF (modExp e) pnt




			convertAlt [] = []
			convertAlt (x :xs) = (con x) : (convertAlt xs)
			con (HsAlt src p bo d ) = changeFToF (HsAlt src p (modBody bo)d) pnt


			changeFToF m  p = fromJust $ (applyTP( full_tdTP ( idTP `adhocTP` changeFToF# ) )) m where
			    changeFToF# :: HsExpP -> Maybe  HsExpP
			    changeFToF# e@(Exp(HsId(HsVar pnt))) = if (p==pnt) then  
								return ( Exp(HsApp (Exp(HsApp (Exp(HsId(HsVar (change pnt)))) (nameToExp "c"))) (nameToExp "n") ))
								 else return e
			    changeFToF# a = Just a

			
		
convertDec d = return [] 


-- from recursion to cataformlism

recToCata :: HsDeclP -> [[HsDeclP]]
recToCata d@( Dec(HsFunBind t [m@(HsMatch src pnt pat body loc)])) = if (check body) then return [d] else return [] where
	check b@(HsBody (Exp (HsCase exp1 alt) )) = checkAlt alt
	check _ = False
	checkAlt [ (HsAlt src1 (Pat (HsPTuple _ p1)) bo1 d1), (HsAlt src2 (Pat (HsPTuple _ p2)) bo2 d2) ] = doCheck p1 p2
	checkAlt _ = False  
	doCheck p1 p2 = (match ==1 )where
		match = count p1 p2
		count (x:xs) (y:ys)= if (eq x y) then 0 + count xs ys
                                     else if (isEmptyPList x && isConsPat y) || 
                                                (isConsPat x && isEmptyPList y) then count xs ys + 1
				     else 2 + count xs ys
		count _  _ = 0
		isConsPat (Pat (HsPParen (Pat (HsPInfixApp a cons b)))) = isListPNT cons
		isConsPat _ = False

                
                -- takes an Exp and return itself if it is an (:) list constructor 
                isListPNT  (PNT (PN (UnQual ":") (G (PlainModule "Prelude") ":"_ )) _ _) = True
                isListPNT  _ = False

                isEmptyPList (Pat (HsPList _ [])) = True
                isEmptyPList _ = False 
		
		eq (Pat (HsPId (HsVar (PNT (PN pn1 _)  _ _))))   (Pat (HsPId (HsVar (PNT (PN pn2 _)  _ _)))) = pn2==pn1
		eq _ _ = False
					 
								   
recToCata _ = return []

