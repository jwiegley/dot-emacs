-- Generate selector functions for data constructors with labelled fields
module FieldSelectors where
import Data.List(nub)
import HsDeclStruct
import HasBaseStruct(hsPApp,hsPVar,hsPWildCard,hsEVar,hsFunBind)
import HsGuardsStruct(HsRhs(..))
import TiNames(localVal')

{-+
Haskell 98 Report, section 3.15.1 Field Selection
-}
fieldSelectors noDef cds = map selector fields 
  where
    conFields = nub [((src,c),[n|(ns,_)<-fs,n<-ns])|HsRecDecl src _ _ c fs<-cds]
    fields = nub [(src,n)|((src,_),ns)<-conFields,n<-ns]

    selector (src,field) =
       hsFunBind src
         [HsMatch src field [hsPApp c (map pat fs)]
                            (HsBody (hsEVar x)) noDef
            |((src,c),fs)<-conFields,field `elem` fs]
      where
        x = localVal' "x" (Just src)
        pat f = if f==field
		then hsPVar x
		else hsPWildCard
