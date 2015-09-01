module HS2Hol where

import Syntax
import PrettyPrint

import Observe


data2hol :: HsDecl -> Doc
data2hol (Dec (HsDataDecl srcloc _ ((Typ (HsTyCon name)):params) cons _))  
    = comment $$ holDatatype $$ nest 4 holCons $$ text "`;"
    where
    comment     = text "(* From" <+> text (show srcloc) <+> text ": *)"
    holDatatype = text "val _ = Hol_datatype `" 
                    <+> text (show name) 
    holCons     = text "=" <+> (foldr1 (\d d' -> d $$ text "|" <+> d') $
                    map (hsConDecl2holConDecl [name]) cons)

data2hol _ = error"data2hol: only wokrs on HsDataDecl"


hsConDecl2holConDecl :: [HsName] -> HsConDecl HsType  -> Doc 
hsConDecl2holConDecl excl (HsConDecl _ name params)
    = hsName2hol name <+> ps
    where
    ps = case params of
        []  -> empty
        xs  -> text "of" <+> (hsep $ punctuate (text " =>") $
                                map (hsType2hol excl . hsBangType2Type) xs)

hsConDecl2holConDecl _ _  = error "hsConDecl2holConDecl: records not implemented"


-- the list of names specifies constructors,
-- which should not be applied to arguments
-- even if they have any.  this is useful in Hol_datatype
-- definitions, where one cannot specify aruments to
-- whatever is currently being defined
hsType2hol :: [HsName] -> HsType -> Doc 
hsType2hol excl (Typ typ)
    = case typ of
        HsTyVar name    -> text "'" <> hsName2hol name
        HsTyCon name    -> hsName2hol name
        HsTyApp t1@(Typ (HsTyCon n)) t2
            | n `elem` excl -> hsType2hol excl t1
            | otherwise     -> parens (hsType2hol excl t2) <+>
                               hsType2hol excl t1
        HsTyTuple ts    -> hsep $ punctuate (text "#") $
                            map (hsType2hol excl) ts
        HsTyForall n t  -> hsType2hol excl t




hsName2hol :: HsName -> Doc 
hsName2hol (UnQual s)   = text s 
hsName2hol _            = error "hsName2hol: only unqualified names work"

hsBangType2Type :: HsBangType t -> t
hsBangType2Type (HsUnBangedType t)  = t
hsBangType2Type  _ = error "hsBangType2Type: only unbaged types work"



--------------------------------------------------------------------------------
-- tests
--

n = UnQual 
loc = SrcLoc "MyFile" 1 1

t1 :: HsDecl
t1 = hsDataDecl loc []
        {-data-} [hsTyCon $ n "List", hsTyVar $ n "a"]
        [ HsConDecl loc (n "Nil") []
        , HsConDecl loc (n "Cons")
            [ HsUnBangedType (hsTyVar $ n "a")
            , HsUnBangedType (hsTyApp (hsTyCon $ n "List") (hsTyVar $n "a"))
            ]
        ]
        {-deriving-} []



--
--------------------------------------------------------------------------------







