{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
{-+
Instances for extracting defined names from the nonrecursive 
base language structures.
-}
module DefinedNamesBaseStruct where
import BaseSyntax
import DefinedNames
import HsIdent (getHSName)

instance DefinedNames i ds => DefinedNames i (HsModuleI m i' ds) where
  definedNames = definedNames . hsModDecls -- hmm

instance ClassMethods i (DI i e p ds t c tp) where
    classMethods cname cnt d =
      case d of 
        (HsTypeSig s nms _ _) -> map (method cname cnt nms) nms
        _                   -> [] 

instance AddName i (DI i e p ds t c tp)

instance (DefinedNames i tp, ClassMethods i ds, ContextSize c, DefinedNames i p)
       => DefinedNames i (DI i e p ds t c tp) where
    definedNames d =
      case d of
        HsTypeDecl s tp t              -> dataNames tp Synonym []
        HsNewTypeDecl s ctx tp cd drv  -> dataNames tp Newtype [cd]
        HsDataDecl s ctx tp cds drv    -> dataNames tp Data cds
        HsClassDecl s c tp fd ds       -> classNames tp c ds
        HsInstDecl s optn c tp ds      -> [] -- !!
        HsDefaultDecl s t              -> []
        HsTypeSig s nms c t            -> []
        HsFunBind s (match:_)          -> [matchName match]
        HsPatBind s p rhs ds           -> definedNames p
        HsInfixDecl s fixity names     -> []

        --HsPrimitiveTypeDecl s ctx tp   -> definedNames tp
        HsPrimitiveTypeDecl s ctx tp   -> dataNames tp Primitive []
        HsPrimitiveBind s nm tp        -> [value nm]
        _ -> []

      where 
        dataNames tp defty cds = tcon t tyinfo:cons++fields
          where
            tyinfo = TypeInfo 
                { defType       = Just defty
                , constructors  = cs
                , fields        = fs 
                } 
    
            cons    = map (con t tyinfo . conName) cs
            fields  = map (field t tyinfo) fs
            cs      = map conNameArity cds
            fs      = concatMap fieldNames cds
            t       = definedType tp
    
            conNameArity c =
              case c of 
                HsConDecl s _ _ n args -> ConInfo {conName=n,
					           conArity=length args,
					           conFields=Nothing}
                HsRecDecl s _ _ n fields -> ConInfo {conName=n,
						     conArity=length fs,
						     conFields=Just fs}
		  where fs = concatMap fst fields
            fieldNames c =
              case c of 
                HsConDecl s _ _ n types -> []
                HsRecDecl s _ _ n fields -> concatMap fst fields 
    
        classNames tp ctx ds =
              classname c n (map (getHSName . fst) methods) : methods
            where
	      n = contextSize ctx -- number of superclasses
              methods = classMethods c n ds
              c = definedType tp
    
        matchName (HsMatch s n _ _ _) = value n


-- Limited to function/pattern bindings. It is used to rename default methods...
instance MapDefinedNames i p => MapDefinedNames i (DI i e p ds t c tp) where
  mapDefinedNames f d =
      case d of
        HsPatBind s p rhs ds -> HsPatBind s (m p) rhs ds
	_ -> mapDI2 f id id id id id id id d
    where m x = mapDefinedNames f x


-- Meaningful for type patterns (types on the lhs in definitions) only:
instance DefinedNames i tp => DefinedNames i (TI i tp) where
  -- no need to define classMethods
  definedNames t =
      case t of
        HsTyApp f x -> definedNames f
        HsTyCon nm  -> [ tcon nm blankTypeInfo ]  
        _ -> [] -- hmm, report error?

{-+
For patterns, #definedNames# should return the identifiers that are bound by
the pattern, i.e., variables, but not constructors and field labels.
-}
instance DefinedNames i p => DefinedNames i (PI i p) where
  -- no need to define classMethods
  definedNames p =
      case p of
        HsPRec c fields -> definedNames fields -- (*)
	_ -> accPI2 ((:).value) (const id) ((++).definedNames) p []

      -- (*) This is treated specially, since accPI2 includes fnm in the result

instance DefinedNames i p => DefinedNames i (HsFieldI i p) where
  definedNames (HsField f p) = definedNames p


instance MapDefinedNames i p => MapDefinedNames i (PI i p) where
  mapDefinedNames f p =
      case p of
        HsPRec c fields -> HsPRec c (m fields)
        _ -> mapPI2 f id m p
    where m x = mapDefinedNames f x

instance MapDefinedNames i p => MapDefinedNames i (HsFieldI i p) where
  mapDefinedNames f (HsField field p) = HsField field (mapDefinedNames f p)
