-- $Id: HsParser.y,v 1.16 2001/11/24 04:55:36 hallgren Exp $

-- New Low-level Haskell Parser
-- Bill Harrison and Emir Pasalic and Andrew Moran and Thomas Hallgren
--
-- Note: 
--   This parser is based on Simon Marlow and Sven Panne's (1997,1998) Haskell
--   grammar for Happy. 
--   The parser does not correspond strictly to the grammar of standard
--   Haskell.  Rather, it relies on a number of postprocessing steps that 
--    (1) validate the rather leaky terms produced by the and discard invalid 
--        programs 
--    (2) perform a small amount of rewriting (e.g., for infix operator
--        precedences)

{
module HsParser (parse) where
 
import Syntax
import SyntaxUtil
import ParseMonad
import Lexer
import LexUtil(readInteger, readRational)
import ParseUtil
--import Rewrite
import IOExts
import Char(showLitChar)

}

%token
        VARID 	 { VarId $$ }
	QVARID 	 { QVarId $$ }
	CONID	 { ConId $$ }
	QCONID   { QConId $$ }
	'-'	 { VarSym "-" }
	VARSYM	 { VarSym $$ }
	CONSYM	 { ConSym $$ }
	QVARSYM	 { QVarSym $$ }
	QCONSYM  { QConSym $$ }
	QMODID   { QModId $$ }
	INT	 { IntTok $$ }
	RATIONAL { FloatTok $$ }
	CHAR	 { Character $$ }
	STRING   { StringTok $$ }
--- Symbols --------------------------
	'('	{ LeftParen }
	')'	{ RightParen }
	';'	{ SemiColon }
	'{'	{ LeftCurly }
	'}'	{ RightCurly }
	vccurly { VRightCurly }	      -- a virtual close brace
	'['	{ LeftSquare }
	']'	{ RightSquare }
  	','	{ Comma }
	'_'	{ Underscore }
	'`'	{ BackQuote }
        '.'     { Period }            -- must be a token so it can matched in
	                              -- property quantifier expressions; it
                                      -- must be turned into an id when not
                                      -- matched thus, or used in a float.

--- Reserved operators ----------------

	'..'	{ DotDot }
	'::'	{ DoubleColon }
	'='	{ Equals }
	'\\'	{ Backslash }
	'|'	{ Bar }
	'<-'	{ LeftArrow }
	'->'	{ RightArrow }
	'@'	{ At }
	'~'	{ Tilde }
	'=>'	{ DoubleArrow }
--	'-'	{ Minus }
	'!'	{ Exclamation }
--- Reserved Ids ----------------------
	'as'		{ KW_As }
	'case'		{ KW_Case }
	'class'		{ KW_Class }
	'data'		{ KW_Data }
	'default'	{ KW_Default }
	'deriving'	{ KW_Deriving }
	'do'		{ KW_Do }
	'else'		{ KW_Else }
	'hiding'	{ KW_Hiding }
	'if'		{ KW_If }
	'import'	{ KW_Import }
	'in'		{ KW_In }
	'infix'		{ KW_Infix }
	'infixl'	{ KW_InfixL }
	'infixr'	{ KW_InfixR }
	'instance'	{ KW_Instance }
	'let'		{ KW_Let }
	'module'	{ KW_Module }
	'newtype'	{ KW_NewType }
	'of'		{ KW_Of }
	'then'		{ KW_Then }
	'type'		{ KW_Type }
	'where'		{ KW_Where }
	'qualified'	{ KW_Qualified }
	'primitive'     { KW_Primitive }
{-
--      Additions for property syntax
        'property'      { KW_Property }
        'All'           { KW_QAll }
        'Ex'            { KW_QExists }
        'AllDef'        { KW_QAllDef }
        'ExU'           { KW_QExistsU }
-}
%monad { PM } { thenPM } { returnPM }
%lexer { lexer } { EOF }
%name parse
%tokentype { Token }
%%
{-

-----------------------------------------------------------------------------
Module Header

-}
module :: { HsModuleR }
        : srcloc 'module' modid maybeexports 'where' body
			     { hsModule $1 $3 $4 $6 }
        | srcloc body	     { hsModule $1 main_mod Nothing $2 }

body :: { ([HsImportDecl], [HsDecl]) }
	:   '{' bodyaux '}'			{ $2 }
 	| open  bodyaux close			{ $2 }

bodyaux :: { ([HsImportDecl], [HsDecl]) }
	: impdecls ';' topdecls optsemi    { ($1, $3) }
	|              topdecls optsemi    { ([], $1) }
	| impdecls              optsemi    { ($1, []) }
	| {- empty -}			   { ([], []) }

optsemi :: { () }
	: ';'						{ () }
	| {- empty -}					{ () }
{-

-----------------------------------------------------------------------------
The Export List

-}
maybeexports :: { Maybe [HsExportSpec] }
 	:  exports				{ Just $1 }
 	|  {- empty -}				{ Nothing }

exports :: { [HsExportSpec] }
	: '(' exportlist maybecomma ')'		{ reverse $2 }
	| '(' ')'				{ [] }

maybecomma :: { () }
	: ','					{ () }
	| {- empty -}				{ () }

exportlist :: { [HsExportSpec] }
 	:  exportlist ',' export		{ $3 : $1 }
 	|  export				{ [$1]  }

export :: { HsExportSpec }
 	:  qvar				      { HsEVar $1 }
 	|  qtyconorcls			      { HsEAbs $1 }
 	|  qtyconorcls '(' '..' ')'	      { HsEThingAll $1 }
 	|  qtyconorcls '(' ')'		      { HsEThingWith $1 [] }
 	|  qtyconorcls '(' qcnames ')'	      { HsEThingWith $1 (reverse $3) }
 	|  'module' modid		      { HsEModuleContents $2 }

qcnames :: { [HsName] }
 	:  qcnames ',' qcname			{ $3 : $1 }
 	|  qcname				{ [$1]  }

qcname :: { HsName }
	:  qvar					{ $1 }
 	|  qcon					{ $1 }
{-

-----------------------------------------------------------------------------
Import Declarations

-}
impdecls :: { [HsImportDecl] }
	: impdecls ';' impdecl			{ $3 : $1 }
	| impdecl				{ [$1] }

impdecl :: { HsImportDecl }
	: 'import' srcloc optqualified modid maybeas maybeimpspec
 		  		{ HsImportDecl $2 $4 $3 $5 $6 }

optqualified :: { Bool }
       : 'qualified'                            { True  }
       | {- empty -}				{ False }

maybeas :: { Maybe Module }
       : 'as' modid                             { Just $2 }
       | {- empty -}				{ Nothing }

maybeimpspec :: { Maybe (Bool, [HsImportSpec]) }
	: impspec				{ Just $1 }
	| {- empty -}				{ Nothing }

impspec :: { (Bool, [HsImportSpec]) }
 	:  '(' optimportlist maybecomma ')'  	  { (False, reverse $2) }
 	|  'hiding' '(' optimportlist maybecomma ')' { (True,  reverse $3) }

optimportlist :: { [HsImportSpec] }
	      : maybecomma			{ [] }
	      | importlist maybecomma		{ $1 }
	      
importlist :: { [HsImportSpec] }
 	:  importlist ',' import		{ $3 : $1 }
 	|  import				{ [$1]  }

import :: { HsImportSpec }
 	:  var				      { HsIVar $1 }
 	|  tyconorcls			      { HsIAbs $1 }
 	|  tyconorcls '(' '..' ')'	      { HsIThingAll $1 }
 	|  tyconorcls '(' ')'		      { HsIThingWith $1 [] }
 	|  tyconorcls '(' cnames ')'	      { HsIThingWith $1 (reverse $3) }

cnames :: { [HsName] }
 	:  cnames ',' cname			{ $3 : $1 }
 	|  cname				{ [$1]  }

cname :: { HsName }
	:  var					{ $1 }
 	|  con					{ $1 }

{-

-----------------------------------------------------------------------------
Top-level declarations.

-}

topdecls :: { [HsDecl] }
	: topdecls ';' topdecl     { funCons $3 $1 }
	| topdecl		      { [$1] }

{-

-----------------------------------------------------------------------------
Fixity Declarations

checkPrec has been eliminated; fixities may now be negative => must be added
to the static check.

-}

fix :: { HsDecl }
 	: infix srcloc prec ops   { hsInfixDecl $2 (HsFixity $1 $3) $4 }
	                
prec :: { Int }
	: {- empty -}		  { 9 }
	| INT		          { fromInteger (readInteger $1) }

infix :: { HsAssoc }
	: 'infix'				{ HsAssocNone  }
	| 'infixl'				{ HsAssocLeft  }
	| 'infixr'				{ HsAssocRight }

ops   :: { [HsIdent] }
	: op ',' ops				{ $1 : $3 }
	| op					{ [$1] }

{-

-----------------------------------------------------------------------------
Top-Level Declarations

Note: The report allows topdecls to be empty. This would result in another
shift/reduce-conflict, so we don't handle this case here, but in bodyaux.

-}

{-
topdecls :: { [HsDecl] }
	: topdecls ';' topdecl		{ funCons $3  $1 }
	| topdecl			{ [$1] }
-}

topdecl :: { HsDecl }
	: 'type' tyconparams srcloc '=' type	
	       { hsTypeDecl $3 $2 $5 }
        | 'data' srcloc ctyconparams '=' constrs deriving
               { hsDataDecl $2 (fst $3) (snd $3) (reverse $5) $6 } 
	| 'newtype' srcloc ctyconparams '=' constr deriving
	       { hsNewTypeDecl $2 (fst $3) (snd $3) $5 $6 }

	| 'class' srcloc ctype optfundeps optcbody	
	       { hsClassDecl  $2 (fst $3) (snd $3) $4 $5 }
	| 'instance' srcloc ctype optvaldefs
               { hsInstDecl $2 (fst $3) (snd $3) $4 }	
	| 'default' srcloc type		
	       { hsDefaultDecl $2 $3 }

        -- Hugs compatibility
        | 'data' srcloc ctybinding
	       { hsPrimitiveTypeDecl $2 (fst $3) (snd $3) }

	| 'primitive' srcloc var '::' type
	       { hsPrimitiveBind $2 $3 $5 }
        
        | decl { $1 }

optfundeps :: { HsFunDeps HsType }
	   :			 	{ [] }
	   | '|' fundeps		{ $2 }

fundeps	   :: { HsFunDeps HsType }
	   : fundep			{ [$1] }
	   | fundep ',' fundeps		{ $1:$3 }

fundep	   :: { HsFunDep HsType }
	   : tyvars '->' tyvars		{ ($1,$3) }

tyvars	   :: { [HsType] }
	   :				{ [] }
	   | typarams			{ $1 }

decls :: { [HsDecl] }
	: decls1 optsemi		{ reverse $1 }
	| optsemi 			{ [] }

decls1 :: { [HsDecl] }
	: decls1 ';' decl		{ funCons $3 $1 }
	| decl				{ [$1] }

decl :: { HsDecl }
	: signdecl			{ $1 }
        | fix                           { $1 }
	| valdef			{ $1 }
{-
        -- Property declarations
        | propdecl                      { $1 }
-}

decllist :: { [HsDecl] }
	:  '{' decls '}'	{ $2 }
	| open decls close	{ $2 }

signdecl :: { HsDecl }
	: vars srcloc '::' ctype
	      { hsTypeSig $2 (reverse $1) (fst $4) (snd $4) }
{-


ATTENTION: Dirty Hackery Ahead! If the second alternative of vars is var
instead of qvar, we get another shift/reduce-conflict. Consider the
following programs:

   { (+) :: ... }          A "signdecl" where everything to the left of the
                           :: is parsed as "vars" which should allow only var

   { (+) x y  = ... }      A "valdef" where everything to the left of the
                           = is parsed as an "infixexp" which (incorrectly
                           in this context) allows a "qvar", since "infixexp"
                           is also used to parse patterns where "qvar" is
                           allowed

This leads to a shift/reduce-conflict. The parser must decide without too much
lookahead.  By allowing a qvar as the first thing in "vars" the parser shifts
(until it sees a "," or a "::") and doesn't get confused.  Without this,
deciding what to do with requires more lookahead.  So let's allow "qvar" in
"vars" and then check for ourselves afterwards that this didn't happen.

-}
vars	:: { [HsName] }
	: vars ',' var		{ $3 : $1 }
	| qvar			{% case $1 of
				   Qual _ _ -> parseError "bad qvar in vars."
				   _        -> return [$1]
				}
{-

-----------------------------------------------------------------------------
Types

-}
type :: { HsType }
	: btype '->' type		{ hsTyFun $1 $3 }
	| btype				{ $1 }

btype :: { HsType }
        : btype atype                   { hsTyApp $1 $2 }
        | atype                         { $1 }

atype :: { HsType }
	: gtycon			{ hsTyCon $1 }
	| tyvar				{ hsTyVar $1 }
	| '(' types ')'			{ hsTyTuple (reverse $2) }
	| '[' type ']'			{ hsTyApp list_tycon $2 }
	| '(' type ')'			{ $2 }

gtycon :: { HsName }
	: qtycon			{ $1 }
	| '(' ')'			{ unit_tycon_name }
	| '[' ']'			{ list_tycon_name }
	| '(' '->' ')'	                { fun_tycon_name }
	| '(' commas ')'		{ tuple_tycon_name $2 }
{- There is no need to qualify special syntax, since it *always* refers to 
   things defined in Prelude... /TH
        -- These next three are not strictly Haskell 98, but are accepted by
        -- GHC.  Their omission from the report seems to be a bug, since
	-- without this, one cannot import the Prelude qualified and refer to
        -- the type construtors (), [], or the tuple type constructors.
	| QMODID '.' '(' ')'		{ qualify $1 "()" }
	| QMODID '.' '[' ']'		{ qualify $1 "[]" }
	| QMODID '.' '(' commas ')'     { qualify $1 (tuple $4) }
-}
{-

(Slightly edited) Comment from GHC's hsparser.y:
"context => type" vs  "type" is a problem, because you can't distinguish
between:

	foo :: (Baz a, Baz a)

	bar :: (Baz a, Baz a) => [a] -> [a] -> [a]

with one token of lookahead.  The HACK is to parse the context as a btype
(more specifically as a tuple type), then check that it has the right form
C a, or (C1 a, C2 b, ... Cn z) and convert it into a context.  Blaach!

-}
ctype :: { ([HsType],HsType) }
	: type '=>' type      { (reverse (tupleTypeToContext $1), $3) }
	| type		      { ([], $1) }

types	:: { [HsType] }
	: types ',' type	    { $3 : $1 }
	| type  ',' type	    { [$3, $1] }

ctyconparams :: { ([HsType], [HsType]) }
	: type '=>' tyconparams     { (reverse (tupleTypeToContext $1), $3) }
	| tyconparams               { ([], $1) }

-- Replacing tycon with gtycon as an experiment: /TH
tyconparams :: { [HsType] }
        : gtycon typarams           { hsTyCon $1 : reverse $2 }
	| gtycon		    { [hsTyCon $1] }

typarams :: { [HsType] }
	: typarams tyvar            { hsTyVar $2 : $1 }
	| tyvar			    { [hsTyVar $1] }

ctybinding :: { ([HsType], HsName) }
	: ctyconparams  {% case snd $1 of
		             [Typ (HsTyCon nm)] -> return (fst $1,nm)
			     _ -> parseError "Primitive types are not allowed to have parameters" }

{-

-----------------------------------------------------------------------------
Datatype declarations

-}
constrs :: { [HsConDecl HsType ] }
	: constrs '|' constr		{ $3 : $1 }
	| constr			{ [$1] }

constr :: { HsConDecl HsType }
	: srcloc scontype		{ HsConDecl $1 (fst $2) (snd $2) }
	| srcloc sbtype conop sbtype	{ HsConDecl $1 $3 [$2, $4] }
	| srcloc con '{' fielddecls '}' 
					{ HsRecDecl $1 $2 (reverse $4) }
scontype :: { (HsName, [HsBangType HsType]) }
	: btype			    {% do { (c, ts) <- splitTyConApp $1 ;
					    return (c, map HsUnBangedType ts)
					  }
				    }
	| scontype1		    { $1 }
--      | '(' qconsym ')' satypes   { ($2,$4) }

scontype1 :: { (HsName, [HsBangType HsType]) }
	: btype '!' atype
	      {% do { (c, ts) <- splitTyConApp $1 ;
		      return (c, map HsUnBangedType ts ++ [HsBangedType $3])
		    }
	      }
	| scontype1 satype		
              { (fst $1, snd $1 ++ [$2] ) }
{-
satypes :: { [HsBangType HsType] }
	:				{ [] }
	| satype satypes		{ $1:$2 }
-}
satype :: { HsBangType HsType }
	: atype				{ HsUnBangedType $1 }
	| '!' atype			{ HsBangedType   $2 }

sbtype :: { HsBangType HsType }
	: btype				{ HsUnBangedType $1 }
	| '!' atype			{ HsBangedType   $2 }

fielddecls :: { [([HsName], HsBangType HsType)] }
	: fielddecls ',' fielddecl	{ $3 : $1 }
	| fielddecl			{ [$1] }

fielddecl :: { ([HsName], HsBangType HsType) }
	: vars '::' stype		{ (reverse $1, $3) }

stype :: { HsBangType HsType}
	: type				{ HsUnBangedType $1 }	
	| '!' atype			{ HsBangedType   $2 }

deriving :: { [HsName] }
	: {- empty -}			{ [] }
	| 'deriving' qtycls		{ [$2] }
	| 'deriving' '('          ')'	{ [] }
	| 'deriving' '(' dclasses ')'	{ reverse $3 }

dclasses :: { [HsName] }
	: dclasses ',' qtycls		{ $3 : $1 }
        | qtycls			{ [$1] }
{-

-----------------------------------------------------------------------------
Class declarations

-}
optcbody :: { [HsDecl] }
	: 'where'  '{' cbody '}'		{ $3 }
	| 'where' open cbody close		{ $3 }
	| {- empty -}				{ [] }

cbody :: { [HsDecl] }
	: cmethods ';' cdefaults optsemi	{ reverse $1 ++ reverse $3 }
	| cmethods optsemi			{ reverse $1 }
	| optsemi				{ [] }

cmethods :: { [HsDecl] }
	: cmethods ';' signdecl			{ funCons $3  $1 }
	| signdecl				{ [$1] }

cdefaults :: { [HsDecl] }
	: cdefaults ';' valdef			{ funCons $3  $1 }
	| valdef				{ [$1] }
{-

-----------------------------------------------------------------------------
Instance declarations

-}
optvaldefs :: { [HsDecl] }
	: 'where'  '{' valdefs '}'	{ $3 }
	| 'where' open valdefs close	{ $3 }
	| {- empty -}				{ [] }
{-

Recycling...

-}
valdefs :: { [HsDecl] }
	: cdefaults optsemi			{ reverse $1 }
	| optsemi				{ [] }
{-

-----------------------------------------------------------------------------
Value definitions

-}

{-
valdef :: { HsDecl }
	: infixexp srcloc rhs optwheredecls
				    {% if isPatternExp $1 
                                       then mkValDef $1 $2 $3 $4
                                       else mkFunDef $1 $2 $3 $4
				    }
-}

valdef :: { HsDecl }
	: funlhs srcloc rhs optwheredecls   { mkFunDef' $1 $2 $3 $4 }
        | infixpat srcloc rhs optwheredecls { hsPatBind $2 $1 $3 $4 }

funlhs :: { (HsName,[HsPat]) }
        : qvar apats1               { ($1,$2) }
        | infixpat qvarop infixpat   { ($2,[$1,$3]) }
        | '(' funlhs ')' apats      { (fst $2,snd $2++$4) }
	              -- ^ Haskell 98 requires apats1 (at least one apat)

optwheredecls :: { [HsDecl] }
        : 'where' decllist          { $2 }
        | {- empty -}               { [] }

rhs	:: { HsRhs HsExp }
	: '=' exp		    { HsBody $2 }
	| gdrhss		    { HsGuard (reverse $1) }

gdrhss :: { [(SrcLoc, HsExp, HsExp)] }
	: gdrhss gdrhs		    { $2 : $1 }
	| gdrhs			    { [$1] }

gdrhs :: { (SrcLoc, HsExp, HsExp) }
	: '|' exp srcloc '=' exp    { ($3, $2, $5) }

{-

-----------------------------------------------------------------------------
Expressions

-}
exp   :: { HsExp }
	: infixexp '::' srcloc ctype  	{ hsExpTypeSig $3 $1 (fst $4) (snd $4) }
        | infixexp	                { $1 }

infixexp :: { HsExp }
	: exp10				{ $1 }
	| infixexp qop exp10		{ hsInfixApp $1 $2 $3 }

{-

    From MPJ's Tool0 Hugs98 parser.y:

        | qfier pats '.' exp		{$$ = gc4(ap(QUANTIFY,
                                                     ap($1,
                                                        pair(rev($2),
                                                             pair($3,$4)))));}
-}

exp10 :: { HsExp }
	: '\\' apats '->' exp { hsLambda $2 $4 }
	      {-% do { ps <- mapM expToPat $2 ;
                      return (hsLambda (reverse ps) $4)
		    }
              -}
{-
       | quant pats '.' exp
             {% do { ps <- mapM expToPat $2 ;
                     return (hsPropQuant (reverse ps) $4)
		   }
             }  
-}
  	| 'let' decllist 'in' exp	 { hsLet $2 $4 }
	| 'if' exp 'then' exp 'else' exp { hsIf $2 $4 $6 }
   	| 'case' exp 'of' altslist	 { hsCase $2 $4 } 
	| '-' fexp			 { hsNegApp $2 }
  	| 'do' stmtlist			 { hsDo (atoms2Stmt $2) }
	| fexp				 { $1 }

fexp :: { HsExp }
	: fexp aexp			{ hsApp $1 $2 }
  	| aexp				{ $1 }
{-
aexps :: { [HsExp] }
	: aexps aexp			{ $2 : $1 }
  	| aexp				{ [$1] }
-}
{-

Note: The first alternative of aexp is not neccessarily a record update, it
could be a labeled construction, too.

-}
aexp	:: { HsExp }
  	: aexp '{' fbinds '}'        { mkRecord $1 (reverse $3) }
  	| aexp1			     { $1 }

aexp1	:: { HsExp }
	: qvar			     { hsEVar ($1 :: HsName) }
	| gcon			     { $1 }
  	| literal		     { hsLit $1 }
	| '(' exp ')'		     { hsParen $2 }
	| '(' texps ')'		     { hsTuple (reverse $2) }
	| '[' list ']'               { $2 }
	| '(' infixexp qop ')'	     { hsLeftSection $2 $3 }
	| '(' qop infixexp ')'	     { hsRightSection $2 $3 }
	| qvar '@' aexp1	     { hsAsPat $1 $3 }
	| '_'			     { hsWildCard }
	| '~' aexp1		     { hsIrrPat $2 }

commas :: { Int }
	: commas ','		     { $1 + 1 }
	| ','			     { 1 }

texps :: { [HsExp] }
	: texps ',' exp		     { $3 : $1 }
	| exp ',' exp		     { [$3, $1] }

{-

-----------------------------------------------------------------------------
List expressions

The rules below are little bit contorted to keep lexps left-recursive while
avoiding another shift/reduce-conflict.

-}
list :: { HsExp }
	: exp				{ hsList [$1] }
	| lexps 			{ hsList (reverse $1) }
	| exp '..'			{ hsEnumFrom $1 }
	| exp ',' exp '..' 		{ hsEnumFromThen $1 $3 }
	| exp '..' exp	 		{ hsEnumFromTo $1 $3 }
	| exp ',' exp '..' exp		{ hsEnumFromThenTo $1 $3 $5 }
	| exp '|' quals			
          { hsListComp (atoms2Stmt (reverse $3 ++ [HsQualifierAtom $1])) }

lexps :: { [HsExp] }
	: lexps ',' exp 		{ $3 : $1 }
	| exp ',' exp			{ [$3,$1] }
{-

-----------------------------------------------------------------------------
List comprehensions

-}
quals :: { [HsStmtAtom HsExp HsPat [HsDecl] ] }
	: quals ',' qual		{ $3 : $1 }
	| qual				{ [$1] }

qual  :: { HsStmtAtom HsExp HsPat [HsDecl] }
	: infixexp '<-' exp		{% do { p <- expToPat $1 ; 
                                                return (HsGeneratorAtom p $3)
					      }
					}
	| exp			  	{ HsQualifierAtom $1 }
  	| 'let' decllist		{ HsLetStmtAtom   $2 }

{-

-----------------------------------------------------------------------------
Case alternatives

-}
altslist :: { [HsAlt HsExp HsPat [HsDecl]] }
	: '{'   alts optsemi '}'	{ reverse $2 }
	| open  alts optsemi close	{ reverse $2 }


alts :: { [HsAlt HsExp HsPat [HsDecl]] }
	: alts ';' alt				{ $3 : $1 }
	| alt					{ [$1] }

alt :: { HsAlt HsExp HsPat [HsDecl] }
	: infixpat srcloc rhscasealts { HsAlt $2 $1 $3 [] }
	      {-% do { p <- expToPat $1 ;
	              return (HsAlt $2 p $3 [])
		    }
	      -} 
        | infixpat srcloc rhscasealts 'where' decllist { HsAlt $2 $1 $3 $5 }
	      {-% do { p <- expToPat $1 ;
		      return (HsAlt $2 p $3 $5)
		    }
	      -}

rhscasealts :: { HsRhs HsExp }
	: '->' exp		            { HsBody $2 }
	| gdcaserhss		            { HsGuard (reverse $1) }

gdcaserhss :: { [(SrcLoc, HsExp, HsExp)] }
	: gdcaserhss gdcaserhs		    { $2 : $1 }
	| gdcaserhs			    { [$1] }

gdcaserhs :: { (SrcLoc, HsExp, HsExp) }
	: '|' srcloc exp  '->' exp          { ($2, $3, $5) }

{-

-----------------------------------------------------------------------------
Statement sequences

-}
stmtlist :: { [HsStmtAtom HsExp HsPat [HsDecl]] }
	:   '{' stmts '}'	{ $2 }
	| open  stmts close	{ $2 }

stmts :: { [HsStmtAtom HsExp HsPat [HsDecl]] }
        : stmts1 ';' exp	      { reverse (HsQualifierAtom $3 : $1) }
 	| exp               	      { [HsQualifierAtom $1] }

stmts1 :: { [HsStmtAtom HsExp HsPat [HsDecl]] }
  	: stmts1 ';' qual		{ $3 : $1 }
	| qual 				{ [$1] }

--- Record Field Update/Construction -------------------------------------------

fbinds :: { [HsFieldUpdate HsExp] }
	  :				{ [] }
	  | fbinds1			{ $1 }

fbinds1 :: { [HsFieldUpdate HsExp] }
	: fbinds1 ',' fbind		{ $3 : $1 }
	| fbind				{ [$1] }

fbind	:: { HsFieldUpdate HsExp }
	: qvar '=' exp			{ HsFieldUpdate $1 $3 }
--	| qvar				{ HsFieldBind $1 }

--- Patterns -------------------------------------------------------------------

pat :: { HsPat }
        : infixpat                { $1 }
     -- | n+k

infixpat :: { HsPat }
	: pat10                   { $1 }
	| infixpat qconop pat10   { hsPInfixApp $1 (HsCon $2) $3 }

pat10 :: { HsPat }
        : qcon apats1             { hsPApp $1 $2 } -- should be gcon...
	| '-' numlit		  { hsPNeg (hsPLit $2) }
        | apat                    { $1 }

apat :: { HsPat }
        : qvar                    { hsPVar $1 }
        | qvar '@' apat           { hsPAsPat $1 $3 }
        | qcon                    { hsPCon $1 } -- should be gcon...
	| '(' ')'                 { hsPCon (qualify "Prelude" "()") }
        | qcon '{' fpats '}'      { hsPRec $1 $3 }
        | literal                 { hsPLit $1 }
        | '_'                     { hsPWildCard }
	| '(' pat ')'             { hsPParen $2 }
	| '(' tpats ')'           { hsPTuple $2 }
	| '[' lpats ']'           { hsPList $2 }
        | '~' apat                { hsPIrrPat $2 }

apats1 :: { [HsPat] }
        : apat apats              { $1 : $2 }

apats :: { [HsPat] }
	:                         { [] }
	| apat apats              { $1 : $2 }

fpats :: { [HsPatField HsPat] }
        :                         { [] }
        | fpats1                  { $1 }

fpats1 :: { [HsPatField HsPat] }
        : fpat ',' fpats1         { $1 : $3 }
	| fpat                    { [$1] }

fpat :: { HsPatField HsPat }
        : qvar '=' pat            { HsPFieldPat $1 $3 }

tpats :: { [HsPat] }
        : pat ',' tpats           { $1 : $3 }
        | pat ',' pat             { [$1, $3] }

lpats :: { [HsPat] }
        :                         { [] }
	| lpats1                  { $1 }

lpats1 :: { [HsPat] }
        : pat ',' lpats           { $1 : $3 }
        | pat                     { [$1] }

{-

-----------------------------------------------------------------------------
Variables, Constructors and Operators.

-}
gcon :: { HsExp }
  	: '(' ')'		     { hsECon (qualify "Prelude" "()") }
	| '[' ']'		     { hsList [] }
	| '(' commas ')'	     { hsECon (qualify "Prelude" (tuple $2)) }
        -- These next three are not strictly Haskell 98, but are accepted by
        -- GHC.  Their omission from the report seems to be a bug, since
	-- without this, one cannot import the Prelude qualified and refer to
        -- the values (), [], or the tuple constructors.  It's unclear what
	-- effect of qualifying the nil list would actually have, since it is
	-- otherwise treated separately (i.e., there is no VARSYM called
        -- "[]").  Since it can't reused, according to the report, I have
	-- treated the same as an unqualified [], ignoring the qualifying
	-- module.  AKM
	| QMODID '.' '(' ')'	     { hsECon (qualify $1 "()") }
	| QMODID '.' '[' ']'	     { hsList [] }
	| QMODID '.' '(' commas ')'  { hsECon (qualify $1 (tuple $4)) }
  	| qcon			     { hsECon $1 }

var 	:: { HsName }
	: varid			{ $1 }
	| '(' varsym ')'	{ $2 }

qvar 	:: { HsName }
	: qvarid		{ $1 }
	| '(' qvarsym ')'	{ $2 }

con	:: { HsName }
	: conid			{ $1 }
	| '(' consym ')'        { $2 }

qcon	:: { HsName }
	: qconid		{ $1 }
	| '(' qconsym ')'	{ $2 }

varop	:: { HsName }
	: varsym		{ $1 }
	| '`' varid '`'		{ $2 }

qvarop :: { HsName }
	: qvarsym		{ $1 }
	| '`' qvarid '`'	{ $2 }
{-
qvaropm :: { HsName }
	: qvarsymm		{ $1 }
	| '`' qvarid '`'	{ $2 }
-}
conop :: { HsName }
	: consym		{ $1 }	
	| '`' conid '`'		{ $2 }

qconop :: { HsName }
	: qconsym		{ $1 }
	| '`' qconid '`'	{ $2 }

op	:: { HsIdent }
	: varop			{ hsVar $1 }
	| conop 		{ hsCon $1 }

qop	:: { HsIdent }
	: qvarop		{ hsVar $1 }
	| qconop		{ hsCon $1 }
{-
qopm	:: { HsIdent }
	: qvaropm		{ hsVar $1 }
	| qconop		{ hsCon $1 }
-}
qvarid :: { HsName }
	: varid			{ $1 }
	| QVARID		{ uncurry (Qual . Module) $1 }

varid :: { HsName }
	: VARID			{ UnQual $1 }
	| 'as'			{ as_name }
	| 'qualified'           { qualified_name }
	| 'hiding'		{ hiding_name }

qconid :: { HsName }
	: conid			{ $1 }
        | QCONID		{ uncurry (Qual . Module) $1 }

qtycon :: { HsName }
	: tycon			{ $1 }
	| QCONID		{ uncurry (Qual . Module) $1 }

conid :: { HsName }
	: CONID			{ UnQual $1 }

qconsym :: { HsName }
	: consym		{ $1 }
	| QCONSYM		{ uncurry (Qual . Module) $1 }

consym :: { HsName }
	: CONSYM		{ UnQual $1 }

qvarsym :: { HsName }
	: varsym		{ $1 }
	| qvarsym1		{ $1 }
{-
qvarsymm :: { HsName }
	: varsymm		{ $1 }
	| qvarsym1		{ $1 }
-}
varsym :: { HsName }
	: VARSYM		{ UnQual $1 }
	| '-'			{ minus_name }
	| '!'			{ pling_name }
        | '.'                   { period_name }
{-
varsymm :: { HsName } -- varsym not including '-'
	: VARSYM		{ UnQual $1 }
	| '!'			{ pling_name }
        | '.'                   { period_name }
-}
qvarsym1 :: { HsName }
	: QVARSYM		{ uncurry (Qual . Module) $1 }

literal :: { HsLiteral }
	: numlit		{ $1 }
	| CHAR 			{ HsChar $1 }
	| STRING		{ HsString $1 }

numlit :: { HsLiteral }
	: INT 			{ HsInt (readInteger $1) }
	| RATIONAL		{ HsFrac (readRational $1) }
        
srcloc :: { SrcLoc }	:	{% getSrcLoc }

--- Layout ---------------------------------------------------------------------

open  :: { () }
       :	                {% do { SrcLoc _ _ c <- getSrcLoc ;
					pushContext (Layout c)
				      }
				}

close :: { () }
	: vccurly		{ () } -- context popped in lexer.
	| error			{% popContext }

--- Miscellaneous (mostly renamings) -------------------------------------------

modid :: { Module }
	: CONID			{ Module $1 }

tyconorcls :: { HsName }
	: conid			{ $1 }

tycon :: { HsName }
	: conid			{ $1 }

qtyconorcls :: { HsName }
	: qtycon		{ $1 }

qtycls :: { HsName }
	: qtycon		{ $1 }

tyvar :: { HsName }
	: varid			{ $1 }
{-

-----------------------------------------------------------------------------

     Property declarations

-----------------------------------------------------------------------------

From MPJ's Tool0 Hugs98 parser.y file:

gendecl   : PROPERTY pLhs '=' exp	{$$ = gc4(ap(PROP,ap($2,ap($3,$4))));}
	  | PROPERTY error		{syntaxError("property decl");}
	  ;
pLhs	  : pLhs varid			{$$ = gc2(ap($1,$2));}
	  | CONID			{$$ = $1;}
	  | error			{syntaxError("property defn lhs");}
	  ;
qfier	  : QALL			{$$ = gc1(quantAll);}
	  | QEX				{$$ = gc1(quantEx);}
	  | QALLDEF			{$$ = gc1(quantAlldef);}
	  | QEXU			{$$ = gc1(quantExu);}
	  ;

-}

{-

propdecl :: { HsDecl }
	: 'property' quant pLhs '=' exp  { hsProp $2 $3 $5 }

quant :: { HsQuantifier } 
	: 'All'                          { hsPropForall } 
        | 'Ex'                           { hsPropExists }
	| 'AllDef'                       { hsPropForallDefined }
	| 'ExU'                          { hsPropExistsUnique }

pLhs :: { [HsName] }
        : pLhs varid                     { $2 : $1 }
        | conid                          { [$1] }

-}

{-

-----------------------------------------------------------------------------

-}

{
happyError = parseError "parse error"
}
