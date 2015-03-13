-- A copied and modified version of ../base/parse2/Parser/HsParser.y...
{
module PropParser (parse) where
 
import PropPosSyntax
--import SyntaxUtil
import HsTokens(Token(..))
import ParseMonad
import HsLexer
import LexUtil(readInteger, readRational)
import PropParseUtil
import PropPlogic as P
--import IOExts

}

%token
--- Reserved Ids ----------------------
	'as'		{ (Varid     ,($$,"as")) }
	'case'		{ (Reservedid,($$,"case")) }
	'class'		{ (Reservedid,($$,"class")) }
	'data'		{ (Reservedid,($$,"data")) }
	'default'	{ (Reservedid,($$,"default")) }
	'deriving'	{ (Reservedid,($$,"deriving")) }
	'do'		{ (Reservedid,($$,"do")) }
	'else'		{ (Reservedid,($$,"else")) }

        -- higher rank poly extension
        'forall'        { (Varid     ,($$,"forall")) }

	'hiding'	{ (Varid     ,($$,"hiding")) }
	'if'		{ (Reservedid,($$,"if")) }
	'import'	{ (Reservedid,($$,"import")) }
	'in'		{ (Reservedid,($$,"in")) }
	'infix'		{ (Reservedid,($$,"infix")) }
	'infixl'	{ (Reservedid,($$,"infixl")) }
	'infixr'	{ (Reservedid,($$,"infixr")) }
	'instance'	{ (Reservedid,($$,"instance")) }
	'let'		{ (Reservedid,($$,"let")) }
	'module'	{ (Reservedid,($$,"module")) }
	'newtype'	{ (Reservedid,($$,"newtype")) }
	'of'		{ (Reservedid,($$,"of")) }
	'then'		{ (Reservedid,($$,"then")) }
	'type'		{ (Reservedid,($$,"type")) }
	'where'		{ (Reservedid,($$,"where")) }
	'qualified'	{ (Varid     ,($$,"qualified")) }
	'_'		{ (Reservedid,($$,"_")) }
        '+'             { (Varsym    ,($$,"+")) }
	'primitive'     { (Varid     ,($$,"primitive")) } -- Hugs extension
	'foreign'       { (Varid     ,($$,"foreign")) } -- FFI extension

--- Additions for property syntax
        'assert'        { (Reservedid,($$,"assert")) }
        'property'      { (Reservedid,($$,"property")) }
        'All'           { (Conid     ,($$,"All")) }
        'Exist'         { (Conid     ,($$,"Exist")) }
        'Lfp'           { (Conid     ,($$,"Lfp")) }
        'Gfp'           { (Conid     ,($$,"Gfp")) }
        '==='           { (Varsym    ,($$,"===")) }
        '=/='           { (Varsym    ,($$,"=/=")) }
        '==>'           { (Varsym    ,($$,"==>")) }
        '<==>'          { (Varsym    ,($$,"<==>")) }
        ':::'           { (Consym    ,($$,":::")) }
        '-/'            { (Varsym    ,($$,"-/")) }
        '/\\'           { (Varsym    ,($$,"/\\")) }
        '\\/'           { (Varsym    ,($$,"\\/")) }
	'$'	        { (Varsym    ,($$,"$")) }

--- Symbols --------------------------
	'('	{ (Special,($$,"(")) }
	')'	{ (Special,($$,")")) }
	';'	{ (Special,($$,";")) }
	'{'	{ (Special,($$,"{")) }
	'}'	{ (Special,($$,"}")) }
	VLCURLY { (Layout ,($$,"{")) }	      -- a virtual open brace
	VRCURLY { (Layout ,($$,"}")) }	      -- a virtual close brace
	'['	{ (Special,($$,"[")) }
	']'	{ (Special,($$,"]")) }
  	','	{ (Special,($$,",")) }
	'`'	{ (Special,($$,"`")) }

        '.'     { (Varsym, ($$,"."))}  -- must be a token so it can matched in
	                               -- property quantifier expressions; it
                                       -- must be turned into an id when not
                                       -- matched thus, or used in a float.


--- Reserved operators ----------------

	'..'	{ (Reservedop,($$,"..")) }
	':'	{ (Reservedop,($$,":")) }
	'::'	{ (Reservedop,($$,"::")) }
	'='	{ (Reservedop,($$,"=")) }
	'\\'	{ (Reservedop,($$,"\\")) }
	'|'	{ (Reservedop,($$,"|")) }
	'<-'	{ (Reservedop,($$,"<-")) }
	'->'	{ (Reservedop,($$,"->")) }
	'@'	{ (Reservedop,($$,"@")) }
	'~'	{ (Reservedop,($$,"~")) }
	'=>'	{ (Reservedop,($$,"=>")) }
	'!'	{ (Varsym    ,($$,"!")) }

--- Open token classes:
        VARID 	 { (Varid,$$) }
	QVARID 	 { (Qvarid,$$) }
	CONID	 { (Conid,$$) }
	QCONID   { (Qconid,$$) }
	'-'	 { (Varsym,($$,"-")) }
	VARSYM	 { (Varsym,$$) }
	CONSYM	 { (Consym,$$) }
	QVARSYM	 { (Qvarsym,$$) }
	QCONSYM  { (Qconsym,$$) }
	INT	 { (IntLit,$$) }
	RATIONAL { (FloatLit,$$) }
	CHAR	 { (CharLit,$$) }
	STRING   { (StringLit,$$) }

        BADTOKEN { $$ } -- This is reported as an unused terminal.
		        -- It is included to turn lexical errors into syntax
		        -- errors, rather than pattern match failures in 
			-- the generated parser.

%monad { PM } { thenPM } { returnPM }
%lexer { lexer } { (GotEOF,_) }
%name parse
%tokentype { HToken }

-- Precedences, from lowest to highest
%right 'Gfp' 'Lfp' 'All' 'Exist'
%right '->' 'in' 'else'
%right '::'
%left '@'
%left '{'
%left '<==>' -- FIRST(qop)
%right '==>' -- FIRST(qop)
%left '/\\' '\\/' '-/' '===' '=/=' -- FIRST(qop)
%left ':::' -- FIRST(qop)
%left VARSYM '+' '-' QVARSYM CONSYM QCONSYM '`' '!' ':' '.' '$' -- FIRST(qop)
%left 'as' 'hiding' 'qualified' 'foreign' VARID CONID QCONID '(' '[' -- FIRST(atype)
%%
{-

-----------------------------------------------------------------------------
Module Header

-}
module :: { HsModuleR }
        : 'module' modid maybeexports 'where' body
			     { hsModule $1 $2 $3 $5 }
        | srcloc body	     { hsMainModule $1 $2 }

body :: { ([HsImportDecl], [HsDecl]) }
	:   '{' bodyaux '}'			{ $2 }
 	| open  bodyaux close			{ $2 }

bodyaux :: { ([HsImportDecl], [HsDecl]) }
	: impdecls semis1 topdecls semis    { ($1, $3) }
	|                 topdecls semis    { ([], $1) }
	| impdecls                 semis    { ($1, []) }
	| {- empty -}                       { ([], []) }

{-
optsemi :: { () }
	: ';'				    { () }
	| {- empty -}		            { () }
-}

semis1 :: { () }
        : ';' semis1                    { () }
        | ';'                           { () }

semis :: { () }
        : ';' semis                     { () }
        | {- empty -}                   { () }



{-

-----------------------------------------------------------------------------
The Export List

-}
maybeexports :: { Maybe [HsExportSpec] }
 	:  exports				{ Just $1 }
 	|  {- empty -}				{ Nothing }

exports :: { [HsExportSpec] }
	: '(' optcomma exportlist optcomma ')'		{ reverse $3 }
	| '(' ')'				{ [] }

optcomma :: { () }
	: ','					{ () }
	| {- empty -}				{ () }

exportlist :: { [HsExportSpec] }
 	:  exportlist ',' export		{ $3 : $1 }
 	|  export				{ [$1]  }

export :: { HsExportSpec }
 	:  qvar				     { EntE (Var $1) }
 	|  qtyconorcls			     { EntE (Abs $1) }
 	|  qtyconorcls '(' '..' ')'	     { EntE (AllSubs $1) }
 	|  qtyconorcls '(' ')'		     { EntE (ListSubs $1 []) }
 	|  qtyconorcls '(' qcnames ')'	     { EntE (ListSubs $1 (reverse $3)) }
 	|  'module' modid		     { ModuleE $2 }

qcnames :: { [HsIdent] }
 	:  qcnames ',' qcname			{ $3 : $1 }
 	|  qcname				{ [$1] }

qcname :: { HsIdent }
	:  qvar					{ HsVar $1 }
 	|  qcon					{ HsCon $1 }
{-

-----------------------------------------------------------------------------
Import Declarations

-}
impdecls :: { [HsImportDecl] }
	: impdecls semis1 impdecl		{ $3 : $1 }
	| impdecl				{ [$1] }

impdecl :: { HsImportDecl }
	: 'import' optqualified modid maybeas maybeimpspec
 		  		{ HsImportDecl $1 $3 $2 $4 $5 }

optqualified :: { Bool }
        : 'qualified'                            { True  }
        | {- empty -}				{ False }

maybeas :: { Maybe ModuleName }
        : 'as' modid                             { Just $2 }
        | {- empty -}				{ Nothing }

maybeimpspec :: { Maybe (Bool, [HsImportSpec]) }
	: impspec				{ Just $1 }
	| {- empty -}				{ Nothing }

impspec :: { (Bool, [HsImportSpec]) }
 	: optimportlist  	          { (False, reverse $1) }
 	| 'hiding' optimportlist          { (True,  reverse $2) }

optimportlist :: { [HsImportSpec] }
        : '(' optcomma ')'		  { [] }
	| '(' importlist optcomma ')'	  { $2 }
	      
importlist :: { [HsImportSpec] }
 	:  importlist ',' import		{ $3 : $1 }
 	|  import				{ [$1]  }

import :: { HsImportSpec }
 	:  var				      { Var $1 }
 	|  tyconorcls			      { Abs $1 }
 	|  tyconorcls '(' '..' ')'	      { AllSubs $1 }
 	|  tyconorcls '(' ')'		      { ListSubs $1 [] }
 	|  tyconorcls '(' cnames ')'	      { ListSubs $1 (reverse $3) }

cnames :: { [HsIdent] }
 	:  cnames ',' cname			{ $3 : $1 }
 	|  cname				{ [$1]  }

cname :: { HsIdent }
	:  var					{ HsVar $1 }
 	|  con					{ HsCon $1 }

{-

-----------------------------------------------------------------------------
Top-level declarations.

-}

topdecls :: { [HsDecl] }
	: topdecls semis1 topdecl     { foldl (flip funCons) $1 $3 }
	| topdecl		      { $1 }


{-

-----------------------------------------------------------------------------
Fixity Declarations

checkPrec has been eliminated; fixities may now be negative => must be added
to the static check.

-}

fixitydecl :: { HsDecl }
 	: infix prec ops   { hsInfixDecl (fst $1) (HsFixity (snd $1) $2) $3 }
	                
prec :: { Int }
	: {- empty -}		  { 9 }
	| INT		          { fromInteger (readInteger (snd $1)) }

infix :: { (SrcLoc,HsAssoc) }
	: 'infix'				{ ($1,HsAssocNone)  }
	| 'infixl'				{ ($1,HsAssocLeft)  }
	| 'infixr'				{ ($1,HsAssocRight) }

ops   :: { [HsIdent] }
	: op ',' ops				{ $1 : $3 }
	| op					{ [$1] }

{-

-----------------------------------------------------------------------------
Top-Level Declarations

Note: The report allows topdecls to be empty. This would result in another
shift/reduce-conflict, so we don't handle this case here, but in bodyaux.

-}

topdecl :: { [HsDecl] }
  -- Hugs compatibility (quick hack)
  : 'primitive' vars optimpent '::' type     { [hsPrimitiveBind $1 v $5|v<-$2] }
  | topdecl1	{ [$1] }

optimpent :: { Maybe String }
	  :        { Nothing }
	  | impent { Just $1 }

topdecl1 :: { HsDecl }
  : decl                                        { $1 }
  | 'type' simpletype '=' type                  { hsTypeDecl $1 $2 $4 }
  | 'data' ctyconparams '=' constrs deriving    { uncurry (hsDataDecl $1) $2 (reverse $4) $5 } 
  | 'newtype' ctyconparams '=' constr deriving  {% chkNewtype $4 >> return (uncurry (hsNewTypeDecl $1) $2 $4 $5) }
  | 'class' ctyconparams optfundeps optcbody    { uncurry (hsClassDecl $1) $2 $3 $4 }
  | 'instance' ctype optibody                   { uncurry (hsInstDecl $1 Nothing) $2 $3 }
  | 'default' '(' opttypes ')'                  { hsDefaultDecl $1 $3 }

  -- Hugs compatibility
  | 'data' ctyconparams            { uncurry (hsPrimitiveTypeDecl $1) $2 }
  -- Old FFI
  | 'foreign' 'import' var '::' type          { hsPrimitiveBind $1 $3 $5 }
  -- FFI, see http://www.cse.unsw.edu.au/~chak/haskell/ffi/
  | 'foreign' 'import' callconv var '::' type { hsPrimitiveBind $1 $4 $6 }
  | 'foreign' 'import' callconv safety var '::' type { hsPrimitiveBind $1 $5 $7 }
  | 'foreign' 'import' callconv impent var '::' type { hsPrimitiveBind $1 $5 $7 }
  | 'foreign' 'import' callconv safety impent var '::' type { hsPrimitiveBind $1 $6 $8 }

callconv :: { HsName }
         : varid        { $1 }

safety   :: { HsName }
          : varid        { $1 }

impent 	 :: { String }
          : STRING       { snd $1 }

optfundeps :: { HsFunDeps HsName }
	   :			 	{ [] }
	   | '|' fundeps		{ $2 }

fundeps	   :: { HsFunDeps HsName }
	   : fundep			{ [$1] }
	   | fundep ',' fundeps		{ $1:$3 }

fundep	   :: { HsFunDep HsName }
	   : tyvars '->' tyvars		{ ($1,$3) }

tyvars	   :: { [HsName] }
	   :				{ [] }
	   | tyvar tyvars		{ $1:$2 }

decls :: { [HsDecl] }
	: decls1 semis                  { reverse $1 }
	| semis                         { [] }

decls1 :: { [HsDecl] }
	: decls1 semis1 decl		{ funCons $3 $1 }
	| decl				{ [$1] }


decl :: { HsDecl }
        : gendecl                       { $1 }
        | valdef			{ $1 }
        -- Property declarations
	| assertion                     { $1 }
        | property_decl                 { $1 }

gendecl :: { HsDecl }
        : signdecl              { $1 }
        | fixitydecl            { $1 }

decllist :: { [HsDecl] }
	:  '{' decls '}'	{ $2 }
	| open decls close	{ $2 }

signdecl :: { HsDecl }
	: vars '::' ctype
	      { uncurry (hsTypeSig $2 (reverse $1)) $3 }
{-


ATTENTION: Dirty Hackery Ahead! If the second alternative of vars is var
instead of qvar, we get another shift/reduce-conflict. Consider the
following programs:

   { (+) :: ... }          A "signdecl" where everything to the left of the
                           :: is parsed as "vars" which should allow only var

   { (+) x y  = ... }      A "valdef" where everything to the left of the
                           = is parsed as an "exp0" which (incorrectly
                           in this context) allows a "qvar", since "exp0"
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
	| unqvar		{ [$1] }

unqvar	:: { HsName }
        : qvar			{% if isQualified $1
				   then fail "Qualified names not allowed here ."
				   else return $1
				}

{-

-----------------------------------------------------------------------------
Types

-}
type :: { HsType }
	: btype '->' type           { hsTyFun $1 $3 }
	| btype         %prec '->'  { $1 }
        -- higher rank poly extension: -------------------
        | 'forall' tyvars '.' ctype { uncurry (hsTyForall $2) $4 }

btype :: { HsType }
        : btype atype   %prec '->'  { hsTyApp $1 $2 }
        | atype                     { $1 }

atype :: { HsType }
	: gtycon			{ hsTyCon $1 }
	| tyvar				{ hsTyVar $1 }
	| '[' type ']'			{ hsTyApp (list_tycon $1) $2 }
	| '(' types ')'			{ case $2 of
					    [t] -> t
					    ts -> hsTyTuple $1 ts }

opttypes :: { [HsType] }
	 :			   { [] }
	 | types		   { $1 }


types	:: { [HsType] }
	: type ',' types	   { $1 : $3 }
	| type	                   { [$1] }

gtycon :: { HsName }
	: qtycon			{ $1 }
	| '(' ')'			{ unit_tycon_name $1 }
	| '[' ']'			{ list_tycon_name $1 }
	| '(' '->' ')'	                { fun_tycon_name $1 }
	| '(' commas ')'		{ tuple_tycon_name $2 $1 }
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
	: context '=>' type      { ($1, $3) }
	| type		       { ([], $1) }

context :: { [HsType] }
	: btype		       { tupleTypeToContext $1 }


simpletype :: { HsType }
	: tycon tyvars         { foldl1 hsTyApp (hsTyCon $1:map hsTyVar $2) }

ctyconparams :: { ([HsType], HsType) }
        : ctype                {% chkTypeLhs $1 }

{-
ctyconparams :: { ([HsType], [HsType]) }
--	: type '=>' tyconparams     { (reverse (tupleTypeToContext $1), $3) }
	: tyconparams               { ([], $1) }

-- Replacing tycon with gtycon as an experiment: /TH
tyconparams :: { [HsType] }
        : gtycon typarams           { hsTyCon $1 : reverse $2 }
--	| gtycon		    { [hsTyCon $1] }

typarams :: { [HsType] }
	: typarams tyvar            { hsTyVar $2 : $1 }
	|			    { [] }
-}
{-
ctybinding :: { ([HsType], HsName) }
	: ctyconparams  {% case snd $1 of
		             Typ (HsTyCon nm) -> return (fst $1,nm)
			     _ -> fail "Primitive types are not allowed to have parameters" }
-}


--- Datatype declarations ------------------------------------------------------

constrs :: { [HsConDecl HsType [HsType]] }
	: constrs '|' constr		{ $3 : $1 }
	| constr			{ [$1] }

-- Constructor with (optional) existential quantification:
constr :: { HsConDecl HsType [HsType] }
	: srcloc existq plain_constr	           { $3 $1 $2 [] }
	| srcloc existq context '=>' plain_constr  { $5 $1 $2 $3 }

-- Extension for existentially quantified types (with GHC compatible syntax):
existq :: { [HsName] }
       :				   { [] }
       | 'forall' tyvars '.'               { $2 }

plain_constr :: { SrcLoc -> [HsName] -> [HsType] -> HsConDecl HsType [HsType] }
	: scontype	         { conD $1 }
	| sbtype conop sbtype    { conD ($2,[$1,$3]) }
	| con '{' fielddecls '}' { fconD $1 (reverse $3) }

scontype :: { (HsName, [HsBangType HsType]) }
	: btype			    {% do { (c, ts) <- splitTyConApp $1 ;
					    return (c, map HsUnBangedType ts)
					  }
				    }
	| scontype1		        { $1 }
        | '(' consym ')' satype satype  { ($2,[$4,$5]) }

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

--- Class declarations ---------------------------------------------------------

optcbody :: { [HsDecl] }
	: 'where'  '{' cdecls '}'		{ $3 }
	| 'where' open cdecls close		{ $3 }
	| {- empty -}				{ [] }

cdecls :: { [HsDecl] }
	:                                       { [] }
	| cdecls1                               { reverse $1 }

cdecls1 :: { [HsDecl] }
	: cdecl                                 { [$1] }
	| cdecls1 semis1 cdecl                     { funCons $3 $1 }

cdecl :: { HsDecl }
      : decl                                    { $1 }
         {- except that pattern bindings aren't allowed! -}


--- Instance declarations ------------------------------------------------------

optibody :: { [HsDecl] }
	: 'where'  '{' idecls '}'	{ $3 }
	| 'where' open idecls close	{ $3 }
	| {- empty -}			{ [] }

idecls :: { [HsDecl] }
	:                                       { [] }
	| idecls1                               { reverse $1 }

idecls1 :: { [HsDecl] }
	: idecl                                 { [$1] }
	| idecls1 semis1 idecl                     { funCons $3 $1 }

idecl :: { HsDecl }
	: valdef	       	                { $1 }

{-

-----------------------------------------------------------------------------
Value definitions

-}

{-
valdef :: { HsDecl }
	: exp0 srcloc rhs optwheredecls
				    {% if isPatternExp $1 
                                       then mkValDef $1 $2 $3 $4
                                       else mkFunDef $1 $2 $3 $4
				    }
-}

valdef :: { HsDecl }
	: funlhs srcloc rhs optwheredecls   { mkFunDef' $1 $2 $3 $4 }
        | pat0 srcloc rhs optwheredecls { hsPatBind $2 $1 $3 $4 }

funlhs :: { (HsName,[HsPat]) }
        : qvar apats1               { ($1,$2) }
        | pat0 qvarop pat0          { ($2,[$1,$3]) }
        | '(' funlhs ')' apats1     { (fst $2,snd $2++$4) }
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
	: '|' exp '=' exp    { ($1, $2, $4) }

{-

-----------------------------------------------------------------------------
Expressions

-}
exp   :: { HsExp }
	: exp0 '::' ctype      	{ hsExpTypeSig $2 $1 (fst $3) (snd $3) }
        | exp0	     %prec '::' { $1 }

exp0 :: { HsExp }
	: exp0 qop exp0     %prec VARSYM { hsInfixApp $1 $2 $3 }
	| '\\' apats '->' exp            { hsLambda $2 $4 }
  	| 'let' decllist 'in' exp	 { hsLet $2 $4 }
	| 'if' exp 'then' exp 'else' exp { hsIf $2 $4 $6 }
   	| 'case' exp 'of' altslist	 { hsCase $2 $4 } 
	| '-' fexp			 { hsNegApp $1 $2 }
  	| 'do' stmtlist			 {% hsDo `fmap` atoms2Stmt $2 }
	| fexp				 { $1 }

fexp :: { HsExp }
	: fexp aexp			{ hsApp $1 $2 }
  	| aexp				{ $1 }

{-+
Note: The first alternative of aexp is not neccessarily a record update, it
could be a labeled construction, too.
-}
aexp	:: { HsExp }
  	: aexp '{' fbinds '}'        { mkRecord $2 $1 (reverse $3) }
  	| aexp1			     { $1 }

aexp1	:: { HsExp }
	: qvar			     { hsEVar ($1 :: HsName) }
	| gcon			     { $1 }
  	| literal		     { uncurry hsLit $1 }
--	| '(' exp ')'		     { hsParen $2 }
	| '(' exps ')'		     { case $2 of
                                         [e] -> hsParen e
				         es -> hsTuple es }
	| '[' list ']'               { $2 }
	| '(' exp0 qop ')'	     { hsLeftSection $2 $3 }
	| '(' qopm exp0 ')'	     { hsRightSection $2 $3 }
{-
	| '(' qvar '=' ')'	     { undefined {- record update -} }
	| '(' qvar '=' exp ')'	     { undefined {- record update -} }
-}
	| qvar '@' aexp	             { hsAsPat $1 $3 }
	| '_'			     { hsWildCard }
	| '~' aexp1		     { hsIrrPat $2 }

commas :: { Int }
	: commas ','		     { $1 + 1 }
	| ','			     { 1 }

exps :: { [HsExp] }
	: exp ',' exps		     { $1 : $3 }
	| exp		             { [$1] }

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
          {% hsListComp `fmap` atoms2Stmt (reverse $3 ++ [HsQualifierAtom $1]) }

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
	: exp0 '<-' exp	                {% do { p <- expToPat $1 ; 
                                                return (HsGeneratorAtom $2 p $3)
					      }
					}
	| exp			  	{ HsQualifierAtom $1 }
  	| 'let' decllist		{ HsLetStmtAtom   $2 }

{-

-----------------------------------------------------------------------------
Case alternatives

-}
altslist :: { [HsAlt HsExp HsPat [HsDecl]] }
	: '{'   alts semis '}'	  { reverse $2 }
	| open  alts semis close  { reverse $2 }


alts :: { [HsAlt HsExp HsPat [HsDecl]] }
	: alts semis1 alt			{ $3 : $1 }
	| alt					{ [$1] }

alt :: { HsAlt HsExp HsPat [HsDecl] }
	: pat0 srcloc rhscasealts { HsAlt $2 $1 $3 [] }
	      {-% do { p <- expToPat $1 ;
	              return (HsAlt $2 p $3 [])
		    }
	      -} 
        | pat0 srcloc rhscasealts 'where' decllist { HsAlt $2 $1 $3 $5 }
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
	: '|' exp  '->' exp          { ($1, $2, $4) }

{-

-----------------------------------------------------------------------------
Statement sequences

-}
stmtlist :: { [HsStmtAtom HsExp HsPat [HsDecl]] }
	:   '{' stmts '}'	{ $2 }
	| open  stmts close	{ $2 }

stmts :: { [HsStmtAtom HsExp HsPat [HsDecl]] }
  	:  qual semis1 stmts  	      { $1 : $3 }
        | semis1 stmts                   { $2 }
        | qual			      { [$1] }
        | qual semis1		      { [$1] }

--- Record Field Update/Construction -------------------------------------------

fbinds :: { [HsField HsExp] }
	  :				{ [] }
	  | fbinds1			{ $1 }

fbinds1 :: { [HsField HsExp] }
	: fbinds1 ',' fbind		{ $3 : $1 }
	| fbind				{ [$1] }

fbind	:: { HsField HsExp }
	: qvar '=' exp			{ HsField $1 $3 }
--	| qvar				{ HsFieldBind $1 }

--- Patterns -------------------------------------------------------------------

pat :: { HsPat }
        : pat0                { $1 }
        | qvar '+' integer    { let (s,i) = $3 in hsPSucc s $1 i }

pat0 :: { HsPat }
	: pat10                   { $1 }
	| pat0 qconop pat10   { hsPInfixApp $1 $2 $3 }

pat10 :: { HsPat }
        : qcon apats1             { hsPApp $1 $2 } -- should be gcon...
	| '-' numlit		  { hsPNeg $1 (snd $2) }
        | apat                    { $1 }

apat :: { HsPat }
        : qvar                    { hsPVar $1 }
        | qvar '@' apat           { hsPAsPat $1 $3 }
        | qcon                    { hsPCon $1 } -- should be gcon...
	| '(' ')'                 { hsPCon (qunit $1) }
        | qcon '{' fpats '}'      { hsPRec $1 $3 }
        | literal                 { uncurry hsPLit $1 }
        | '_'                     { hsPWildCard }
	| '(' pat ')'             { hsPParen $2 }
	| '(' tpats ')'           { hsPTuple $1 $2 }
	| '[' lpats ']'           { hsPList $1 $2 }
        | '~' apat                { hsPIrrPat $2 }

apats1 :: { [HsPat] }
        : apat apats              { $1 : $2 }

apats :: { [HsPat] }
	:                         { [] }
	| apat apats              { $1 : $2 }

fpats :: { [HsField HsPat] }
        :                         { [] }
        | fpats1                  { $1 }

fpats1 :: { [HsField HsPat] }
        : fpat ',' fpats1         { $1 : $3 }
	| fpat                    { [$1] }

fpat :: { HsField HsPat }
        : qvar '=' pat            { HsField $1 $3 }

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
	: '[' ']'		     { hsList [] }
        | tupcon		     { hsECon $1 }
  	| qcon			     { hsECon $1 }

tupcon :: { HsName }
        : '(' ')'		     { qunit $1 }
	| '(' commas ')'	     { qtuple $2 $1 }

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
	| '(' gconsym ')'	{ $2 }

varop	:: { HsName }
	: varsym		{ $1 }
	| '`' varid '`'		{ $2 }

qvarop :: { HsName }
	: qvarsym		{ $1 }
	| '`' qvarid '`'	{ $2 }

qvaropm :: { HsName }
	: qvarsymm		{ $1 }
	| '`' qvarid '`'	{ $2 }

conop :: { HsName }
	: consym		{ $1 }	
	| '`' conid '`'		{ $2 }

qconop :: { HsName }
	: gconsym		{ $1 }
	| '`' qconid '`'	{ $2 }

op	:: { HsIdent }
	: varop			{ hsVar $1 }
	| conop 		{ hsCon $1 }

qop	:: { HsIdent }
	: qvarop		{ hsVar $1 }
	| qconop		{ hsCon $1 }

gconsym :: { HsName }
	: qconsym		{ $1 }

qopm	:: { HsIdent }
	: qvaropm		{ hsVar $1 }
	| qconop		{ hsCon $1 }

qvarid :: { HsName }
	: varid			{ $1 }
	| QVARID		{ qualid $1 }

varid1 :: { HsName }
	: VARID			{ unqualid $1 }
	| 'as'			{ unqualid ($1,"as") }
	| 'qualified'           { unqualid ($1,"qualified") }
	| 'hiding'		{ unqualid ($1,"hiding") }
        | 'foreign'	        { unqualid ($1,"foreign") }
--      | 'primitive'	        { unqualid ($1,"primitive") }

varid :: { HsName }
        : varid1                { $1 }
        | 'forall'	        { unqualid ($1,"forall") }
    

qconid :: { HsName }
	: conid			{ $1 }
        | QCONID		{ qualid $1 }

qtycon :: { HsName }
	: tycon			{ $1 }
	| QCONID		{ qualid $1 }

conid :: { HsName }
	: CONID			{ unqualid $1 }
        | 'Gfp'                 { unqualid ($1,"Gfp") }
        | 'Lfp'                 { unqualid ($1,"Lfp") }
        | 'All'                 { unqualid ($1,"All") }
        | 'Exist'               { unqualid ($1,"Exist") }

qconsym :: { HsName }
	: consym		{ $1 }
	| QCONSYM		{ qualid $1 }

consym :: { HsName }
	: CONSYM		{ unqualid $1 }
	| ':'			{ unqualid ($1,":") }
	 -- ':' should really be part fo gconsym...
        | ':::'                 { unqualid ($1,":::") }

qvarsym :: { HsName }
	: varsym		{ $1 }
	| qvarsym1		{ $1 }

qvarsymm :: { HsName }
	: varsymm		{ $1 }
	| qvarsym1		{ $1 }

varsym :: { HsName }
	: '-'			{ unqualid ($1,"-") }
	| varsymm		{ $1 }

varsymm :: { HsName } -- varsym not including '-'
	: VARSYM		{ unqualid $1 }
        | '+'                   { unqualid ($1,"+") }
	| '!'			{ unqualid ($1,"!") }
        | '.'                   { unqualid ($1,".") }
        | '$'                   { unqualid ($1,"$") }
        | '-/'                  { unqualid ($1,"-/") }
        | '/\\'                 { unqualid ($1,"/\\") }
        | '\\/'                 { unqualid ($1,"\\/") }
        | '==='                 { unqualid ($1,"===") }
        | '=/='                 { unqualid ($1,"=/=") }
        | '==>'                 { unqualid ($1,"==>") }
        | '<==>'                { unqualid ($1,"<==>") }

qvarsym1 :: { HsName }
	: QVARSYM		{ qualid $1 }

literal :: { (SrcLoc,HsLiteral) }
	: numlit		{ $1 }
	| CHAR 			{ (fst $1,HsChar (read (snd $1))) }
	| STRING		{ (fst $1,HsString (read (snd $1))) }

numlit :: { (SrcLoc,HsLiteral) }
        : integer      	{ $1 }
	| float      	{ $1 }

integer :: { (SrcLoc,HsLiteral) }
	: INT	       	{ let (s,l)=$1 in (s,HsInt (readInteger l)) }


float :: { (SrcLoc,HsLiteral) }
	: RATIONAL	{ let (s,l)=$1 in (s,HsFrac (readRational l)) }

srcloc :: { SrcLoc }	:	{% getSrcLoc }

--- Layout ---------------------------------------------------------------------

open  :: { () }
       : VLCURLY		{ () }

close :: { () }
	: VRCURLY		{ () } -- context popped in lexer.
	| error			{% popContext }

--- Miscellaneous (mostly renamings) -------------------------------------------

modid :: { ModuleName }
	-- : CONID		{ Module (snd $1) }
	: qconid                {% hsName2modName $1 }

tyconorcls :: { HsName }
	: conid			{ $1 }

tycon :: { HsName }
	: conid			{ $1 }

qtyconorcls :: { HsName }
	: qtycon		{ $1 }

qtycls :: { HsName }
	: qtycon		{ $1 }

tyvar :: { HsName }
	: varid1		{ $1 }
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

assertion :: { HsDecl }
	: 'assert'           proposition      { hsAssertion $1 Nothing   $2 }
	| 'assert' conid '=' proposition      { hsAssertion $1 (Just $2) $4 }

proposition :: { Assertion }
        : prop                                      {% plogicAssertion $1 }

quantifier :: { Quantifier } 
	: 'All'                          { All }
        | 'Exist'                        { Exist }

optctype :: { Maybe HsQualType }
	:                                { Nothing }
	| '::' ctype                     { Just (uncurry (:=>) $2) }

prop :: { Plogic }
        : quantifier typedvars '.' prop %prec 'All'
				        { quants $1 $2 $4 }
        | '-/' prop                     { Neg $2 }
        | prop '/\\' prop               { Op Conj $1 $3 }
        | prop '\\/' prop               { Op Disj $1 $3 }
        | prop '==>' prop               { Op Imp $1 $3 }
        | prop '<==>' prop              { Op Equiv $1 $3 }
        | pexp '===' pexp               { Equal $1 $3 }
        | pexp '=/=' pexp               { Neg (Equal $1 $3) }
        | pexp ':::' prop               { Has $1 $3 }
        | pqcon predargs                { App $1 $2 }
        | aprop                          { $1 }
        | prop '->' prop                 { arrow $1 $3 }
        | prop qconop prop %prec '->'    { InfixApp $1 $2 $3 }
        | 'Lfp' conid '.' prop %prec 'Lfp'  { Lfp $2 $4 }
        | 'Gfp' conid '.' prop %prec 'Gfp'  { Gfp $2 $4 }

aprop :: { Plogic }
        : pqcon                         { App $1 [] }
        | '[' ']'                       { Nil }
	| '!' aexp1                     { Lifted $2 }
        | '$' aprop                     { Strong $2 }
        | '(' props ')'                 { case $2 of
					    [f] -> Paren f
					    fs -> predTuple fs $1
                                        }
        | '{' '|' typedpats '|' prop '|' '}' { Comp $3 $5 }

pexp :: { HsExp }
        : '{' exp '}'                   { $2 }
        | qvar                          { hsEVar $1 }
--      | pqcon                         { hsECon $1 } -- hmm, error prone...
	| literal		        { uncurry hsLit $1 }

typedvars :: { [(HsName,Maybe HsQualType)] }
        : var optctype                  { [($1,$2)] }
        | var optctype ',' typedvars    { ($1,$2):$4 }

{-
pexps :: { [HsExp] }
        : pexp                          { [$1] }
        | pexp pexps                    { $1:$2 }
-}
property_decl :: { HsDecl }
        : 'property' conid ids '=' prop {% propDecl $1 $2 $3 $5 }

ids :: { [HsIdent] }
        :                                  { [] }
        | var ids                        { HsVar $1:$2 }
        | con ids                        { HsCon $1:$2 }

predargs :: { [PredArg HsExp Plogic] }
        : predarg                       { [$1] }
        | predarg predargs              { $1:$2 }

predarg :: { PredArg HsExp Plogic }
	: '{' exp '}'			{ Left $2 }
        | qvar				{ Left (hsEVar $1) }
	| literal		        { Left (uncurry hsLit $1) }
        | aprop			{ Right $1 }

typedpats :: { [(HsPat,Maybe HsQualType)] }
      : pat optctype			{ [($1,$2)] }
      | pat optctype ',' typedpats	{ ($1,$2):$4 }


props :: { [Plogic] }
        : prop                      { [$1] }
        | prop ',' props         { $1:$3 }

-- In logical formulas, some special conids are reserved...
pqconid :: { HsName }
	: CONID			{ unqualid $1 }
        | QCONID		{ qualid $1 }
	| tupcon		{ $1 }

pqcon	:: { HsName }
	: pqconid		{ $1 }
	| '(' gconsym ')'	{ $2 }

----------------------------------------------------------------------------
{
predTuple fs pos = App (qtuple n pos)  (map Right fs)
  where n = length fs-1

conD (con,ts) s vs ctx = HsConDecl s vs ctx con ts
fconD con fs  s vs ctx  = HsRecDecl s vs ctx con fs

happyError = parseError "syntax error"

quants q [] p = p
quants q ((v,t):vts) p = P.Quant q v t (quants q vts p)
}
