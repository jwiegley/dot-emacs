-- $Id: Token.hs,v 1.2 2001/07/25 22:53:06 hallgren Exp $

module Token(Token(..),
             IntKind(..),
             reserved_ids,
             reserved_ops,
             tab_length)

where


data Token 
    = VarId String
    | QVarId (String, String)
    | ConId String
    | QConId (String, String)
    | VarSym String
    | ConSym String
    | QVarSym (String, String)
    | QConSym (String, String)
    | QModId String -- special case hack for M.(,,,).  The token QModId
                    -- holds the M, and the '.' and the list/tupe constructors
                    -- follow tokenized.  Must be matched in the grammar.
		    -- This isn't used for M.[N], since that must parse as
		    -- M . [N], most likely ending in an error.
    | IntTok String
    | FloatTok String
    | Character Char
    | StringTok String
{-

Symbols

-}
    | LeftParen
    | RightParen
    | SemiColon
    | LeftCurly
    | RightCurly
    | VRightCurly			-- a virtual close brace
    | LeftSquare
    | RightSquare
    | Comma
    | Underscore
    | BackQuote
    | Period                            -- needed for properties
{-

Reserved operators

-}
    | DotDot
    | DoubleColon
    | Equals
    | Backslash
    | Bar
    | LeftArrow
    | RightArrow
    | At
    | Tilde
    | DoubleArrow
    | Minus
    | Exclamation
{-

Reserved Ids

-}
    | KW_As       
    | KW_Case     
    | KW_Class    
    | KW_Data     
    | KW_Default  
    | KW_Deriving 
    | KW_Do       
    | KW_Else     
    | KW_Hiding
    | KW_If       
    | KW_Import   
    | KW_In       
    | KW_Infix    
    | KW_InfixL   
    | KW_InfixR   
    | KW_Instance 
    | KW_Let      
    | KW_Module   
    | KW_NewType  
    | KW_Of       
    | KW_Then     
    | KW_Type     
    | KW_Where    
    | KW_Qualified
    | KW_Primitive
    -- Keywords for Properties
    | KW_Property
    | KW_QAll
    | KW_QExists
    | KW_QAllDef
    | KW_QExistsU 
    | EOF
      deriving (Eq, Show)


reserved_ops :: [(String, Token)]
reserved_ops
    = [
        ( "..", DotDot ),    
	( "::", DoubleColon ),
	( "=",  Equals ),    
	( "\\", Backslash ), 
	( "|",  Bar ),       
	( "<-", LeftArrow ), 
	( "->", RightArrow ),
	( "@",  At ),        
	( "~",  Tilde ),     
	( "=>", DoubleArrow ),
--	( "-",  Minus ),	-- ToDo: shouldn't be here
	( "!",  Exclamation )	-- ditto
      ]


reserved_ids :: [(String, Token)]
reserved_ids
    = [
	( "as",        KW_As ),       
        ( "case",      KW_Case ),     
	( "class",     KW_Class ),    
	( "data",      KW_Data ),     
	( "default",   KW_Default ),  
	( "deriving",  KW_Deriving ), 
	( "do",        KW_Do ),       
	( "else",      KW_Else ),     
	( "if",        KW_If ),       
	( "import",    KW_Import ),   
	( "in",        KW_In ),       
	( "infix",     KW_Infix ),    
	( "infixl",    KW_InfixL ),   
	( "infixr",    KW_InfixR ),   
	( "instance",  KW_Instance ), 
	( "let",       KW_Let ),      
	( "module",    KW_Module ),   
	( "newtype",   KW_NewType ),  
	( "of",        KW_Of ),       
	( "then",      KW_Then ),     
	( "type",      KW_Type ),     
	( "where",     KW_Where ),    
	( "qualified", KW_Qualified ),
	( "hiding",    KW_Hiding ),
	( "primitive", KW_Primitive ),
        -- Keywords for Properties
        ( "property",  KW_Property ),
	( "All",       KW_QAll ),
        ( "Ex",        KW_QExists ),
        ( "AllDef",    KW_QAllDef ),
        ( "ExU",       KW_QExistsU )
      ]


data IntKind
    = Decimal     (String, String)
    | Octal       (String, String)
    | Hexadecimal (String, String)


tab_length = 8 :: Int
