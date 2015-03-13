-- $Id: Lexer.hs,v 1.11 2001/11/08 22:09:28 hallgren Exp $

{-

ToDo: Parsing floats is a *real* hack...
ToDo: FloatTok should have three parts (integer part, fraction, exponent)
ToDo: Use a lexical analyser generator (lx?)

Known bug: It seems that _x is a valid identifier name; our lexer, on the
other hand, produces two lexemes, the wildcard followed by x. Argh!!!!
e.p. FIXED e.p.

-}

module Lexer (Token(..), lexer, isSymbol) where


import ParseMonad
import LexUtil
import SrcLoc
import Char
import Ratio
--import IOExts(trace)
import Token


{-

The source location, (f, y, x), is the coordinates of the previous token.
col is the current column in the source file f.  If col is 0, we are
somewhere at the beginning of the line before the first token.

Setting col to 0 is used in two places: just after emitting a virtual
close brace due to layout, so that next time through we check whether
we also need to emit a semi-colon, and at the beginning of the file,
to kick off the lexer.

-}
lexer :: (Token -> PM a) -> PM a
lexer cont =
    PM $ \input (SrcLoc f y x) col ->
    if col == 0 then tab f y x   True  input  col
                else tab f y col False input  col -- throw away old x
    where
    -- move past whitespace and comments
    tab f y x bol []          col = (unPM $ cont EOF) [] (SrcLoc f y x) col
    tab f y x bol ('\t':s)    col = tab f y (nextTab x) bol s col
    tab f y x bol ('\n':s)    col = newLine f s y col
    tab f y x bol ('-':'-':s) col = newLine f (drop 1 (dropWhile (/= '\n') s))
				      y col
    tab f y x bol ('{':'-':s) col = nestedComment tab f y x bol s col
    tab f y x bol (c:s)       col
		 | isSpace c = tab f y (x + 1) bol s col
	         | otherwise =
		     if bol then
		         (unPM $ lexBOL cont)   (c:s) (SrcLoc f y x) x
		     else
		         (unPM $ lexToken cont) (c:s) (SrcLoc f y x) x

    newLine f s y col = tab f (y + 1) 1 True s col


nextTab x = x + (tab_length - (x - 1) `mod` tab_length)

{-

When we are lexing the first token of a line, check whether we need to
insert virtual semicolons or close braces due to layout.

-}
lexBOL :: (Token -> PM a) -> PM a
lexBOL cont =
    PM $ \ s loc@(SrcLoc f y x) col (state@ctx) ->
    if need_close_curly x ctx then 
        -- trace "layout: inserting '}'\n" $
	-- Set col to 0, indicating that we're still at the
	-- beginning of the line, in case we need a semi-colon too.
	-- Also pop the context here, so that we don't insert
	-- another close brace before the parser can pop it.
        (unPM $ cont VRightCurly) s loc 0 (tail ctx)
    else if need_semi_colon x ctx then
        -- trace "layout: inserting ';'\n" $
	(unPM $ cont SemiColon) s loc col state
    else
        (unPM $ lexToken cont)  s loc col state
    where
        need_close_curly x []    = False
	need_close_curly x (i:_) = case i of
				   NoLayout -> False
				   Layout n -> x < n

        need_semi_colon x []     = False
	need_semi_colon x (i:_)  = case i of
				   NoLayout -> False
				   Layout n -> x == n


lexToken :: (Token -> PM a) -> PM a
lexToken cont =
    PM lexToken'
    where
    lexToken' (c:s) loc@(SrcLoc f y x') x =
        -- trace ("lexer: y = " ++ show y ++ " x = " ++ show x ++ "\n") $ 
	case c of
	-- First the special symbols
        '(' -> special LeftParen
        ')' -> special RightParen
        ',' -> special Comma
        ';' -> special SemiColon
        '[' -> special LeftSquare
        ']' -> special RightSquare
        '`' -> special BackQuote
        '{' -> special LeftCurly . (NoLayout:) -- push context on '{'
        '}' -> \state ->
               case state of
               _:ctxt ->
	           special RightCurly ctxt -- pop context on '}'
               []       ->
		   (unPM $ parseError "parse error (possibly incorrect indentation)")
                   s loc x []

        '\'' -> (unPM $ lexChar cont)   s loc (x + 1)
        '\"' -> (unPM $ lexString cont) s loc (x + 1)


        c | isDigit c ->
	      case lexInt (c:s) of
	      Decimal (n, rest) ->
		  case rest of
		  ('.':c2:rest2) | isDigit c2 ->
				     case lexFloatRest (c2:rest2) of
				     Nothing -> (unPM $
						 parseError "illegal float.")
						s loc x
				     Just (n2,rest3) ->
					 let f = n ++ ('.':n2) in
				         forward (length f) (FloatTok f) rest3
		  _ -> forward (length n) (IntTok n) rest
	      Octal       (n,rest) -> forward (length n) (IntTok n) rest
	      Hexadecimal (n,rest) -> forward (length n) (IntTok n) rest

          | isLower_ c ->
	      let (vidtail, rest) = span isIdent s
		  vid             = c:vidtail
		  l_vid           = 1 + length vidtail
	      in
		  case lookup vid reserved_ids of
		  Just keyword -> forward l_vid keyword rest
		  Nothing      -> forward l_vid (VarId vid) rest

          | isUpper c ->
	      let (contail, rest) = span isIdent s
		  l_con           = 1 + length contail
		  con             = c:contail
	      in
		  case lookup con reserved_ids of
		  Just keyword -> forward l_con keyword rest
		  Nothing      -> lexQual l_con con rest
                                      (forward l_con (ConId con) rest)
		  
          | isSymbol c ->
	      let (symtail, rest) = span isSymbol s
		  sym             = c : symtail
		  l_sym           = 1 + length symtail
	      in
	          case lookup sym reserved_ops of
		  Just t  -> forward l_sym t rest
		  Nothing -> case c of
			     ':' -> forward l_sym (ConSym sym) rest
                             '.' | l_sym == 1 -> special Period
                                 | otherwise  ->
                                    forward l_sym (VarSym sym) rest
			     _   -> forward l_sym (VarSym sym) rest

          | otherwise ->
	      (unPM $
	       parseError ("illegal character \'" ++
			   showLitChar c "" ++ "\'\n"))
	      s loc x
		  
      where
      special t = forward 1 t s
      forward n t s = (unPM $ cont t) s loc (x + n)
 
      lexFloatRest r = case span isDigit r of
		       (r2, 'e':r3) -> lexFloatExp (r2 ++ "e") r3
		       (r2, 'E':r3) -> lexFloatExp (r2 ++ "e") r3
		       f@(r2,   r3) -> Just f
 
      lexFloatExp r1 ('-':r2) = lexFloatExp2 (r1 ++ "-") r2
      lexFloatExp r1 ('+':r2) = lexFloatExp2 (r1 ++ "+") r2
      lexFloatExp r1      r2  = lexFloatExp2 r1          r2

      lexFloatExp2 r1 r2 = case span isDigit r2 of
			   ("", _ ) -> Nothing
			   (ds, r3) -> Just (r1++ds,r3)

      lexQual l_mod mod s lexConId =
          case s of
          '.':c:rest
           | isLower c ->	-- qualified varid?
	       let (vidtail, rest1) = span isIdent rest
		   vid              = c:vidtail
		   l_vid            = 1 + length vidtail
	       in
	       case lookup vid reserved_ids of -- cannot qualify reserved word
	       Just keyword -> lexConId
	       Nothing      -> forward (l_mod + l_vid + 1) -- + 1 for the '.'
				       (QVarId (mod, vid)) rest1

           | isUpper c ->	-- qualified conid?
	       let (con1, rest1) = span isIdent rest
		   qcon          = c : con1
		   l_con1        = 1 + length con1
	       in
		   forward (l_mod + l_con1 + 1) -- + 1 for the '.'
			   (QConId (mod, qcon)) rest1

           | isSymbol c ->	-- qualified symbol?
               let (symtail, rest1) = span isSymbol rest    
		   sym              = c : symtail
		   l_sym            = 1 + length symtail
               in
	       case lookup sym reserved_ops of
	       -- cannot qualify a reserved operator
	       Just _  -> lexConId
	       Nothing ->
		   case c of
	           ':' -> forward (l_mod + l_sym + 1) -- + 1 for the '.'
			          (QConSym (mod, sym)) rest1
		   _   -> forward (l_mod + l_sym + 1) -- + 1 for the '.'
			          (QVarSym (mod, sym)) rest1

           -- special case for M.[]; allows whitespace between '[' and ']'
	   -- (provided layout is not violated)
           | c == '[' ->
	       case snd $ span isSpace rest of
	       (']':_) -> forward l_mod (QModId mod) s
               _       -> lexConId

           -- special case for M.(), M.(,,,), etc.; allows whitespace between
	   -- '(' and ')', and '(' and ',' (provided layout is not violated)
           | c == '(' ->
	       case snd $ span isSpace rest of
	       (')':_) -> forward l_mod (QModId mod) s
               (',':_) -> forward l_mod (QModId mod) s
	       _       -> lexConId

	  _ -> lexConId -- not a qualified object
			      
    lexToken' _  _ _ =
	error "Lexer.lexToken: Internal error: empty input stream."


lexInt ('0':o:d:r) | toLower o == 'o' && isOctDigit d
    = let (ds, rs) = span isOctDigit r
      in
           Octal       ('0':'o':d:ds, rs)
lexInt ('0':x:d:r) | toLower x == 'x' && isHexDigit d
    = let (ds, rs) = span isHexDigit r
      in 
           Hexadecimal ('0':'x':d:ds, rs)
lexInt r = Decimal     (span isDigit r)


lexChar :: (Token -> PM a) -> PM a
lexChar cont = PM lexChar'
    where
    lexChar' s loc x =
	case s of
	'\\':s ->
	    let (e, s2, i) =
		  runPM (escapeChar s) "" loc x []
	    in
                charEnd e s2 loc (x + i)
	c:s  -> charEnd c s  loc (x + 1)
	[]   -> error "Lexer.lexChar: Internal error: empty list."

    charEnd c ('\'':s)   =
	\loc x -> (unPM $ cont (Character c)) s loc (x + 1)
    charEnd c s         =
	(unPM $ parseError "improperly terminated character constant.") s 


lexString :: (Token -> PM a) -> PM a
lexString cont = PM lexString'
    where
    lexString' s loc@(SrcLoc f y _) x = loop "" s x y
	where
	loop e s x y =
	    case s of
            '\\':'&':s  -> loop e s (x+2) y
	    '\\':c:s | isSpace c -> stringGap e s (x + 2) y
		     | otherwise ->
			 let (e', sr, i) =
			       runPM (escapeChar (c:s)) ""  loc x []
                         in  loop (e':e) sr (x+i) y
            '\"':s{-"-} -> (unPM $ cont (StringTok (reverse e))) s  loc (x + 1)
	    c:s	      -> loop (c:e) s (x + 1) y
	    []          -> (unPM $ parseError "improperly terminated string.")
			            s  loc x

	stringGap e s x y =
	    case s of
		'\n':s -> stringGap e s 1 (y + 1)
	        '\\':s -> loop e s (x + 1) y
	        c:s' | isSpace c -> stringGap e s' (x + 1) y
	             | otherwise ->
			 (unPM $ parseError "illegal character in string gap.")
			 s  loc x
	        []     -> error "Lexer.stringGap: Internal error: empty list."


escapeChar :: String -> PM (Char, String, Int)
escapeChar s = case s of
    -- Production charesc from section B.2 (Note: \& is handled by caller)
   'a':s 	 -> return ('\a', s, 2)
   'b':s 	 -> return ('\b', s, 2)
   'f':s 	 -> return ('\f', s, 2)
   'n':s 	 -> return ('\n', s, 2)
   'r':s 	 -> return ('\r', s, 2)
   't':s 	 -> return ('\t', s, 2)
   'v':s 	 -> return ('\v', s, 2)
   '\\':s        -> return ('\\', s, 2)
   '"':s         -> return ('\"', s, 2)
   '\'':s        -> return ('\'', s, 2)

    -- Production ascii from section B.2
   '^':x@(c:s)   -> cntrl x
   'N':'U':'L':s -> return ('\NUL', s, 4)
   'S':'O':'H':s -> return ('\SOH', s, 4)
   'S':'T':'X':s -> return ('\STX', s, 4)
   'E':'T':'X':s -> return ('\ETX', s, 4)
   'E':'O':'T':s -> return ('\EOT', s, 4)
   'E':'N':'Q':s -> return ('\ENQ', s, 4)
   'A':'C':'K':s -> return ('\ACK', s, 4)
   'B':'E':'L':s -> return ('\BEL', s, 4)
   'B':'S':s     -> return ('\BS',  s, 3)
   'H':'T':s  	 -> return ('\HT',  s, 3)
   'L':'F':s 	 -> return ('\LF',  s, 3)
   'V':'T':s 	 -> return ('\VT',  s, 3)
   'F':'F':s 	 -> return ('\FF',  s, 3)
   'C':'R':s 	 -> return ('\CR',  s, 3)
   'S':'O':s 	 -> return ('\SO',  s, 3)
   'S':'I':s 	 -> return ('\SI',  s, 3)
   'D':'L':'E':s -> return ('\DLE', s, 4)
   'D':'C':'1':s -> return ('\DC1', s, 4)
   'D':'C':'2':s -> return ('\DC2', s, 4)
   'D':'C':'3':s -> return ('\DC3', s, 4)
   'D':'C':'4':s -> return ('\DC4', s, 4)
   'N':'A':'K':s -> return ('\NAK', s, 4)
   'S':'Y':'N':s -> return ('\SYN', s, 4)
   'E':'T':'B':s -> return ('\ETB', s, 4)
   'C':'A':'N':s -> return ('\CAN', s, 4)
   'E':'M':s     -> return ('\EM',  s, 3)
   'S':'U':'B':s -> return ('\SUB', s, 4)
   'E':'S':'C':s -> return ('\ESC', s, 4)
   'F':'S':s     -> return ('\FS',  s, 3)
   'G':'S':s     -> return ('\GS',  s, 3)
   'R':'S':s     -> return ('\RS',  s, 3)
   'U':'S':s     -> return ('\US',  s, 3)
   'S':'P':s     -> return ('\SP',  s, 3)
   'D':'E':'L':s -> return ('\DEL', s, 4)


   -- Depending upon the compiler/interpreter's Char type, these yield either
   -- just 8-bit ISO-8859-1 or 2^16 UniCode.  The report says it should be the
   -- latter.

   -- Octal representation of a character
   'o':s           -> let (ds, s') = span isOctDigit s
			  n        = readNumber 8 ds
                      in 
		          numberToChar n s' (length ds + 1)

   -- Hexadecimal representation of a character
   'x':s           -> let (ds, s') = span isHexDigit s
			  n        = readNumber 16 ds
                      in
		          numberToChar n s' (length ds + 1)
 
   -- Base 10 representation of a charactef
   d:s | isDigit d -> let (ds, s') = span isDigit s
			  n        = readNumber 10 (d:ds)
                      in 
		          numberToChar n s' (length ds + 1)

   _               -> parseError "illegal escape sequence."

   where numberToChar n s l_n =
	     if toInteger (fromEnum (minBound :: Char))<=n &&
		n <= toInteger (fromEnum (maxBound :: Char))
	     then return (chr $ fromInteger n, s, l_n)
	     else parseError $ "illegal character literal (number "++
			       show n++" out of range)."
            
{-

Production cntrl from section B.2

-}
cntrl :: String -> PM (Char, String, Int)
cntrl (c   :s) | isUpper c = return (chr (ord c - ord 'A'), s, 2)
cntrl ('@' :s)             = return ('\^@', s, 2)
cntrl ('[' :s)             = return ('\^[', s, 2)
cntrl ('\\':s)             = return ('\^\', s, 2)
cntrl (']' :s)             = return ('\^]', s, 2)
cntrl ('^' :s)             = return ('\^^', s, 2)
cntrl ('_' :s)             = return ('\^_', s, 2)
cntrl _                    = parseError "illegal control character"


nestedComment cont f y x bol s  col =
    case s of
    '-':'}':s -> cont f y (x + 2) bol s  col
    '{':'-':s -> nestedComment (nestedComment cont) f y (x + 2) bol s  col
    '\t':s    -> nestedComment cont f y (nextTab x) bol s  col
    '\n':s    -> nestedComment cont f (y + 1) 1 True s  col
    c:s       -> nestedComment cont f y (x + 1) bol s  col
    []        -> error "Lexer.nestedComment: Internal error: empty list."


{-
getTokens 0       = return []
getTokens (n + 1) = lexer (\t -> do { l <- getTokens n
			            ; return (t:l)
				    }
			  )

tokens f s =
    (unPM $ getTokens (length s)) s (SrcLoc f 0 0) 0
        (error "Lexer.tokens: problem with initial infix environment.", [])

-}

{-
instance Printable Token where
    ppi (VarId v)        = text v
    ppi (QVarId (m, v))  = text m <> '.' <> text v
    ppi (ConId c)        = text c
    ppi (QConId (m, c))  = text m <> '.' <> text c
    ppi (VarSym v)       = text v
    ppi (ConSym c)       = text c
    ppi (QVarSym (m, v)) = text m <> '.' <> text v
    ppi (QConSym (m, c)) = text m <> '.' <> text c
    ppi (QModId m)       = text m
    ppi (IntTok i)       = text i
    ppi (FloatTok f)     = text f
    ppi (Character ch)   = char ch
    ppi (StringTok s)    = text s

    ppi LeftParen    = lparen
    ppi RightParen   = rparen
    ppi SemiColon    = semi
    ppi LeftCurly    = lcurly
    ppi RightCurly   = rcurly
    ppi VRightCurly  = text "virtual" <+> rcurly
    ppi LeftSquare   = lbrack
    ppi RightSquare  = rbrack
    ppi Comma        = comma
    ppi Underscore   = char '_'
    ppi BackQuote    = backQuote
    ppi Period       = char '.'

    ppi DotDot       = text ".."
    ppi DoubleColon  = text "::"
    ppi Equals       = text "=="
    ppi Backslash    = char '\\'
    ppi Bar          = char '|'
    ppi LeftArrow    = text "<-"
    ppi RightArrow   = text "->"
    ppi At           = char'@'
    ppi Tilde        = char '~'
    ppi DoubleArrow  = text "=>"
    ppi Minus        = char '-'
    ppi Exclamation  = char '!'

    ppi KW_As        = text "as"
    ppi KW_Case      = text "case"     
    ppi KW_Class     = text "class"    
    ppi KW_Data      = text "data"     
    ppi KW_Default   = text "default"  
    ppi KW_Deriving  = text "deriving" 
    ppi KW_Do        = text "do"       
    ppi KW_Else      = text "else"     
    ppi KW_If        = text "if"       
    ppi KW_Import    = text "import"   
    ppi KW_In        = text "in"       
    ppi KW_Infix     = text "infix"    
    ppi KW_InfixL    = text "infixl"   
    ppi KW_InfixR    = text "infixr"   
    ppi KW_Instance  = text "instance" 
    ppi KW_Let       = text "let"      
    ppi KW_Module    = text "module"   
    ppi KW_NewType   = text "newtype"  
    ppi KW_Of        = text "of"       
    ppi KW_Then      = text "then"     
    ppi KW_Type      = text "type"     
    ppi KW_Where     = text "where"    
    ppi KW_Qualified = text "qualified"
    ppi KW_Hiding    = text "hiding"
    ppi KW_Primitive = text "primitive"

    ppi KW_Property  = text "property"
    ppi KW_QAll      = text "All"
    ppi KW_QExists   = text "Ex"
    ppi KW_QAllDef   = text "AllDef"

    ppi EOF = text "EOF"
-}
