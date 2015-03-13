
module Main (main) where


import IO
import Lexer
import ParseMonad
import PropParser
import ParseUtil
import Syntax
import PrettyPrint
import System
import GetOpt
import IOExts
import List
import Rewrite(rewriteDec)
import HsAssoc(initEnv, OperatorEnv)
import Prop2SVC(prop2SVC)


data Flag = LexOnlyLength          -- print number of tokens only
          | LexOnlyRev             -- print tokens in reverse order
          | LexOnly                -- print tokens
          | ParseLength            -- print number of declarations only
          | ParseInternal          -- print abstract syntax in internal format
          | ParsePretty PPLayout   -- pretty print in this style
          | ToHOL                  -- produces naive HOL version
          | TestStatic             -- test static checker
          | TestTypeCheck
          | ShowNames
          | Help                   -- give short usage info

usage = "usage: prop2hol [option] [filename]"

options =
   [ Option ['n']  ["numtokens"] (NoArg LexOnlyLength)
         "print number of tokens only",
     Option ['r']  ["revtokens"] (NoArg LexOnlyRev)
         "print tokens in reverse order",
     Option ['t']  ["tokens"]    (NoArg LexOnly)
         "print tokens",
     Option ['d']  ["numdecls"]  (NoArg ParseLength)
         "print number of declarations only",
     Option ['a']  ["abstract"]  (NoArg ParseInternal)
         "print abstract syntax in internal format",
     Option ['p']  ["pretty"]    (OptArg style "STYLE")
         "pretty print in STYLE[(o)ffside|(s)emicolon|(u)trecht|(i)nline|\
                    \(n)one] (default = offside)",
     Option ['h','?'] ["help"]   (NoArg Help)
         "display this help and exit",
     Option ['s'] ["static"] (NoArg TestStatic) 
         "run stattic checker",
     Option ['c'] ["typecheck"] (NoArg TestTypeCheck) "run typechecker",
     Option ['m'] ["names"]     (NoArg ShowNames)      "show all defined names"
   ]

style :: Maybe String -> Flag
style Nothing  = ToHOL
style (Just s) = ParsePretty $
         case s of
         "o"         -> PPOffsideRule
         "offside"   -> PPOffsideRule
         "s"         -> PPSemiColon
         "semicolon" -> PPSemiColon
         "u"         -> PPUtrecht
         "utrecht  " -> PPUtrecht
         "i"         -> PPInLine
         "inline"    -> PPInLine
         "n"         -> PPNoLayout
         "none"      -> PPNoLayout
         _           -> PPOffsideRule

main :: IO ()
main = do cmdline <- getArgs
          mainHugs cmdline

toSVC = mainHugs ["foo.hs"]

mainHugs :: [String] -> IO ()
mainHugs cmdline =
   case getOpt Permute options cmdline of
      (flags, args, [])    ->
       do (file, inp) <- case args of
			 []  -> do inp <- getContents
				   return ("stdio", inp)
			 [f] -> do inp <- readFile f
				   return (f, inp)
			 _   -> error usage
          putStrLn (handleFlag (getFlag flags) file inp)
      (    _,   _, errors) ->
        error (concat errors ++ usageInfo usage options)

getFlag :: [Flag] -> Flag
getFlag []  = ToHOL
getFlag [f] = f
getFlag _   = error usage

handleFlag :: Flag -> FilePath -> String -> String
handleFlag LexOnlyLength    f = show . numToks . testLexerRev f
handleFlag LexOnlyRev       f = show . testLexerRev f
handleFlag LexOnly          f = show . testLexer f
handleFlag ShowNames        f = 
    error "Main.handleFlag: name extraction not implemented yet."
-- show . getAllNames . testParser f
handleFlag ParseLength      f = show . allLengths . testParser f
   where allLengths (HsModule _ _ imp inf d) =
            length imp + length inf + length d
handleFlag ParseInternal    f = show . testParser f
handleFlag ToHOL            f = render . testProp2HOL f
handleFlag TestStatic       f =
    error "Main.handleFlag: static analysis test not implemented yet."
{-
handleFlag TestStatic       f = \s -> 
    unsafePerformIO $ 
    do { r <- testStatic $ testParser f s ;
         return "Done static checking." }
-}
handleFlag TestTypeCheck    f =
    error "Main.handleFlag: type check test not implemented yet."
{-
handleFlag TestTypeCheck    f = \s -> 
    unsafePerformIO $ 
    do  { let { m = testParser f s } ;
          r <- testStatic m ;
          print $ (typeCheckDecls . (\ (HsModule _ _ _ _ ds) -> ds)) m;
          return "Done static checking." }
-}
handleFlag (ParsePretty lo) f
    = renderWithMode mode . ppi . testParser f
      where mode = defaultMode { layoutType = lo }
handleFlag Help             f          
    = const $
      usageInfo
          ("A simple test program for *The Haskell Parser*" ++ usage)
      options

numToks :: ParseResult OperatorEnv [Token] -> Int
numToks (Ok _ toks)  = length toks
numToks (Failed err) = error ("Huh? " ++ err)

testLexerRev :: FilePath -> String -> ParseResult OperatorEnv [Token]
testLexerRev f s =
    (unPM $ loop []) s (SrcLoc f 1 0) 1 (error "Initial environment", []) 
    where loop toks =
	      lexer (\t -> case t of 
                           EOF -> returnPM toks
                           _   -> loop (t:toks))

testLexer :: FilePath -> String -> ParseResult OperatorEnv [Token]
testLexer f s = (unPM $ loop []) s  (SrcLoc f 1 0) 1 (initEnv, [])
  where loop toks =
         lexer (\t -> case t of 
              EOF -> returnPM (reverse toks) -- space leak?
              _   -> loop (t:toks))

testParser :: FilePath -> String -> HsModuleR
testParser f s =
    case (unPM parse) s  (SrcLoc f 1 1) 0 (initEnv, []) of
    Ok state (HsModule m ex im inf decls) ->
	(HsModule m ex im inf (map (rewriteDec initEnv) decls))
    Failed err -> error err

testProp2HOL f s = prop2SVC $ testParser f s

------------------------------------------------------------------------------
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

----------------------------------------------------------------------------
