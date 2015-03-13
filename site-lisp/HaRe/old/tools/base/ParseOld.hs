-- $Id: ParseOld.hs,v 1.4 2001/11/09 00:47:50 hallgren Exp $

-- Currently a test harness for the lexer/parser/pretty printer.

--ToDo: Are initial values for SrcLoc/current column correct?

import IO
import Monad
import Lexer
import ParseMonad
import HsParser
import ParseUtil
import Syntax
import PrettyPrint
import System
import GetOpt
import IOExts
import List
--import Rewrite(rewriteModule)
--import HsAssoc(initEnv, OperatorEnv)
import HsAssocInitEnv


data Flag = LexOnlyLength          -- print number of tokens only
          | LexOnlyRev             -- print tokens in reverse order
          | LexOnly                -- print tokens
          | ParseLength            -- print number of declarations only
          | ParseInternal          -- print abstract syntax in internal format
          | ParsePretty PPLayout   -- pretty print in this style
--        | TestStatic             -- test static checker
--        | TestTypeCheck
--        | ShowNames
          | Help                   -- give short usage info
--        | BindingGroupTest


usage = "usage: hsparser [option] [filename]"

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
         "display this help and exit"
--   Option ['s'] ["static"]     (NoArg TestStatic) 
--       "run stattic checker",
--   Option ['c'] ["typecheck"]  (NoArg TestTypeCheck)
--       "run typechecker",
--   Option ['m'] ["names"]      (NoArg ShowNames)
--       "show all defined names"
--   Option ['b'] ["groups"]     (NoArg BindingGroupTest)
--       "show binding groups"
   ]

style :: Maybe String -> Flag
style Nothing  = ParsePretty PPOffsideRule
style (Just s) = ParsePretty $
         case s of
         "o"         -> PPOffsideRule
         "offside"   -> PPOffsideRule
         "s"         -> PPSemiColon
         "semicolon" -> PPSemiColon
         "u"         -> PPUtrecht
         "utrecht"   -> PPUtrecht
         "i"         -> PPInLine
         "inline"    -> PPInLine
         "n"         -> PPNoLayout
         "none"      -> PPNoLayout
         _           -> PPOffsideRule

main :: IO ()
main = do cmdline <- getArgs
          mainHugs cmdline

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
getFlag []  = ParsePretty PPOffsideRule
getFlag [f] = f
getFlag _   = error usage

handleFlag :: Flag -> FilePath -> String -> String
handleFlag LexOnlyLength    f = show . numToks . testLexerRev f
handleFlag LexOnlyRev       f = show . testLexerRev f
handleFlag LexOnly          f = show . testLexer f
--handleFlag ShowNames        f = show . getAllNames . testParser f
handleFlag ParseLength      f = show . allLengths . testParser f
   where allLengths (HsModule _ _ imp ds) = length imp + length ds
handleFlag ParseInternal    f = show . testParser f
{-
handleFlag TestStatic       f = \s -> 
    unsafePerformIO $ 
    do { r <- testStatic $ testParser f s ;
         return "Done static checking." }
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
{-
handleFlag BindingGroupTest f = \s -> 
          unsafePerformIO (return groups >>= \s ->  return " Done b.g. ")
-}

handleFlag Help   f
    = const $
      usageInfo
          ("A simple test program for *The Haskell Parser*" ++ usage)
          options


numToks :: ParseResult [Token] -> Int
numToks (Ok _ toks)  = length toks
numToks (Failed err) = error ("Huh? " ++ err)

testLexerRev :: FilePath -> String -> ParseResult [Token]
testLexerRev f s =
    (unPM $ loop []) s (SrcLoc f 1 0) 1 []
    where loop toks =
           lexer (\t -> case t of 
                           EOF -> returnPM toks
                           _   -> loop (t:toks))

testLexer :: FilePath -> String -> ParseResult [Token]
testLexer f s = (unPM $ loop []) s  (SrcLoc f 1 0) 1 []
  where loop toks =
         lexer (\t -> case t of 
              EOF -> returnPM (reverse toks) -- space leak?
              _   -> loop (t:toks))

testParser :: FilePath -> String -> HsModuleR
testParser f s =
    case parseFile parse f s of
      Right mod -> {-rewriteModule initEnv-} mod
      Left err -> error err

start s = liftM (testParser s) (readFile s)

{-
start s = do contents <- readFile s
             return $ testParser s contents
-}

look s = unsafePerformIO $ start s
{-
myTestTypeCheck f s =
    do { let { m = testParser f s } ;
     r <- testStatic m ;
         return $ (typeCheckDs . (\ (HsModule _ _ _ _ ds) -> ds)) m
       } 



t22 x =
    unsafePerformIO $
    do { putStrLn "\nEnter Haskell declarations.  Terminate with :q \
          \on a single line\n" ;
     ls <- getLines [] ;
     myTestTypeCheck "Stdio" ls
       }

t34 x = 
    unsafePerformIO $ 
    do { putStrLn "\nEnter Haskell declarations.  Terminate with :q \
          \on a single line\n"
       ; text <- getLines []
       ; z @ (v, text, _) <- myTestTypeCheck "Stdio" text
       ; putStrLn "\n\n OUTPUT: \n"
       ; putStrLn text
       ; return v
       }

testFreeV = 
    unsafePerformIO $
    do { putStrLn "\nEnter Haskell declarations.  Terminate with :q \
          \on a single line\n"
       ; text <- getLines []
       ; let HsModule _ _ _ _ ds = testParser "Stdio" text
       ; let (a, b, c) = tfv (SS.freeD ds, map (\x -> SS.freeD [x]) ds)
       ; print ( (map zap  a), map zap b)
       }

tfv ((f1, f2), ds) = (f1 [], f2 [], map (\ (f1, f2) -> (f1 [], f2 [])) ds)

zap (UnQual x) = x
-}
{-
go () = 
     let (a,b,c) = tfv(testFreeV ())
         h (x,y) = (map zap x, map zap y)
     in (map zap a, map zap b, map h c)


getLines c = 
    do { l <- getLine
       ; if l == ":q" 
           then return c
           else getLines (c ++ "\n" ++ l)
       }

z = testGeneral "test2.hs" SCC.tim

testGeneral fname f  = 
    do { text <- readFile fname
       ; let HsModule _ _ _ _ ds = testParser fname text
       ; return $ f ds 
       }
          
w = do { testGeneral "test3.hs" test
       ; testGeneral "test3.hs" performTC
       } >>= id

dfree = (testGeneral "test3.hs" (\ ds -> SS.makeSCC ds [])) >>= print

d2 = (testGeneral "test3.hs" (map (\ d -> ff [] d []))) >>= print
-}
{- testD doesn't appear in Scope2 (imported qualified as S2) ...
d3 =  (testGeneral "test3.hs" (map (\ d -> S2.testD [d]))) >>= print

d4 =  (testGeneral "test3.hs" S2.testD) >>= print
-}

{-
HsModule _ _ _ _ ds = unsafePerformIO (start "test3.hs")


Dec(HsDataDecl _ cs1 tp1 t1 _) = ds !! 0
Dec(HsDataDecl _ cs2 tp2 t2 _) = ds !! 1
Dec(HsTypeDecl _ tp3 t3) = ds !! 2


fr xs y = let (bound,freef1) = SS.scopPatList [] (map SS.freeTP xs)
       in (bound ,SS.freeT y bound)


groups fname = 
    do { (bg,cyclic) <- testGeneral fname SCC.bindingGroups
       ; mapM_ (\ x -> do { putStrLn (pp x)
              ; putStrLn "-----------------"
              })
           bg
       }

-----------------------------------------------------------------
-- testing the free variable analysis

HsModule _ _ _ _ freeds = unsafePerformIO (start "tests/freeVartests.hs")

test1 d = testD [d]
freetest _ = map test1 freeds

d5 = freeds !! 4
-}
