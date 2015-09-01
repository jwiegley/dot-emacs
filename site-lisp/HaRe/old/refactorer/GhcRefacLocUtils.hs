module GhcRefacLocUtils(
                     {-
                     module HsTokens,
                     PosToken,simpPos,
                     -}
                     SimpPos,unmodified,modified
                     {-                   
                     ,simpPos0,ghead,glast,gfromJust
                     -}
                     , showToks                   
                     , gtail
                     , tokenCol, tokenRow
                     , tokenPos
                     , tokenCon
                     , tokenLen
                     {- 
                     ,lengthOfToks,
                     mkToken,defaultToken,newLnToken,whiteSpacesToken,whiteSpaceTokens
                     -}
                     , isWhite
                     , notWhite
                     -- , isWhiteSpace
                     {-
                     ,isNewLn,isCommentStart,isComment,
                     isNestedComment,isMultiLineComment,isOpenBracket,isCloseBracket,
                     isOpenSquareBracket,isCloseSquareBracket,isOpenBrace,isConid,
                     isLit,isWhereOrLet,isWhere,isLet,isIn,isCase,isDo,isIf,isForall,
                     isHiding,isModule,isComma,isEqual,isLambda,isIrrefute,isBar,isMinus,
                     endsWithNewLn,startsWithNewLn,hasNewLn,startsWithEmptyLn,
                     lastNonSpaceToken,firstNonSpaceToken,compressPreNewLns,compressEndNewLns
                     -}
                     , lengthOfLastLine
                     , updateToks
                     -- , getToks,replaceToks,deleteToks, doRmWhites,doAddWhites
                     , srcLocs
                     -- , ghcSrcLocs -- Test version
                     , getGhcLoc
                     , getStartEndLoc
                     {-    
                     , getStartEndLoc2,
                     startEndLoc,extendBothSides,extendForwards,extendBackwards,
                     startEndLocIncFowComment,startEndLocIncFowNewLn,startEndLocIncComments,
                     prettyprint ,deleteFromToks, prettyprintGuardsAlt,
                     addFormalParams,  adjustOffset, -- try to remove it
                     StartEndLoc, isArrow,-- swapInToks,
                     commentToks
                     -}
                     , tokenise
                     , lexStringToRichTokens  
                     -- , prettyprintPatList
                     , groupTokensByLine
                     -- , addLocInfo, getOffset
                     , splitToks
                     {-  
                     , insertComments,
                     extractComments, insertTerms
                     -}
  ) where


import qualified BasicTypes    as GHC
import qualified DynFlags      as GHC
import qualified FastString    as GHC
import qualified GHC           as GHC
import qualified GHC.Paths     as GHC
import qualified HsSyn         as GHC
import qualified Lexer         as GHC
import qualified Module        as GHC
import qualified MonadUtils    as GHC
import qualified Outputable    as GHC
import qualified RdrName       as GHC
import qualified SrcLoc        as GHC
import qualified StringBuffer  as GHC

import qualified Data.Generics as SYB
import qualified GHC.SYB.Utils as SYB

import GhcRefacTypeSyn
import GhcRefacMonad
import SrcLoc1
import SourceNames
import HsName
{-
import RefacTypeSyn(SimpPos)
import PosSyntax
import UniqueNames
import HsLexerPass1 hiding (notWhite)
import HsTokens
import PrettySymbols(rarrow)
import HsLayoutPre (PosToken)
-}
import PrettyPrint
{-
import HsExpUtil
import PNT

import RefacTypeSyn
-}
import Data.Maybe
import Data.List
{-
import SourceNames
-------------------------
--import DriftStructUtils
-}
import StrategyLib

------------------------
import Control.Monad.State
import System.IO.Unsafe

--In the token stream, locations are unique except the default locs.

{- Some related data types defined by Programatica's Lexer:
type Lexer = String -> LexerOutPut

type LexerOutput = [PosToken]

type PosToken = (Token,(Pos,String))

data Pos = Pos { char, line, column :: !Int } deriving (Show)
-- it seems that the field char is used to handle special characters including the '\t'


data Token
  = Varid | Conid | Varsym | Consym
  | Reservedid | Reservedop  | Specialid
  | IntLit | FloatLit | CharLit | StringLit
  | Qvarid | Qconid | Qvarsym | Qconsym
  | Special | Whitespace
  | NestedCommentStart -- will cause a call to an external function
  | NestedComment  -- from the external function
  | Commentstart  -- dashes
  | Comment -- what follows the dashes
  | ErrorToken | GotEOF | TheRest
  | ModuleName | ModuleAlias -- recognized in a later pass
  -- Inserted during layout processing (see Haskell 98, 9.3):
  | Layout     -- for implicit braces
  | Indent Int -- <n>, to preceed first token on each line
  | Open Int   -- {n}, after let, where, do or of, if not followed by a "{"
  deriving (Show,Eq,Ord)
-}

showToks :: [PosToken] -> String
showToks toks = show $ map (\t@(_,s) -> ((tokenRow t,tokenCol t),s)) toks

--A flag used to indicate whether the token stream has been modified or not.
unmodified = False
modified   = True

--- some default values----
pos0=Pos 0 0 0
simpPos0 = (0,0)
{-
extractComments :: (SimpPos, SimpPos) -> [PosToken] -> [PosToken]
extractComments ((startPosl, startPosr), endPos) toks
   = let (toks1, toks21, toks22) = splitToks ((startPosl, startPosr), endPos) toks
      in toks1

------------------------------------------------
-}
ghead info []    = error $ "ghead "++info++" []"
ghead info (h:_) = h

glast info []    = error $ "glast " ++ info ++ " []"
glast info h     = last h

gtail info []   = error $ "gtail " ++ info ++ " []"
gtail info h    = tail h
{-
gfromJust info (Just h) = h
gfromJust info Nothing = error $ "gfromJust " ++ info ++ " Nothing"
-}
--Some functions for fetching a specific field of a token
tokenCol (GHC.L l _,_) = c where [(_,c)] = getGhcLoc l 

tokenRow (GHC.L l _,_) = r where [(r,_)] = getGhcLoc l

tokenPos (GHC.L l _,_)     = head $ getGhcLoc l

tokenCon (_,s)     = s

tokenLen (_,s)     = length s   --check this again! need to handle the tab key.
{-
lengthOfToks::[PosToken]->Int
lengthOfToks=length.(concatMap tokenCon)
-}
--Some functions for checking whether a token is of a specific type of token.


-- ++WARNING++ : there is no explicit Whitespace token in GHC.
--isWhite (GHC.L _ t,_)                = t==Whitespace || t==Commentstart || t==Comment || t==NestedComment
isWhite (GHC.L _ (GHC.ITeof),_) = True
isWhite (GHC.L _ (GHC.ITdocCommentNext _) ,_) = True
isWhite (GHC.L _ (GHC.ITdocCommentPrev _) ,_) = True
isWhite (GHC.L _ (GHC.ITdocCommentNamed _),_) = True
isWhite (GHC.L _ (GHC.ITdocSection _ _)   ,_) = True
isWhite (GHC.L _ (GHC.ITdocOptions _)     ,_) = True	 
isWhite (GHC.L _ (GHC.ITdocOptionsOld _)  ,_) = True	 
isWhite (GHC.L _ (GHC.ITlineComment _)    ,_) = True 
isWhite (GHC.L _ (GHC.ITblockComment _)   ,_) = True
isWhite (GHC.L _ _                        ,_) = False

notWhite  = not.isWhite

-- ++WARNING++ : there is no explicit Whitespace token in GHC.
-- isWhiteSpace (t,(_,s))       = t==Whitespace && s==" "

{-
isNewLn (t,(_,s))            = t==Whitespace && s=="\n"

isCommentStart (t,(_,s))     = t==Commentstart && s=="--"
isComment (t,(_,s))          = t==Comment || t ==NestedComment
isNestedComment (t,(_,s))    = t==NestedComment
isMultiLineComment (t,(_,s)) = t==NestedComment && (isJust (find (=='\n') s))

isOpenBracket  (t,(_,s))       = t==Special && s=="("
isCloseBracket (t,(_,s))       = t==Special && s==")"

isOpenSquareBracket  (t,(_,s)) = t==Special && s=="["
isCloseSquareBracket (t,(_,s)) = t==Special && s=="]"

isOpenBrace  (t,(_,s))         = t==Special && s=="{"
isCloseBrace (t,(_,s))         = t==Special && s=="}"

isConid (t,(_,_))              = t==Conid
isLit (t,(_,s)) = t==IntLit || t==FloatLit || t==CharLit || t==StringLit

isWhereOrLet  t   = isWhere t || isLet t
isWhere (t,(_,s)) = t==Reservedid && s=="where"
isLet   (t,(_,s)) = t==Reservedid && s=="let"
isImport (t, (_,s))= t == Reservedid && s=="import"
isType (t, (_,s))= t  == Reservedid && s=="type"
isData (t, (_,s))= t == Reservedid && s=="data"
isFixty (t, (_,s)) = t==Reservedid && (s=="infix" || s=="infixl" || s=="infixr")
isDefault (t, (_,s)) = t == Reservedid && s=="default"
isClass (t, (_,s)) = t == Reservedid && s=="class"
isInstance (t, (_,s)) = t == Reservedid && s=="instance"
isNewtype (t, (_,s)) = t == Reservedid && s=="newtype"

isIn    (t,(_,s))  = t==Reservedid && s=="in"
isCase  (t,(_,s))  = t==Reservedid && s=="case"
isDo    (t,(_,s))  = t==Reservedid && s=="do"
isIf    (t,(_,s))  = t==Reservedid && s=="if"
isForall (t,(_,s)) = t==Reservedid && s=="forall"
isHiding (t,(_,s)) = s=="hiding"
isModule (t,(_,s)) = t==Reservedid && s=="module"

isComma (t,(_,s))    = t==Special && s==","
isEqual  (t,(_,s))   = t==Reservedop && s=="="
isLambda (t,(_,s))   = t==Reservedop && s=="\\"
isIrrefute (t,(_,s)) = t==Reservedop && s=="~"
isBar   (t,(_,s))    = t==Reservedop && s=="|"
isArrow (t,(_,s))    = t==Reservedop && s=="->"
isMinus (t,(_,s))    = t==Varsym && s=="-"

-----------------------------------------------------------------

--Returns True if the token ends with '\n'
endsWithNewLn::PosToken->Bool
endsWithNewLn   (_,(_,s)) =if s==[] then False
                                    else (glast "endsWithNewLn"  s=='\n')

--Returns True if the token starts with `\n`.
startsWithNewLn::PosToken->Bool
startsWithNewLn (_,(_,s)) =if s==[] then False
                                    else ((ghead "starsWithNewLn" s)=='\n')
-}
--Returns True if there is a '\n' in the token.
hasNewLn :: PosToken -> Bool
hasNewLn (GHC.L l _,_) = case l of
  GHC.RealSrcSpan ss -> (GHC.srcSpanStartLine ss /= GHC.srcSpanEndLine ss)
  _ -> False

onSameLn :: PosToken -> PosToken -> Bool
onSameLn (GHC.L l1 _,_) (GHC.L l2 _,_) = r1 == r2
  where
    [(r1,_)] = getGhcLoc l1
    [(r2,_)] = getGhcLoc l2

{-
--Returns True if a token stream starts with a newline token (apart from the white spaces tokens)
startsWithEmptyLn::[PosToken]->Bool
startsWithEmptyLn toks=isJust (find isNewLn $ takeWhile (\t->isWhiteSpace t || isNewLn t) toks)

-- get the last non-space token in a token stream.
lastNonSpaceToken::[PosToken]->PosToken
lastNonSpaceToken toks=case dropWhile isWhiteSpace (reverse toks) of
                         [] ->defaultToken
                         l -> ghead "lastNonSpaceToken" l

--get the first non-space token in a token stream.
firstNonSpaceToken::[PosToken]->PosToken
firstNonSpaceToken toks=case dropWhile isWhiteSpace toks of
                         [] ->defaultToken
                         l -> ghead "firstNonSpaceToken" l

-- remove the extra preceding  empty lines.
compressPreNewLns::[PosToken]->[PosToken]
compressPreNewLns toks= let (toks1, toks2) = break (not.(\t->isNewLn t || isWhiteSpace t)) toks
                            groupedToks    = groupTokensByLine toks1
                        in if length groupedToks>1 then (last groupedToks)++toks2
                                                   else toks

--remove the following extra empty lines.
compressEndNewLns::[PosToken]->[PosToken]
compressEndNewLns toks=let (toks1, toks2) = break (not.(\t->isNewLn t || isWhiteSpace t)) (reverse toks)
                           groupedToks    = groupTokensByLine toks1
                       in if length groupedToks>1 then reverse ((ghead "compressEndNewLns" groupedToks)++toks2)
                                                  else toks

prettyprintPatList beginWithSpace t
     = replaceTabBySpaces $ if beginWithSpace then format1 t else format2 t
 where
   format1 t = foldl (\x y -> x++ " "++(render.ppi) y) "" t

   format2 [] = ""
   format2 [p] = (render.ppi) p
   format2 (p:ps) = (render.ppi) p ++" " ++ format2 ps

prettyprint = replaceTabBySpaces.render.ppi

prettyprintGuardsAlt = replaceTabBySpaces.render.(ppRhs rarrow)


--Replace Tab by white spaces. (1 Tab=8 white spaces)
replaceTabBySpaces::String->String
replaceTabBySpaces []=[]
replaceTabBySpaces (s:ss)
  =if s=='\t' then replicate 8 ' ' ++replaceTabBySpaces ss
              else s:replaceTabBySpaces ss


--Compose a new token using the given arguments.
mkToken::Token->SimpPos->String->PosToken
mkToken t (row,col) c=(t,(Pos 0 row col,c))

---Restriction: the refactorer should not modify refactorer-modified/created tokens.
defaultToken = (Whitespace, (pos0," "))
newLnToken   = (Whitespace, (pos0,"\n"))

-}

tokenise :: GHC.RealSrcLoc -> Int -> Bool -> [Char] -> IO [PosToken]
tokenise  startPos _ _ [] = return []
tokenise  startPos colOffset withFirstLineIndent str
  = let str' = case lines str of
                    (ln:[]) -> addIndent ln ++ if glast "tokenise" str=='\n' then "\n" else ""
                    (ln:lns)-> addIndent ln ++ "\n" ++ concatMap (\n->replicate colOffset ' '++n++"\n") lns
        str'' = if glast "tokenise" str' == '\n' && glast "tokenise" str /='\n'
                  then genericTake (length str' -1) str'
                  else str'
    -- in expandNewLnTokens $ lexerPass0' startPos str''
    -- in expandNewLnTokens $ GHC.addSourceToTokens startPos
        
        -- toks = liftIO $ lexStringToRichTokens startPos str''
        toks = lexStringToRichTokens startPos str''
        -- toks = []
    in toks
    -- in error $ "tokenise:" ++ (showToks $ head toks)
   where
     addIndent ln = if withFirstLineIndent
                      then replicate colOffset ' '++ ln
                      else ln
                           
     {- ++AZ++ removed for now. Needed?                      
     --preprocssing the token stream to expand the white spaces to individual tokens.
     expandNewLnTokens::[PosToken]->[PosToken]
     expandNewLnTokens ts = concatMap expand ts
       where
        expand tok@(Whitespace,(pos,s)) = doExpanding pos s
        expand x = [x]

        doExpanding pos [] =[]
        doExpanding pos@(Pos c row col) (t:ts)
          = case t of
             '\n'  -> (Whitespace, (pos,[t])):(doExpanding (Pos c (row+1) 1) ts)
             _     -> (Whitespace, (pos,[t])):(doExpanding (Pos c row (col+1)) ts)
     -}

-- ---------------------------------------------------------------------

-- lexStringToRichTokens :: GHC.RealSrcLoc -> String -> IO [GHC.Located GHC.Token]
lexStringToRichTokens :: GHC.RealSrcLoc -> String -> IO [PosToken]
lexStringToRichTokens startLoc str = do
  GHC.defaultErrorHandler GHC.defaultLogAction $ do
    GHC.runGhc (Just GHC.libdir) $ do
      dflags <- GHC.getSessionDynFlags
      let dflags' = foldl GHC.xopt_set dflags
                    [GHC.Opt_Cpp, GHC.Opt_ImplicitPrelude, GHC.Opt_MagicHash]
      GHC.setSessionDynFlags dflags'

      -- lexTokenStream :: StringBuffer -> RealSrcLoc -> DynFlags -> ParseResult [Located Token]
      let res = GHC.lexTokenStream (GHC.stringToStringBuffer str) startLoc dflags'
      case res of
        -- GHC.POk _ toks -> return toks 
        GHC.POk _ toks -> return $ GHC.addSourceToTokens startLoc (GHC.stringToStringBuffer str) toks 
        GHC.PFailed srcSpan msg -> error $ "lexStringToRichTokens:" -- ++ (show $ GHC.ppr msg)

        -- addSourceToTokens :: RealSrcLoc -> StringBuffer -> [Located Token] -> [(Located Token, String)]

-- ---------------------------------------------------------------------
        
{-
--Should add cases for literals.
addLocInfo (decl, toks)
    = runStateT (applyTP (full_tdTP (idTP `adhocTP` inPnt
                                          `adhocTP` inSN)) decl) toks
       where
         inPnt (PNT pname ty (N (Just loc)))
            = do loc' <- findLoc (pNtoName pname)
                 return (PNT pname ty (N (Just loc')))
         inPnt x = return x

         inSN (SN (PlainModule modName) (SrcLoc _ _ row col))
             = do loc' <- findLoc modName
                  return (SN (PlainModule modName) loc')
         inSN x = return x


         pNtoName (PN (UnQual i) _)=i
         pNtoName (PN (Qual (PlainModule modName) i) _) = modName++"."++i
         pNtoName (PN (Qual (MainModule _) i) _)        = "Main."++i
         findLoc name
          = do  let name' = if name =="Prelude.[]" || name == "[]"  then "["
                               else if name=="Prelude.(,)" || name == "(,)" || name == "()"  then "("
                                                                                             else name   ----Check this again.
                    toks' = dropWhile (\t->tokenCon t /= name') toks
                    (row, col) =if toks'==[] then error ("HaRe: Error in addLocInfo while looking for" ++ name' ++ " !")
                                              else tokenPos $ ghead "findLoc" toks'
                return (SrcLoc "unknown" 0 row col)

-}

{- Old
groupTokensByLine [] = []
groupTokensByLine xs =let (xs', xs'') = break hasNewLn xs
                      in if xs''==[] then [xs']
                          else (xs'++ [ghead "groupTokensByLine" xs''])
                                : groupTokensByLine (gtail "groupTokensByLine" xs'')
-}

groupTokensByLine [] = []
groupTokensByLine (xs) = let x = head xs
                             (xs', xs'') = break (\x' -> tokenRow x /= tokenRow x') xs
                      in if xs''==[] then [xs']
                          else (xs'++ [ghead "groupTokensByLine" xs''])
                                : groupTokensByLine (gtail "groupTokensByLine" xs'')

--Give a token stream covering multi-lines, calculate the length of the last line
-- AZ: should be the last token start col, plus length of token.
lengthOfLastLine::[PosToken]->Int
lengthOfLastLine [] = 0
lengthOfLastLine toks
   -- = let (toks1,toks2)=break hasNewLn $ reverse toks
   = let rtoks = reverse toks
         x = head rtoks
         (toks1,toks2)=break (\x' -> tokenRow x /= tokenRow x') rtoks
     -- in  if toks2==[]
     in  if length toks2 == 0
          then sum (map tokenLen toks1)
          else sum (map tokenLen toks1) + lastLineLenOfToken (ghead "lengthOfLastLine" toks2)
  where
   --Compute the length of a token, if the token covers multi-line, only count the last line.
   --What about tab keys?
   lastLineLenOfToken (_,s)=(length.(takeWhile (\x->x/='\n')).reverse) s

{-

--get a token stream specified by the start and end position.
getToks::(SimpPos,SimpPos)->[PosToken]->[PosToken]
getToks (startPos,endPos) toks
    =let (_,toks2)=break (\t->tokenPos t==startPos) toks
         (toks21, toks22)=break (\t->tokenPos t==endPos) toks2
     in (toks21++ [ghead "getToks" toks22])   -- Should add error message for empty list?
-}
-- Split the token stream into three parts: the tokens before the startPos,
-- the tokens between startPos and endPos, and the tokens after endPos.
splitToks::(SimpPos, SimpPos)->[PosToken]->([PosToken],[PosToken],[PosToken])
splitToks (startPos, endPos) toks
   = if (startPos, endPos) == (simpPos0, simpPos0)
       then error "Invalid token stream position!"
       else let startPos'= if startPos==simpPos0 then endPos else startPos
                endPos'  = if endPos == simpPos0 then startPos else endPos
                (toks1, toks2) = break (\t -> tokenPos t == startPos') toks
                -- (toks21, toks22) = break (\t -> tokenPos t== endPos') toks2
                (toks21, toks22) = break (\t -> tokenPos t >= endPos') toks2
                -- Should add error message for empty list?
            -- in  if length toks22==0 then error "Sorry, HaRe failed to finish this refactoring." -- (">" ++ (show (startPos, endPos) ++ show toks))
            in  if length toks22==0 then error $ "Sorry, HaRe failed to finish this refactoring. >" ++ (show (startPos, endPos,startPos',endPos')) ++ "," ++ (showToks toks1) ++ "," ++ (showToks toks2)
                  else (toks1, toks21++[ghead "splitToks" toks22], gtail "splitToks" toks22)

{-
getOffset toks pos
  = let (ts1, ts2) = break (\t->tokenPos t == pos) toks
    in if ts2==[]
         then error "HaRe error: position does not exist in the token stream!"
         else lengthOfLastLine ts1
-}

-- ++AZ++ next bit commented out with --, otherwise ghci complains

-- --comment a token stream specified by the start and end position.
-- commentToks::(SimpPos,SimpPos)->[PosToken]->[PosToken]
-- commentToks (startPos,endPos) toks
--     = let (toks1, toks21, toks22) = splitToks (startPos, endPos) toks
--           toks21' = case toks21 of
--                      []              -> toks21
--                      (t,(l,s)):[]    -> (t, (l, ("{-" ++ s ++ "-}"))):[]
--                      (t1,(l1,s1)):ts -> let lastTok@(t2, (l2, s2)) = glast "commentToks" ts
--                                             lastTok' = (t2, (l2, (s2++" -}")))
--                                         in (t1,(l1, ("{- "++s1))): (reverse (lastTok': gtail "commentToks" (reverse ts)))
--       in (toks1 ++ toks21' ++ toks22)
         
-- ++AZ++ prev bit commented out with --, otherwise ghci complains

{-
insertTerms :: (SimpPos, SimpPos) -> [PosToken] -> String -> [PosToken]
insertTerms ((startPosl, startPosr), endPos) toks com
    = let (toks1, toks21, toks22) = splitToks ((startPosl, startPosr), endPos) toks
          toks21' = (Commentstart, ((Pos 0 startPosl startPosr) , "")) : [(Comment, ((Pos 0 startPosl startPosr), ("\n" ++ com ++ "\n")))]
      in (toks1 ++ toks21' ++ (toks21 ++ toks22))


insertComments :: (SimpPos, SimpPos) -> [PosToken] -> String -> [PosToken]
insertComments ((startPosl, startPosr), endPos) toks com
    = let (toks1, toks21, toks22) = splitToks ((startPosl, startPosr), endPos) toks
          toks21' = (Commentstart, ((Pos 0 startPosl startPosr) , "")) : [(Comment, ((Pos 0 startPosl startPosr), ("\n{- " ++ com ++ " -}\n")))]
      in (toks1 ++ toks21' ++ (toks21 ++ toks22))

---  - } - } 
-}


updateToks ::
 (SYB.Data t) =>
  GHC.GenLocated GHC.SrcSpan t
  -> GHC.GenLocated GHC.SrcSpan t -> (GHC.GenLocated GHC.SrcSpan t -> [Char]) -> Refact (GHC.GenLocated GHC.SrcSpan t, [PosToken])
updateToks oldAST newAST printFun
   = do (RefSt toks _ (v1, v2)) <- get
	let offset             = lengthOfLastLine toks1
            (toks1, _, _)      = splitToks (startPos, endPos) toks
	    (startPos, endPos) = getStartEndLoc toks oldAST
        newToks <- liftIO $ tokenise (GHC.mkRealSrcLoc (GHC.mkFastString "foo") 0 0) offset False $ printFun newAST  -- TODO: set filename as per loc in oldAST
        let 
            toks' = replaceToks toks startPos endPos newToks
        if length newToks == 0
          then put (RefSt toks' modified (v1,v2))
          else put (RefSt toks' modified (tokenRow (glast "updateToks1" newToks) -10, v2))
	
        return (newAST, newToks) 
        
{-
---REFACTORING: GENERALISE THIS FUNCTION.
addFormalParams t newParams
  = do ((toks,_),(v1, v2))<-get
       let (startPos,endPos) = getStartEndLoc toks t
           tToks     = getToks (startPos, endPos) toks
           (toks1, _) = let (toks1', toks2') = break (\t-> tokenPos t == endPos) toks
                        in (toks1' ++ [ghead "addFormalParams" toks2'], gtail "addFormalParams"  toks2')
           offset  = lengthOfLastLine toks1
           newToks = tokenise (Pos 0 v1 1) offset False (prettyprintPatList True newParams )
           toks'   = replaceToks toks startPos endPos (tToks++newToks)
       put ((toks',modified), ((tokenRow (glast "addFormalParams" newToks) -10), v2))
       addLocInfo (newParams, newToks)
-}

--Replace a list of tokens in the token stream by a new list of tokens, adjust the layout as well.
--To use this function make sure the start and end positions really exist in the token stream.
--QN: what happens if the start or end position does not exist?

replaceToks::[PosToken]->SimpPos->SimpPos->[PosToken]->[PosToken]
replaceToks toks startPos endPos newToks
   -- = error $ "replaceToks: newToks=" ++ (showToks newToks) -- ++AZ++
   = if length toks22 == 0
        then toks1 ++ newToks
        else let {-(pos::(Int,Int)) = tokenPos (ghead "replaceToks" toks22)-} -- JULIEN
                 oldOffset = {-getOffset toks pos  -}  lengthOfLastLine (toks1++toks21) --JULIEN
                 newOffset = {-getOffset (toks1++newToks++ toks22) pos -} lengthOfLastLine (toks1++newToks) -- JULIEN
             in  toks1++ (newToks++ adjustLayout toks22 oldOffset newOffset)
   where
      (toks1, toks21, toks22) = splitToks (startPos, endPos) toks
   
     
{-
{- Delete an syntax phrase from the token stream, this function (instead of the following one)
   should be the interface function for deleting tokens.
-}
-- deleteFromToks::( (MonadState (([PosToken], Bool), t1) m), StartEndLoc t,Printable t,Term t)=>t->m ()
deleteFromToks t getLocFun
   =do ((toks,_),others)<-get
       let (startPos,endPos)=getLocFun toks t
           toks'=deleteToks toks startPos endPos
       put ((toks',modified),others)

{-Delete a sequence of tokens specified by the start position and end position from the token stream,
  then adjust the remaining token stream to preserve layout-}
deleteToks::[PosToken]->SimpPos->SimpPos->[PosToken]
deleteToks toks startPos@(startRow, startCol) endPos@(endRow, endCol)
  = case after of
      (_:_) ->    let nextPos =tokenPos $ ghead "deleteToks1" after
                      oldOffset = getOffset toks nextPos
                      newOffset = getOffset (toks1++before++after) nextPos
                  in  toks1++before++adjustLayout (after++toks22) oldOffset newOffset
      _     -> if toks22 == []
                 then toks1++before
                 else let toks22'=let nextOffset = getOffset toks (tokenPos (ghead "deleteToks2" toks22))
                                  in if isMultiLineComment (lastNonSpaceToken toks21)
                                       then whiteSpaceTokens (-1111, 0) (nextOffset-1) ++ toks22
                                       else toks22
                      in if endsWithNewLn (last (toks1++before)) || startsWithNewLn (ghead "deleteToks3" toks22')
                           then  toks1++before++toks22'
                           --avoiding layout adjustment by adding a `\n', sometimes may produce extra lines.
                             else  toks1++before++[newLnToken]++toks22'
                            --  else toks1 ++ before ++ toks22'
     where

      (toks1, toks2) = let (ts1, ts2)   = break (\t->tokenPos t == startPos) toks
                           (ts11, ts12) = break hasNewLn (reverse ts1)
                       in (reverse ts12, reverse ts11 ++ ts2)
      (toks21, toks22)=let (ts1, ts2) = break (\t -> tokenPos t == endPos) toks2
                           (ts11, ts12) = break hasNewLn ts2
                       in (ts1++ts11++if ts12==[] then [] else [ghead "deleteToks4" ts12], if ts12==[] then [] else gtail "deleteToks5"  ts12)

      -- tokens before the tokens to be deleted at the same line
      before = takeWhile (\t->tokenPos t/=startPos) toks21

      -- tokens after the tokens to be deleted at the same line.
      after = let t= dropWhile (\t->tokenPos t /=endPos) toks21
              in  if t == [] then error "Sorry, HaRe failed to finish this refactoring."
                             else  gtail "deleteToks6" t

-}
-- Adjust the layout to compensate the change in the token stream.
adjustLayout::[PosToken]->Int->Int->[PosToken]
adjustLayout [] _ _ = []
adjustLayout toks oldOffset newOffset = toks -- ++AZ++ temporary while plumbing the rest
{- ++AZ++ TODO: restore and fix this
adjustLayout toks oldOffset newOffset
 | oldOffset == newOffset  = toks

adjustLayout toks oldOffset newOffset
  = case layoutRuleApplies of
    True -> let (ts:ts') = groupTokensByLine  toks
            in ts ++ addRmSpaces (newOffset-oldOffset) oldOffset  ts'  -- THIS IS PROBLEMETIC.
    _    -> toks
  where

  layoutRuleApplies
    = let ts = dropWhile (\t-> (not.elem (tokenCon t)) keyWords)
               -- $ filter notWhite
               $ takeWhile (not.hasNewLn) toks -- ++AZ++ TODO: pretty sure hasNewLn will not give expected result, no whitespace toks in GHC
      in case ts of
         (_: t: _) -> tokenCon t /= "{"
         _         -> False

  keyWords = ["where","let","do","of"]

  addRmSpaces n col [] = []
  addRmSpaces n col toks@(ts:ts')
    =case find notWhite ts of
      Just t  -> if length (concatMap tokenCon ts1) >= col
                 then (addRmSpaces' n ts) ++ addRmSpaces n col ts'
                 else concat toks
      _       -> ts ++ addRmSpaces n col ts'
     where
      (ts1, ts2) = break notWhite ts

  addRmSpaces' 0 ts = ts
  addRmSpaces' _ [] = []
  addRmSpaces' n ts@(t:ts')
    = case n >0 of
       True -> whiteSpaceTokens (tokenRow t,0) n ++ ts   -- CHECK THIS.
       _    -> if isWhiteSpace t
               then addRmSpaces' (n+1) ts'
               else error $ "Layout adjusting failed at line:"
                           ++ show (tokenRow t)++ "."
++AZ++ -}

{-
-- remove at most n white space tokens from the beginning of ts
doRmWhites::Int->[PosToken]->[PosToken]
doRmWhites 0 ts=ts
doRmWhites n []=[]
doRmWhites n toks@(t:ts)=if isWhiteSpace t then doRmWhites (n-1) ts
                                           else toks

--add n white space tokens to the beginning of ts
doAddWhites::Int->[PosToken]->[PosToken]
doAddWhites n []=[]
doAddWhites n ts@(t:_)= whiteSpacesToken (tokenRow t,0) n ++ts

whiteSpaceTokens (row, col) n
 = if n<=0
    then []
    else (mkToken Whitespace (row,col) " "):whiteSpaceTokens (row,col+1) (n-1)
-}
-------------------------------------------------------------------------------------------------
--get all the source locations (use locations) in an AST phrase t in according the the occurrence order of identifiers.
srcLocs::(Term t)=> t->[SimpPos]
srcLocs t =(nub.srcLocs') t \\ [simpPos0]
   where srcLocs'= SYB.everythingStaged SYB.Parser (++) []
                   ([]
                    `SYB.mkQ` pnt
                    `SYB.extQ` sn
                    `SYB.extQ` literalInExp
                    `SYB.extQ` literalInPat)


         pnt :: GHC.GenLocated GHC.SrcSpan GHC.RdrName -> [SimpPos]
         pnt (GHC.L l (GHC.Unqual _)) = getGhcLoc l
         pnt (GHC.L l (GHC.Qual _ _)) = getGhcLoc l
         pnt (GHC.L l (GHC.Orig _ _)) = getGhcLoc l
         pnt (GHC.L l (GHC.Exact _))  = getGhcLoc l
         pnt _                        = []

         sn :: GHC.HsModule GHC.RdrName -> [SimpPos]
         sn (GHC.HsModule (Just (GHC.L l _)) _ _ _ _ _) = getGhcLoc l
         sn _ = []

         literalInExp :: GHC.LHsExpr GHC.RdrName -> [SimpPos]
         literalInExp (GHC.L l (GHC.HsOverLit _)) = getGhcLoc l

         literalInExp (GHC.L l (GHC.HsLit (GHC.HsChar _)))        = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsCharPrim _)))    = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsString _)))      = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsStringPrim _)))  = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsInt _)))         = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsIntPrim _)))     = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsWordPrim _)))    = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsInt64Prim _)))   = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsWord64Prim _)))  = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsInteger _ _)))   = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsRat _ _)))       = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsFloatPrim _)))   = getGhcLoc l
         literalInExp (GHC.L l (GHC.HsLit (GHC.HsDoublePrim _ ))) = getGhcLoc l
         literalInExp _ = []

         literalInPat :: GHC.LPat GHC.RdrName -> [SimpPos]
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsChar _)))        = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsCharPrim _)))    = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsString _)))      = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsStringPrim _)))  = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsInt _)))         = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsIntPrim _)))     = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsWordPrim _)))    = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsInt64Prim _)))   = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsWord64Prim _)))  = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsInteger _ _)))   = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsRat _ _)))       = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsFloatPrim _)))   = getGhcLoc l
         literalInPat (GHC.L l (GHC.LitPat (GHC.HsDoublePrim _ ))) = getGhcLoc l
         literalInPat _ = []

{-
GHC.everythingStaged ::
  forall r.
  GHC.Stage -> (r -> r -> r) -> r -> SYB.GenericQ r -> SYB.GenericQ r

SYB.everything ::
  forall r.
               (r -> r -> r) ->      SYB.GenericQ r -> SYB.GenericQ r
  	-- Defined in `Data.Generics.Schemes'
-}

{-
main = print $ ( listify (\(_::Int) -> True)         mytree
               , everything (++) ([] `mkQ` fromLeaf) mytree
               )
  where
    fromLeaf :: Tree Int Int -> [Int]
    fromLeaf (Leaf x) = [x]
    fromLeaf _ = []
-}


getGhcLoc (GHC.RealSrcSpan ss)    = [(GHC.srcSpanStartLine ss, GHC.srcSpanStartCol ss)]
getGhcLoc (GHC.UnhelpfulSpan _) = []

{-
class StartEndLocPat t where

   startEndLoc2 :: [PosToken]->t->[(SimpPos,SimpPos)]
   -- startEndLoc3 :: [PosToken]->t->[(SimpPos,SimpPos)]


instance StartEndLocPat [HsDeclP] where
   startEndLoc2 toks ds=if  ds==[] then [(simpPos0,simpPos0)]
                                   else if length ds==1
                                         then [startEndLoc toks (ghead "StartEndLoc:[HsDeclP]" ds)]
                                         else concat (map (startEndLoc2 toks) ds)


instance StartEndLocPat HsMatchP where
   startEndLoc2 toks (HsMatch loc i ps rhs ds)
         =let (startLoc,_)=startEndLoc toks i
              (_,endLoc)  =if ds==[] then startEndLoc toks rhs
                                     else startEndLoc toks (glast "StartEndLoc:HsMatchP" ds)
          in [(startLoc,endLoc)]

instance StartEndLocPat HsDeclP where

   startEndLoc2 toks (Dec (HsTypeDecl (SrcLoc _ _ r c) tp t))
      = let (startLoc, _) = startEndLoc toks tp
            (_ , endLoc)  = startEndLoc toks t
        in [extendForwards toks startLoc endLoc isType]

   startEndLoc2 toks (Dec (HsDataDecl loc c tp decls is))
        = let (startLoc, _) = startEndLoc toks tp
              (_, endLoc)  = if is == [] then startEndLoc toks (glast "StartEndLoc:HsDeclP1" decls)
                                        else startEndLoc toks is
          in [extendForwards toks startLoc endLoc isData]

   startEndLoc2 toks (Dec (HsNewTypeDecl loc c tp decls is))
        = let (startLoc, _) = startEndLoc toks tp
              (_, endLoc) = if is == [] then startEndLoc toks decls
                                        else startEndLoc toks is
          in [extendForwards toks startLoc endLoc isNewtype]

   startEndLoc2 toks (Dec (HsDefaultDecl _ ts))
      = let (startLoc, _) = startEndLoc toks (head ts)
            (_ , endLoc) = startEndLoc toks (last ts)
        in [extendForwards toks startLoc endLoc isDefault]

   startEndLoc2 toks (Dec (HsInfixDecl _ _ is))
      = let (startLoc, _) = startEndLoc toks (head is)
            (_, endLoc)   = startEndLoc toks (last is)
        in [extendForwards toks startLoc endLoc isFixty]

   startEndLoc2 toks d@(Dec (HsFunBind _ ms))
      = map (startEndLoc toks) ms

   startEndLoc2 toks (Dec (HsPatBind _  p rhs ds))
       = let (startLoc, _) = startEndLoc toks p
             (_, endLoc)   = if ds ==[] then startEndLoc toks rhs
                                        else startEndLoc toks (glast "startEndLoc:HsDeclP5" ds)
             toks1 = dropWhile (\t->tokenPos t /= endLoc) toks
	     endLoc1 = if toks1==[]
			  then endLoc
			  else let toks2 = takeWhile (\t -> isSpecialTok t) toks1
                               in (tokenPos.glast "startEndLoc::HsMatchP") toks2
          in [(startLoc, endLoc1)]
       where
         isSpecialTok t = isWhiteSpace t  || isCloseBracket t || isOpenBracket t || isOpenSquareBracket t
                        || isCloseSquareBracket t

   startEndLoc2 toks (Dec (HsTypeSig _ is c t))
      = let (startLoc, _) = startEndLoc toks (ghead "startEndLoc:HsDeclP6" is)
            (_, endLoc)   = startEndLoc toks t
        in [(startLoc, endLoc)]


   startEndLoc2 toks decl@(Dec (HsClassDecl loc c tp funDeps  ds))
      = let locs = srcLocs decl
            (startLoc, endLoc)
              = if locs == [] then (simpPos0, simpPos0)
                 else (head locs, last locs)
        in [extendForwards toks startLoc endLoc isClass]

   startEndLoc2 toks decl@(Dec (HsInstDecl loc i c t ds))
     = let locs = srcLocs decl
           (startLoc, endLoc)
              = if locs == [] then (simpPos0, simpPos0)
                 else (head locs, last locs)
        in [extendForwards toks startLoc endLoc isInstance]


getStartEndLoc2::(Term t, StartEndLocPat t,Printable t)=>[PosToken]->t->[(SimpPos,SimpPos)]
getStartEndLoc2 toks t
  = startEndLoc2 toks t
     {-   locs = srcLocs t
        (startPos,endPos) = (if startPos' == simpPos0 && locs /=[] then ghead "getStartEndLoc2" locs
                                                                   else startPos',
                             if endPos' == simpPos0 && locs /= [] then glast "gerStartEndLoc2" locs
                                                                  else endPos')
    in (startPos, endPos)  -}

-}

--given an AST phrase, 'startEndLoc' gets its start and end position in the program source.
class StartEndLoc t where
   startEndLoc :: [PosToken]-> t ->(SimpPos,SimpPos)


instance StartEndLoc (GHC.HsExpr GHC.RdrName) where
  -- TODO: do this properly
  startEndLoc toks e =
    case e of

      GHC.HsVar id	-> ((0,0),(0,0))
{-
      GHC.HsIPVar (IPName id)	

      GHC.HsOverLit (HsOverLit id)	

      GHC.HsLit HsLit	

      GHC.HsLam (MatchGroup id)	 

      GHC.HsApp (LHsExpr id) (LHsExpr id)
      
      GHC.OpApp (LHsExpr id) (LHsExpr id) Fixity (LHsExpr id)
      
      GHC.NegApp (LHsExpr id) (SyntaxExpr id)
      
      GHC.HsPar (LHsExpr id)
      
      GHC.SectionL (LHsExpr id) (LHsExpr id)
      
      GHC.SectionR (LHsExpr id) (LHsExpr id)
      
      GHC.ExplicitTuple [HsTupArg id] Boxity
      
      GHC.HsCase (LHsExpr id) (MatchGroup id)
      
      GHC.HsIf (Maybe (SyntaxExpr id)) (LHsExpr id) (LHsExpr id) (LHsExpr id)
      
      GHC.HsLet (HsLocalBinds id) (LHsExpr id)
      
      GHC.HsDo (HsStmtContext Name) [LStmt id] PostTcType
      
      GHC.ExplicitList PostTcType [LHsExpr id]
      
      GHC.ExplicitPArr PostTcType [LHsExpr id]
      
      GHC.RecordCon (Located id) PostTcExpr (HsRecordBinds id)
      
      GHC.RecordUpd (LHsExpr id) (HsRecordBinds id) [DataCon] [PostTcType] [PostTcType]
      
      GHC.ExprWithTySig (LHsExpr id) (LHsType id)
      
      GHC.ExprWithTySigOut (LHsExpr id) (LHsType Name)
      
      GHC.ArithSeq PostTcExpr (ArithSeqInfo id)
      
      GHC.PArrSeq PostTcExpr (ArithSeqInfo id)
      
      GHC.HsSCC FastString (LHsExpr id)
      
      GHC.HsCoreAnn FastString (LHsExpr id)
      
      GHC.HsBracket (HsBracket id)
      
      GHC.HsBracketOut (HsBracket Name) [PendingSplice]
      
      GHC.HsSpliceE (HsSplice id)
      
      GHC.HsQuasiQuoteE (HsQuasiQuote id)
      
      GHC.HsProc (LPat id) (LHsCmdTop id)
      
      GHC.HsArrApp (LHsExpr id) (LHsExpr id) PostTcType HsArrAppType Bool
      
      GHC.HsArrForm (LHsExpr id) (Maybe Fixity) [LHsCmdTop id]
      
      GHC.HsTick (Tickish id) (LHsExpr id)
      
      GHC.HsBinTick Int Int (LHsExpr id)
      
      GHC.HsTickPragma (FastString, (Int, Int), (Int, Int)) (LHsExpr id)
      
      GHC.EWildPat
      
      GHC.EAsPat (Located id) (LHsExpr id)
      
      GHC.EViewPat (LHsExpr id) (LHsExpr id)
      
      GHC.ELazyPat (LHsExpr id)
      
      GHC.HsType (LHsType id)
      
      GHC.HsWrap HsWrapper (HsExpr id)	 
-}

   
{-
instance StartEndLoc HsModuleP where
  startEndLoc toks _  = (tokenPos (ghead "startEndLoc:HsModuleP" toks),
                         tokenPos (glast "startEndLoc:HsModuleP" toks))

instance StartEndLoc HsExpP where

  startEndLoc  toks (Exp e)=
      case e of

        HsId ident@(HsVar (PNT pn _ _)) ->let (startLoc, endLoc) = startEndLoc toks ident
                                              {- To handle infix operator. for infix operators like (++), there
                                                  is no parenthesis in the syntax tree -}
                                             {-  (toks1,toks2) = break (\t->tokenPos t==startLoc) toks
                                              toks1' = dropWhile isWhite (reverse toks1)
                                              toks2' = dropWhile isWhite (gtail "startEndLoc:HsExpP"
                                                          (dropWhile (\t->tokenPos t /=endLoc) toks2)) -}
                                           in  {-if toks1'/=[] && toks2'/=[] && isOpenBracket (head toks1')
                                                 && isCloseBracket (head toks2')
                                              then (tokenPos (head toks1'), tokenPos (head toks2'))
                                              else-}  (startLoc, endLoc)
        HsId  x                       ->startEndLoc toks x

        HsLit (SrcLoc _ _ r c) _      -> ((r,c),(r,c))

        HsInfixApp e1 op e2           ->let (startLoc,_)=startEndLoc toks e1
                                            (_, endLoc) =startEndLoc toks e2
                                        in (startLoc,endLoc)

        e@(HsApp e1 e2)               ->let (startLoc,endLoc)=startEndLoc toks e1
                                            (startLoc1, endLoc1 )=startEndLoc toks e2

                                        in (startLoc, endLoc1)

        HsNegApp (SrcLoc _ _ r c) e     ->let (_,endLoc)=startEndLoc toks e
                                          in ((r,c), endLoc)

        HsLambda ps e                 ->let (startLoc,_)=startEndLoc toks (ghead "startEndLoc:HsLambda" ps)  --ps can not be empty
                                            (_,endLoc)  =startEndLoc toks e
                                        in extendForwards toks startLoc endLoc isLambda

        HsIf e1 e2 e3                 ->let (startLoc, _)=startEndLoc toks e1
                                            (_, endLoc)=startEndLoc toks e3
                                        in extendForwards toks  startLoc endLoc isIf

        HsLet ds e                    ->if ds==[]
                                          then
                                            let  (startLoc,endLoc)=startEndLoc toks e
                                            in extendForwards toks startLoc endLoc isLet
                                          else
                                            let  (startLoc,_)=startEndLoc toks (ghead "startEndLoc:HsLet" ds)
                                                 (_,endLoc)  =startEndLoc toks e
                                            in extendForwards toks startLoc endLoc isLet

        HsCase e alts                 ->let (startLoc,_)=startEndLoc toks e
                                            (_,endLoc)  =startEndLoc toks (glast "HsCase" alts) --alts can not be empty.
                                        in extendForwards toks startLoc endLoc isCase

        HsDo stmts                    ->let (startLoc, endLoc)=startEndLoc toks  stmts
                                        in extendForwards toks startLoc endLoc isDo

        HsTuple es                    ->if es==[]
                                         then  (simpPos0,simpPos0)  --Empty tuple can cause problem.
                                         else let (startLoc,_)=startEndLoc toks (ghead "startEndLoc:HsTuple" es)
                                                  (_,endLoc)  =startEndLoc toks (glast "startEndLoc:HsTuple" es)
                                              in extendBothSides toks startLoc endLoc isOpenBracket isCloseBracket

        HsList es                     ->if es==[]
                                         then (simpPos0,simpPos0)  --Empty list can cause problem.
                                         else let (startLoc,_)=startEndLoc toks (ghead "startEndLoc:HsList" es)
                                                  (_,endLoc)  =startEndLoc toks (glast "startEndLoc:HsList" es)
                                              in extendBothSides toks startLoc endLoc isOpenSquareBracket isCloseSquareBracket

        HsParen e                     ->let (startLoc,(endLocR, endLocC))=startEndLoc toks  e
                                        in extendBothSides toks startLoc (endLocR, endLocC) isOpenBracket isCloseBracket

                                       --  in if expIsPNT e
--                                              then (startLoc, (endLocR, endLocC+1))
--                                              else extendBothSides toks startLoc (endLocR, endLocC) isOpenBracket isCloseBracket
--                                           where
--                                             expIsPNT (Exp (HsId (HsVar pnt)))=True
--                                             expIsPNT (Exp (HsParen e))=expIsPNT e
--                                             expIsPNT _ =False

        HsLeftSection e op            ->let (startLoc,_)=startEndLoc toks e
                                            (_, endLoc )=startEndLoc toks op
                                        in (startLoc,endLoc)

        HsRightSection op e           ->let (startLoc,_)=startEndLoc toks op
                                            (_, endLoc )=startEndLoc toks op
                                        in (startLoc,endLoc)

        HsRecConstr loc i upds            ->let (startLoc,_)=startEndLoc toks i
                                                (_,endLoc)  =startEndLoc toks (glast "startEndLoc:HsRecConstr" upds) --can 'upds' be empty?
                                        in extendBackwards toks startLoc endLoc isCloseBrace

        HsRecUpdate loc e upds            ->let (startLoc,_)=startEndLoc toks e
                                                (_,endLoc)  =startEndLoc toks (glast "startEndLoc:HsRecUpdate" upds) --ditto
                                        in extendBackwards toks startLoc endLoc isCloseBrace

        HsEnumFrom e                  ->let (startLoc,endLoc)=startEndLoc toks e
                                        in extendBothSides toks startLoc endLoc isOpenSquareBracket isCloseSquareBracket

        HsEnumFromTo e1 e2            ->let (startLoc,_)=startEndLoc toks e1
                                            (_,  endLoc)=startEndLoc toks e2
                                        in extendBothSides toks startLoc endLoc isOpenSquareBracket isCloseSquareBracket

        HsEnumFromThen e1 e2          ->let (startLoc,_)=startEndLoc toks e1
                                            (_,  endLoc)=startEndLoc toks e2
                                        in extendBothSides toks startLoc endLoc isOpenSquareBracket isCloseSquareBracket

        HsEnumFromThenTo e1 e2 e3     ->let (startLoc,_)=startEndLoc toks e1
                                            (_,  endLoc)=startEndLoc toks e3
                                        in extendBothSides toks startLoc endLoc isOpenSquareBracket isCloseSquareBracket

        HsListComp stmts              ->let (startLoc,endLoc)=startEndLoc toks stmts
                                        in  extendBothSides toks startLoc endLoc isOpenSquareBracket isCloseSquareBracket

        HsAsPat i e                   ->let (startLoc,_)=startEndLoc toks i
                                            (_,endLoc)=  startEndLoc toks e
                                        in (startLoc,endLoc)

        HsIrrPat e                    ->let (startLoc,endLoc)=startEndLoc toks e
                                        in extendForwards toks startLoc endLoc isIrrefute

        HsWildCard                    ->(simpPos0,simpPos0)  -- wildcard can cause problem.


        HsExpTypeSig loc e c t        ->let (startLoc,_)=startEndLoc toks e
                                            (_, endLoc )=startEndLoc toks t
                                        in (startLoc,endLoc)

instance StartEndLoc HsTypeP where

   startEndLoc toks (Typ p)=
      case p of
        HsTyFun  t1  t2       ->   let (startLoc,e)=startEndLoc toks t1
                                       (_ , endLoc)=startEndLoc toks t2
                                   in (startLoc,endLoc)
        --HsTyTuple [t]         ->

        HsTyApp  t1 t2        ->   let (startLoc,endLoc)=startEndLoc toks  t1
                                       (startLoc1 , endLoc1)=startEndLoc toks  t2
                                   in case t1 of
                                        (Typ (HsTyCon t)) -> if (render.ppi) t == "[]"
                                                   then extendBothSides toks startLoc1 endLoc1 isOpenSquareBracket isCloseSquareBracket
                                                   else (startLoc, endLoc1)
                                        _  -> (startLoc, endLoc1)

        HsTyVar  i            ->   let (startLoc, endLoc) = startEndLoc toks i
                                   in  extendBothSides' toks startLoc endLoc isOpenBracket isCloseBracket
        HsTyCon  i            ->   let (startLoc, endLoc) = startEndLoc toks i
                                   in if (render.ppi) i =="[]"
                                        then extendBothSides toks startLoc endLoc isOpenSquareBracket isCloseSquareBracket
                                        else extendBothSides' toks startLoc endLoc isOpenBracket isCloseBracket

        HsTyForall   is ts t   ->   case is of
                                     []  ->let (startLoc,endLoc)=startEndLoc toks t
                                           in  extendForwards toks startLoc endLoc isForall

                                     l  -> let (startLoc, _) =startEndLoc toks  $ ghead "StartEndLoc:HsTypeP" is
                                               ( _ , endLoc) =startEndLoc toks t
                                           in extendForwards toks startLoc endLoc isForall

extendBothSides'  toks startLoc endLoc  forwardCondFun backwardCondFun
       =let (toks1,toks2)=break (\t->tokenPos t==startLoc) toks
            toks21=dropWhile (\t->tokenPos t<=endLoc) toks2
            firstLoc=case (dropWhile isWhite (reverse toks1)) of
                             [] -> startLoc    -- is this the correct default?
                             ls  -> if (forwardCondFun.ghead "extendBothSides:lastTok") ls  then tokenPos (head ls)
                                      else startLoc
            lastLoc =case (dropWhile isWhite toks21) of
                            [] ->endLoc   --is this a correct default?
                            ls -> if (backwardCondFun.ghead "extendBothSides:lastTok") ls then tokenPos (head ls)
                                   else endLoc
        in (firstLoc, lastLoc)

instance StartEndLoc HsPatP where

  startEndLoc toks (Pat p)=
     case p of
       HsPId i                          ->startEndLoc toks i

       HsPLit (SrcLoc _ _ r c) _        ->((r,c),(r,c))

       HsPNeg (SrcLoc _ _  r c) p       ->((r,c),(r,c))

       HsPInfixApp p1 op p2             ->let (startLoc,_)=startEndLoc toks  p1
                                              (_ , endLoc)=startEndLoc toks p2
                                          in (startLoc,endLoc)

       HsPApp i ps                      ->let (startLoc,_)=startEndLoc toks  i
                                              (_,endLoc)=startEndLoc toks (glast "StartEndLoc:HsPatP" ps)
                                          in (startLoc,endLoc)

       HsPTuple loc ps                  -> if ps==[]
                                             then  (simpPos0,simpPos0)  -- ****Update this using locations****.
                                             else let (startLoc,_)=startEndLoc toks (ghead "startEndLoc:HsPTuple"  ps)
                                                      (_,endLoc)=startEndLoc toks (glast "startEndLoc:HsPTuple" ps)
                                                  in extendBothSides toks startLoc endLoc isOpenBracket isCloseBracket

       HsPList loc ps                     ->if ps==[]
                                            then (simpPos0,simpPos0)  -- ***Update this using locations*****
                                            else let (startLoc,_)=startEndLoc toks (ghead "startEndLoc:HsPList" ps)
                                                     (_, endLoc) =startEndLoc toks (glast "startEndLoc:HsPList" ps)
                                            in  extendBothSides toks startLoc endLoc isOpenSquareBracket isCloseSquareBracket

       HsPParen p                       ->let (startLoc,endLoc)=startEndLoc toks p
                                          in extendBothSides toks startLoc endLoc isOpenBracket isCloseBracket

       HsPRec i upds                    ->let (startLoc,_)=startEndLoc toks i
                                              (_,endLoc)=startEndLoc toks (glast "startEndLoc:HsPRec" upds) --can upds be empty?
                                          in extendBackwards toks startLoc endLoc isCloseBrace

       HsPAsPat i p                     ->let (startLoc,_)=startEndLoc toks i
                                              (_,endLoc)=startEndLoc toks p
                                          in (startLoc,endLoc)

       HsPIrrPat p                      ->let (startLoc,endLoc)=startEndLoc toks p
                                          in extendForwards toks startLoc endLoc isIrrefute

       HsPWildCard                       ->(simpPos0,simpPos0)  -- wildcard can  cause problem.

instance StartEndLoc [HsPatP] where

   startEndLoc toks ps = let locs=(nub.(map (startEndLoc toks))) ps \\ [(simpPos0,simpPos0)]
                         in if locs==[] then (simpPos0,simpPos0)
                                        else let (startLoc,_)=ghead "StartEndLoc:HsPatP" locs
                                                 (_,endLoc) =glast "StartEndLoc:HsPatP"  locs
                                             in (startLoc,endLoc)
instance StartEndLoc [HsExpP] where

   startEndLoc toks es=let locs=(nub.(map (startEndLoc toks))) es \\ [(simpPos0,simpPos0)]
                       in if locs==[] then (simpPos0,simpPos0)
                                      else let (startLoc,_)=ghead "StartEndLoc:HsExp" locs
                                               (_,endLoc) =glast "startEndLoc:HsExp" locs
                                           in (startLoc,endLoc)
instance StartEndLoc [HsDeclP] where
  startEndLoc toks ds=if  ds==[] then (simpPos0,simpPos0)
                                 else if length ds==1
                                        then startEndLoc toks (ghead "StartEndLoc:[HsDeclP]" ds)
                                        else  let (startLoc,_)=startEndLoc toks (ghead "StartEndLoc:[HsDeclP]" ds)
                                                  (_,endLoc) =startEndLoc toks (glast  "StartEndLoc:[HsDeclP]" ds)
                                              in (startLoc,endLoc)

instance StartEndLoc HsMatchP where
   startEndLoc toks t@(HsMatch loc i ps rhs ds)
         =let (startLoc,_)=startEndLoc toks i
              (_,endLoc)  =if ds==[] then startEndLoc toks rhs
                                     else startEndLoc toks (glast "StartEndLoc:HsMatchP" ds)
              locs = srcLocs t
              (startLoc1,endLoc1) = (if startLoc == simpPos0 && locs /=[] then ghead "getStartEndLoc" locs
                                                                   else startLoc,
				     if endLoc == simpPos0 && locs /= [] then glast "getStartEndLoc" locs
                                                                         else endLoc)
              toks1 = gtail "startEndLoc:HsMatchP" (dropWhile (\t->tokenPos t /= endLoc1) toks)
              toks0 = getToks (startLoc1, endLoc1) toks
	      endLoc2 = if toks1==[]
		 	  then endLoc1
			  else let toks2 = takeWhile (\t -> isSpecialTok t && needmore toks t ) toks1
                               in if toks2 == [] || all (\t-> isWhiteSpace t ) toks2
				       then endLoc1
                                       else (tokenPos.glast "startEndLoc::HsMatchP") toks2

          in (startLoc1, endLoc2)
        where
          isSpecialTok t = isWhiteSpace t  || isCloseBracket t || isOpenBracket t || isOpenSquareBracket t
                          || isCloseSquareBracket t
          needmore toks t = case  isCloseBracket t of
                              True -> let openBrackets = length $ filter isOpenBracket toks
                                          closeBrackets = length $ filter isCloseBracket toks
                                      in closeBrackets < openBrackets
                              False -> case isCloseSquareBracket t of
                                       True -> let openSqBrackets = length $ filter isOpenSquareBracket toks
                                                   closeSqBrackets = length $ filter isCloseSquareBracket toks
                                               in closeSqBrackets < openSqBrackets
                                       false -> True


instance StartEndLoc HsStmtP where      -- Bug fixed. 20/05/2004
   startEndLoc toks stmts=let s=getStmtList  stmts
                              locs = map (startEndLoc toks) s
                              (startLocs, endLocs) =(sort (map fst locs), sort (map snd locs))
                          in (ghead "StartEndLoc::HsStmtP" startLocs, glast "StartEndLoc::HsStmtP" endLocs)

instance StartEndLoc (HsStmtAtom HsExpP HsPatP [HsDeclP])  where

    startEndLoc toks stmt=
      case stmt of
           HsGeneratorAtom (SrcLoc _ _ r c) p e ->
                                  let (startLoc,_)=startEndLoc toks p
                                      (_,endLoc)  =startEndLoc toks e
                                  in (startLoc,endLoc)
           HsQualifierAtom e   -> startEndLoc toks e
           HsLetStmtAtom ds    -> if ds==[]
                                   then (simpPos0,simpPos0)
                                   else let (startLoc,_)= startEndLoc toks (ghead "StartEndLoc:HsStmtAtom" ds)
                                            (_,endLoc)  = startEndLoc toks (glast "StartEndLoc:HsStmtAtom" ds)
                                        in (startLoc,endLoc)
           HsLastAtom e        ->startEndLoc toks e

instance (StartEndLoc i,StartEndLoc e)=>StartEndLoc (HsFieldI i e) where
    startEndLoc toks (HsField i e)=let (startLoc,_)=startEndLoc toks i
                                       (_,endLoc)=startEndLoc toks e
                                   in (startLoc,endLoc)

instance StartEndLoc HsAltP where
    startEndLoc toks (HsAlt l p rhs ds)=let (startLoc,_)=startEndLoc toks p
                                            (_,endLoc)=if ds==[] then startEndLoc toks rhs
                                                                 else startEndLoc toks (glast "StartEndLoc:HsAltP" ds)
                                        in (startLoc,endLoc)

instance StartEndLoc RhsP where
   startEndLoc toks (HsBody e)=startEndLoc toks e

   startEndLoc toks (HsGuard es)=if es==[] then (simpPos0,simpPos0)
                                           else let (_,e1,_)=ghead "StartEndLoc:RhsP" es
                                                    (_,_,e2)=glast "StartEndLoc:RhsP" es
                                                    (startLoc,_)=startEndLoc toks e1
                                                    (_,endLoc)=startEndLoc toks e2
                                                in extendForwards toks startLoc endLoc isBar

instance StartEndLoc (HsIdentI PNT) where
    startEndLoc toks ident =
       case ident of
           HsVar i  ->startEndLoc toks i
           HsCon i  ->startEndLoc toks i

instance StartEndLoc [PNT] where
    startEndLoc toks pnts
       = if pnts==[] then (simpPos0, simpPos0)
           else let (startPos, _) = startEndLoc toks (head pnts)
                    (_,      endPos) = startEndLoc toks (last pnts)
                in (startPos, endPos)

instance StartEndLoc (HsImportDeclI ModuleName PNT)  where
     startEndLoc toks (HsImportDecl (SrcLoc _ _ row col) modName qual  as Nothing)
        = let startPos=fst (startEndLoc toks modName)
              endPos = if isJust as then snd (startEndLoc toks (fromJust as))
                                    else snd (startEndLoc toks modName)
          in extendForwards toks startPos endPos isImport

     startEndLoc toks (HsImportDecl (SrcLoc _ _ row col) modName qual as (Just (_, ents)))
         = let startPos = fst (startEndLoc toks modName)
               endPos = if ents == [] then if isJust as then  snd (startEndLoc toks (fromJust as))
                                                        else  snd (startEndLoc toks modName)
                                      else snd (startEndLoc toks (glast "startEndLocImport" ents))
           in extendBothSides toks startPos endPos isImport isCloseBracket


instance StartEndLoc  [HsExportSpecI ModuleName PNT] where
   startEndLoc toks es
     = if es == [] then (simpPos0, simpPos0)
                   else let (startLoc, _) = startEndLoc toks $ head es
                            (_, endLoc)   = startEndLoc toks $ last es
                        in (startLoc, endLoc)
                        -- in extendBothSides toks startLoc endLoc isOpenBracket isCloseBracket


instance StartEndLoc (HsExportSpecI ModuleName PNT) where
     startEndLoc toks (EntE ent) =startEndLoc toks ent

     startEndLoc toks (ModuleE moduleName) = let (startPos, endPos) = startEndLoc toks moduleName
                                             in extendForwards toks startPos endPos isModule



instance StartEndLoc(EntSpec PNT) where
      startEndLoc toks (Var i)=startEndLoc toks i   --- x (a variable identifier)

      startEndLoc toks (Abs i) =startEndLoc toks i   -- T, C

      startEndLoc toks (AllSubs i) =let (startPos, endPos) =startEndLoc toks i -- T(..), C(..)
                                    in extendBackwards toks startPos endPos isCloseBracket
      startEndLoc toks (ListSubs i ents)= let (startPos, _) = startEndLoc toks i --T (C_1, ...,C_n, f1,...f_n)
                                              (_, endPos)   = startEndLoc toks (glast "startEnPosListSubs" ents)
                                          in extendBackwards toks startPos endPos isCloseBracket

instance StartEndLoc ModuleName where
   startEndLoc toks (SN modName (SrcLoc _ _ row col)) = ((row,col), (row,col))

instance StartEndLoc [EntSpec PNT] where
      startEndLoc toks ents
        = if ents==[] then (simpPos0,simpPos0)
                      else let (startPos, _)=startEndLoc toks $ head ents
                               (_,  endPos) =startEndLoc toks $ last ents
                           in (startPos,endPos)
                --         in extendBothSides toks startPos endPos isHiding isCloseBracket

instance StartEndLoc PNT where
     startEndLoc toks pnt =
        case pnt of
          PNT pn  _ (N (Just (SrcLoc _ _ row col)))->((row,col),(row,col))
          _                                        ->(simpPos0,simpPos0)  {-Shouldn't cause any problems here, as in a normal
                                                                            AST, every PNT has a source location. -}


instance (Eq i, Eq t, StartEndLoc i, StartEndLoc t,StartEndLoc [i]) =>StartEndLoc (HsConDeclI i t c) where
   startEndLoc toks (HsConDecl _ is c i ds)
      = let (startLoc, _) = startEndLoc toks is
            (_, endLoc)   = if ds==[] then startEndLoc toks i
                                      else startEndLoc toks (last ds)
        in (startLoc, endLoc)

   startEndLoc toks (HsRecDecl _ is c i ds)
      = let (startLoc, _) = startEndLoc toks is
            (_, endLoc)   = if ds==[] then startEndLoc toks i
                                      else startEndLoc toks (last ds)
        in (startLoc, endLoc)

instance (StartEndLoc t)=>StartEndLoc (HsBangType t) where
   startEndLoc toks (HsBangedType t) = startEndLoc toks t

   startEndLoc toks (HsUnBangedType t) = startEndLoc toks t

instance (StartEndLoc t, StartEndLoc [i]) => StartEndLoc ([i], HsBangType t) where

   startEndLoc toks (x,y)
     = let (startLoc, endLoc) = startEndLoc toks y
         in  extendBackwards toks startLoc endLoc isCloseBrace



instance StartEndLoc HsDeclP where

   startEndLoc toks (Dec (HsTypeDecl (SrcLoc _ _ r c) tp t))
      = let (startLoc, _) = startEndLoc toks tp
            (_ , endLoc)  = startEndLoc toks t
        in extendForwards toks startLoc endLoc isType

   startEndLoc toks (Dec (HsDataDecl loc c tp decls is))
        = let (startLoc, _) = startEndLoc toks tp
              (_, endLoc)  = if is == [] then startEndLoc toks (glast "StartEndLoc:HsDeclP1" decls)
                                        else startEndLoc toks is
          in extendForwards toks startLoc endLoc isData

   startEndLoc toks (Dec (HsNewTypeDecl loc c tp decls is))
        = let (startLoc, _) = startEndLoc toks tp
              (_, endLoc) = if is == [] then startEndLoc toks decls
                                        else startEndLoc toks is
          in extendForwards toks startLoc endLoc isNewtype

   startEndLoc toks (Dec (HsDefaultDecl _ ts))
      = let (startLoc, _) = startEndLoc toks (head ts)
            (_ , endLoc) = startEndLoc toks (last ts)
        in extendForwards toks startLoc endLoc isDefault

   startEndLoc toks (Dec (HsInfixDecl _ _ is))
      = let (startLoc, _) = startEndLoc toks (head is)
            (_, endLoc)   = startEndLoc toks (last is)
        in extendForwards toks startLoc endLoc isFixty

   startEndLoc toks d@(Dec (HsFunBind _ ms))
      = let (startLoc, _) = startEndLoc toks (ghead "startEndLoc:HsDeclP3" ms)
            (_,   endLoc) = if ms == [] then (simpPos0, simpPos0)
                                        else startEndLoc toks (glast "startEndLoc:HsDeclP4" ms)
        in (startLoc, endLoc)
   startEndLoc toks t@(Dec (HsPatBind _  p rhs ds))
       = let (startLoc, _) = startEndLoc toks p
             (_, endLoc)   = if ds ==[] then startEndLoc toks rhs
                                        else startEndLoc toks (glast "startEndLoc:HsDeclP5" ds)
	     locs = srcLocs t
             (startLoc1,endLoc1) = (if startLoc == simpPos0 && locs /=[] then ghead "getStartEndLoc" locs
                                                                   else startLoc,
				    if endLoc == simpPos0 && locs /= [] then glast "getStartEndLoc" locs
                                                                         else endLoc)
             toks1 = gtail "startEndLoc:HsPatBind" (dropWhile (\t->tokenPos t /= endLoc1) toks)
	     endLoc2 = if toks1==[]
		       then endLoc1
                       else let toks2 = takeWhile (\t -> isSpecialTok t && needmore toks t) toks1
                            in if toks2 == [] || all (\t-> isWhiteSpace t) toks2
			       then endLoc1
                               else (tokenPos.glast "startEndLoc::HsMatchP") toks2
	 in (startLoc1, endLoc2)
    where
        isSpecialTok t = isWhiteSpace t  || isCloseBracket t || isOpenBracket t || isOpenSquareBracket t
                      || isCloseSquareBracket t
        needmore toks t = case  isCloseBracket t of
                            True -> let openBrackets = length $ filter isOpenBracket toks
                                        closeBrackets = length $ filter isCloseBracket toks
                                    in  closeBrackets < openBrackets
                            False -> case isCloseSquareBracket t of
                                      True -> let openSqBrackets = length $ filter isOpenSquareBracket toks
                                                  closeSqBrackets = length $ filter isCloseSquareBracket toks
                                              in  closeSqBrackets < openSqBrackets
                                      False -> True




   startEndLoc toks (Dec (HsTypeSig _ is c t))
      = let (startLoc, _) = startEndLoc toks (ghead "startEndLoc:HsDeclP6" is)
            (_, endLoc)   = startEndLoc toks t
        in (startLoc, endLoc)

   startEndLoc toks decl@(Dec (HsClassDecl loc c tp funDeps  ds))
      = let locs = srcLocs decl
            (startLoc, endLoc)
              = if locs == [] then (simpPos0, simpPos0)
                 else (head locs, last locs)
        in extendForwards toks startLoc endLoc isClass

   startEndLoc toks decl@(Dec (HsInstDecl loc i c t ds))
     = let locs = srcLocs decl
           (startLoc, endLoc)
              = if locs == [] then (simpPos0, simpPos0)
                 else (head locs, last locs)
        in extendForwards toks startLoc endLoc isInstance


{-
   startEndLoc toks (Dec (HsPrimitiveTypeDecl _ c tp))
     = let (startLoc, endLoc) = startEndLoc toks tp
       in extendForward toks startLoc endLoc isData


   startEndLoc toks (Dec (HsPrimitiveBind _ i t))
     = let (startLoc, _) = startEndLoc toks i
           (_, endLoc)   = stratEndLoc toks t
       in  extendForward toks startLoc endLoc isPrimitive
-}

---------------End of the class StartEndLoc----------------------------------------
-}

--------------------------------------------------------------------------------------------------------
-- This function should be the interface function for fetching start and end locations of a AST phrase in the source.
-- TODO: restore Printable t below
-- getStartEndLoc::(Term t, StartEndLoc t,Printable t)=>[PosToken]->t->(SimpPos,SimpPos)
-- xxxxxxx
-- getStartEndLoc::(Term t)=>[PosToken]->t->(SimpPos,SimpPos)
getStartEndLoc::(Term t)=>[PosToken]->GHC.GenLocated GHC.SrcSpan t ->(SimpPos,SimpPos)

getStartEndLoc toks t
  = let (startPos',endPos') = startEndLocGhc toks t
        locs = srcLocs t
        (startPos,endPos) = (if startPos' == simpPos0 && locs /=[] then ghead "getStartEndLoc" locs
                                                                   else startPos',
                             if endPos' == simpPos0 && locs /= [] then glast "getStartEndLoc" locs
                                                                  else endPos')
    in (startPos, endPos)
{- ++AZ++ old version
getStartEndLoc::(Term t, StartEndLoc t)=>[PosToken]->t->(SimpPos,SimpPos)
getStartEndLoc toks t
  = let (startPos',endPos') = startEndLoc toks t
        locs = srcLocs t
        (startPos,endPos) = (if startPos' == simpPos0 && locs /=[] then ghead "getStartEndLoc" locs
                                                                   else startPos',
                             if endPos' == simpPos0 && locs /= [] then glast "getStartEndLoc" locs
                                                                  else endPos')
    in (startPos, endPos)
-}

-- ---------------------------------------------------------------------

startEndLocGhc toks t@(GHC.L l _) =
  case l of
    (GHC.RealSrcSpan ss) ->
      ((GHC.srcSpanStartLine ss,GHC.srcSpanStartCol ss),
       (GHC.srcSpanEndLine ss,GHC.srcSpanEndCol ss))
    (GHC.UnhelpfulSpan _) -> ((0,0),(0,0))
  
-- ---------------------------------------------------------------------



{-
-- this function has problems whegtn they encounter sth. like [.....[p]]/
extendBothSides  toks startLoc endLoc  forwardCondFun backwardCondFun
       =let (toks1,toks2)=break (\t->tokenPos t==startLoc) toks
            toks21=gtail ("extendBothSides" ++ (show (startLoc, endLoc, toks2))  ) $ dropWhile (\t->tokenPos t /=endLoc) toks2
            firstLoc=case (dropWhile (not.forwardCondFun) (reverse toks1)) of
                             [] -> startLoc    -- is this the correct default?
                             l  -> (tokenPos.ghead "extendBothSides:lastTok") l
            lastLoc =case (dropWhile (not.backwardCondFun) toks21) of
                            [] ->endLoc   --is this a correct default?
                            l -> (tokenPos.ghead "extendBothSides:lastTok") l
        in (firstLoc, lastLoc)

extendForwards toks startLoc endLoc forwardCondFun
       =let toks1=takeWhile (\t->tokenPos t /= startLoc) toks
            firstLoc=case (dropWhile (not.forwardCondFun) (reverse toks1)) of
                       [] ->startLoc  -- is this the correct default?
                       l -> (tokenPos.ghead "extendForwards") l
        in (firstLoc, endLoc)

extendBackwards toks startLoc endLoc backwardCondFun
       = let toks1= gtail "extendBackwards"  $ dropWhile (\t->tokenPos t /=endLoc) toks
             lastLoc=case (dropWhile (not.backwardCondFun) toks1) of
                          [] ->endLoc -- is this the correct default?
                          l ->(tokenPos. ghead "extendBackwards") l
         in (startLoc, lastLoc)

------------------Some functions for associating comments with syntax phrases.---------------------------
{- Note: We assume that a comment before t belongs to t only if there is at most one blank line between them,
         and a cooment after t belongs to t only it the comment starts at the last line of t.
-}

{-Get the start&end location of syntax phrase t, then extend the end location to cover the comment/white spaces
  or new line which starts in the same line as the end location-}
startEndLocIncFowComment::(Term t, Printable t,StartEndLoc t)=>[PosToken]->t->(SimpPos,SimpPos)
startEndLocIncFowComment toks t
       =let (startLoc,endLoc)=getStartEndLoc toks t
            toks1= gtail "startEndLocIncFowComment"  $ dropWhile (\t->tokenPos t/=endLoc) toks
            toks11 = let (ts1, ts2) = break hasNewLn toks1
                     in (ts1 ++ if ts2==[] then [] else [ghead "startEndLocInFowComment" ts2])
         in  if toks11/=[] && all (\t->isWhite t || endsWithNewLn t) toks11
             then (startLoc, tokenPos (glast "startEndLocIncFowComment" toks11))
             else (startLoc, endLoc)


{-get the start&end location of t in the token stream, then extend the end location to cover
  the following '\n' if there is no other characters (except white space) between t and the '\n'
-}
startEndLocIncFowNewLn::(Term t, Printable t,StartEndLoc t)=>[PosToken]->t->(SimpPos,SimpPos)
startEndLocIncFowNewLn toks t
  =let (startLoc,endLoc)=getStartEndLoc toks t
       toks1 = dropWhile isWhiteSpace $ gtail "startEndLocIncFowNewLn"  $ dropWhile (\t->tokenPos t /=endLoc) toks
       nextTok= if toks1==[] then defaultToken else head toks1
   in if isNewLn nextTok
        then (startLoc, tokenPos nextTok)
        else (startLoc, endLoc)

{-get the start&end loation of t in the token stream, then extend the start and end location to
  cover the preceding and folllowing comments.
-}
startEndLocIncComments::(Term t, StartEndLoc t,Printable t)=>[PosToken]->t->(SimpPos,SimpPos)
startEndLocIncComments toks t
  =let (startLoc,endLoc)=getStartEndLoc toks t
       (toks11,toks12)= let (ts1,ts2) = break (\t->tokenPos t == startLoc) toks
                            (ts11, ts12) = break hasNewLn (reverse ts1)
                        in (reverse ts12, reverse ts11++ts2)
       toks12'=takeWhile (\t->tokenPos t /=startLoc) toks12
       startLoc'=
         if all isWhite  toks12'
           then  -- group the toks1 according to lines in a reverse order.
                 let  groupedToks=reverse $ groupTokensByLine toks11
                      -- empty lines right before t
                      emptyLns=takeWhile (all (\t->isWhiteSpace t || isNewLn t )) groupedToks
                      lastComment=if length emptyLns <=1  -- get the comment if there is any
                                    then takeWhile (all isWhite) $ takeWhile (any isComment) $ dropWhile
                                               (all (\t->isWhiteSpace t || isNewLn t)) groupedToks
                                    else [] -- no comment
                      toks1'=if lastComment /=[] then concat $ reverse (emptyLns ++ lastComment)
                                                 else []
                 in if toks1'==[]
                       then if toks12'/=[]
                              then (tokenPos (ghead "startEndLocIncComments"  toks12'))  --there is no comment before t
                              else startLoc
                       --there is a comment before t
                       else tokenPos (ghead "startEndLocIncComments"  toks1')
           else startLoc
       -- tokens after t
       toks2=gtail "startEndLocIncComments1"  $ dropWhile (\t->tokenPos t/=endLoc) toks
       -- toks21 are those tokens that are in the same line with the last line of t
       (toks21,tok22)= let (ts11, ts12) = break hasNewLn toks2
                       in (ts11 ++ if ts12==[] then [] else [ghead "startEndLocIncComments" ts12],
                                                             gtail "startEndLocIncComments2" ts12)
    in if toks21==[] then (startLoc',endLoc)  -- no following comments.
        else if all (\t->isWhite t || endsWithNewLn t) toks21 --get the following white tokens in the same
                                                              --line of the last token of t
               then (startLoc', tokenPos (last toks21))
               else (startLoc', endLoc)

--Create a list of white space tokens.
whiteSpacesToken::SimpPos->Int->[PosToken]
whiteSpacesToken (row,col) n
  |n>0        = [(Whitespace,(Pos 0 row col,replicate n ' '))]
  |otherwise  = []

-------------------------------------------------------------------------------------------------

adjustOffset::Int->[PosToken]->Bool->[PosToken]
adjustOffset offset [] _ = []
adjustOffset offset toks firstLineIncluded
     = let groupedToks = groupBy (\x y->tokenRow x==tokenRow y) toks  --groupedToks/=[], no problem with 'head'
           --if firstLineIncluded is False, the offset of the first line won't be ajusted.
       in if offset>=0 then if firstLineIncluded
                               then concatMap (doAddWhites offset) groupedToks
                               else ghead "adjustOffset" groupedToks ++ concatMap (doAddWhites offset) (tail groupedToks)
                       else if firstLineIncluded
                               then concatMap (doRmWhites  (-offset)) groupedToks
                               else ghead "adjustOffset" groupedToks ++ concatMap (doRmWhites  (-offset)) (tail groupedToks)

-}
