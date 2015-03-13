-----------------------------------------------------------------------------
-- |
-- Module      :  DuplicateCode
-- Copyright   :  (c) Christopher Brown 2007
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a duplicate code analysis tool
-- that works over the HaRe infrastructure.
-- Comparing two Haskell source files at the token stream level
-- this module constructs a report based on the structural
-- duplication of the two source files.
--
-- VERSION
-- -------
-- 02 January 2007: 0.0 -- basic implementation set up.
-- 22 Januray 2007: 0.1 -- fully working alpha equivalence with textual output
--                         in the form of a report.
--
-- 31 July 2008: 0.2  -- rewrite to compare expressions via AST using
--                       avoidance of capture.
--
-----------------------------------------------------------------------------

module DuplicateCode where
import System.Time
import PrettyPrint
import System.IO.Unsafe
import PosSyntax hiding (ModuleName, HsName, SN)
import SourceNames
import ScopeModule
import UniqueNames hiding (srcLoc)
import HsName
import HsLexerPass1
import PNT
import TiPNT
import SimpleGraphs(reverseGraph,reachable)
import HsTokens
import RefacTypeSyn
import RefacLocUtils
import Data.Char
import GHC.Unicode
import AbstractIO
import Data.Maybe
import Data.List
import RefacUtils
import LocalSettings (reportFilePath,transFilePath,answerFilePath)
import Data.Function
import RefacGenFold (expToPat)


-- as this module is not a transformation, we will not need to modify
-- the source files in question. It is still necessary to import the
-- HaRe API, in all it's glory, to gain access to tree traversals.

type Group = ([HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP],[HsExpP])

emptyGroup = ([],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[])


-- define the clone type; E = clone is an Expression;
--                        G = clone is a list of Generators: monadic patterns;
--                        S = clone is a monadic sequence (including generators).
data CloneType = E (HsExpP, String) | G (HsStmtP, String) | S (HsStmtP, String)
                    deriving (Eq, Show, Read, Ord)

-- the filenames need to be given with their full file path
-- unless they appear in the same directory as the executable.

-- We use the concept of a line number quite a lot, so let's define it:

type LineNumber = Int

-- the idea is to look for expressions of a particular
-- size and repetition. For the moment, we use two constants
-- to define this...
-- expressionSize = 5
-- expression size is a variable to determine the size of the expressions
-- we need to look for expressions as close to size 10 as possible.

expressionRep = 1
-- expressionRep determines how many times a particular expression
-- may occur in a code clone.
-- for example: x + y + z      x + y occurs twice...


duplicateCode args
  = do let
           fileName1    = args!!0
           expressionSize = read (args!!1) :: Int
       AbstractIO.putStrLn "duplicateCode Analysis"
       timeone <- AbstractIO.getClockTime
       -- we work over a project, so we take the name of the current
       -- (hopefully main module) and work over it all, in turn....
       let fileName2 = fileName1
       modName <- fileNameToModName fileName1

       -- the analysis should be perform over the main module...
       -- get a list of all the modules that are imported directly, or indirectly,
       -- by Main...
       servers<-serverModsAndFiles modName -- returns [(module name ,filename)]
       -- we arn't interested in the libraries yet though.
       -- I guess it's OK to strip away those not defined in current directory...

       let directory = getDirectory fileName1
           servers' = stripServers servers directory
       rest <- parseAll expressionSize servers' -- hardServers
       modInfo1@(inscps1, exps1, mod1, tokList1) <- parseSourceFile fileName1
       -- for each module in our project, we need to normalise the token streams.
       -- we then concatenate the token streams together, and perform
       -- a big analysis over that. Question? How do we remember
       -- which module we are talking about?
       -- tokList1' <- normaliseTokens fileName1 mod1 tokList1
       -- AbstractIO.putStrLn tokList1'

       -- normalize the AST. We Alpa-Reduce all local variables
       -- to "$" (as they can be passed in as parameters)
       -- top level decs are left alone.
       -- mod' <- renameAST mod1

       asts <- genExpList expressionSize tokList1 mod1
       let groupAST = groupExps asts emptyGroup
       duplications <- loop expressionSize ((mod1, tokList1, fileName1, groupAST):rest)
       duplications' <- removeDuplicates (concat duplications)
       -- display generates a report of the duplications
       -- and writes them to a file for further processing...

       let display = prettyPrint duplications' (map (\(x,y,z,_) -> (y,z)) ((mod1, tokList1, fileName1, groupAST):rest))
           duplications'' = prettyPrint2 duplications' (map (\(x,y,z,_) -> (y,z)) ((mod1, tokList1, fileName1, groupAST):rest))
       AbstractIO.writeFile reportFilePath display

       -- for now, print this to the screen also
       AbstractIO.writeFile transFilePath (show duplications'')
       AbstractIO.writeFile answerFilePath ""
       AbstractIO.putStrLn ("Clone analysis complete. Report delivered to: " ++ reportFilePath)
       timetwo <- AbstractIO.getClockTime
       AbstractIO.putStrLn $ show $ diffClockTimes timetwo timeone

--Takes an AST and returns a list of tuples containing the string equivalent of the
-- Expression name, and the start & finish locations of the Expression
-- genExpList :: (Term t) => t -> [HsExpP]
genExpList expressionSize tokList ast = applyTU (full_tdTU ( constTU [] `adhocTU` isExp)) ast
    where

             isExp (Exp (HsTuple [])) = return []
             isExp (Exp (HsList [])) = return []
             isExp (Exp (HsLet _ _)) = return []
             isExp (a::HsExpP)= do
                                let (start, end)  = getStartEndLoc tokList a
                                let tokExpression = getToks (start, end) tokList
                                if (length (filter (not. isWhite') tokExpression)) < expressionSize
                                     then return []
                                     else return [a]


getGroup :: HsExpP -> Group -> [HsExpP]
getGroup (Exp (HsId x)) g = getId g
getGroup (Exp (HsLit s i)) g = getLit g
getGroup (Exp (HsInfixApp _ _ _)) g = getInfix g
getGroup (Exp (HsApp _ _)) g = getApp g
getGroup (Exp (HsNegApp _ _)) g = getNegApp g
getGroup (Exp (HsLambda _ _)) g = getLambda g
getGroup (Exp (HsLet _ _)) g = getLet g
getGroup (Exp (HsIf _ _ _)) g = getIf g
getGroup (Exp (HsCase _ _)) g = getCase g
getGroup (Exp (HsDo _)) g = getDo g
getGroup (Exp (HsTuple _)) g = getTuple g
getGroup (Exp (HsList _)) g = getList g
getGroup (Exp (HsParen _)) g = getParen g
getGroup (Exp (HsLeftSection _ _)) g = getLeft g
getGroup (Exp (HsRightSection _ _)) g = getRight g
getGroup (Exp (HsRecConstr _ _ _)) g = getRecConstr g
getGroup (Exp (HsRecUpdate _ _ _)) g = getRecUpdate g
getGroup (Exp (HsEnumFrom _)) g = getEnumFrom g
getGroup (Exp (HsEnumFromTo _ _)) g = getEnumFromTo g
getGroup (Exp (HsEnumFromThen _ _)) g = getEnumFromThen g
getGroup (Exp (HsEnumFromThenTo _ _ _)) g = getEnumFromThenTo g
getGroup (Exp (HsListComp _)) g = getListComp g
getGroup (Exp (HsExpTypeSig _ _ _ _)) g = getTypeSig g
getGroup (Exp (HsAsPat _ _)) g = getAsPat g
getGroup (Exp (HsWildCard)) g = getWildCard g
getGroup (Exp (HsIrrPat _)) g = getIrrPat g

getId :: Group -> [HsExpP]
getId (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = a
getLit :: Group -> [HsExpP]
getLit (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = b
getInfix :: Group -> [HsExpP]
getInfix (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = c
getApp :: Group -> [HsExpP]
getApp (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = d
getNegApp :: Group -> [HsExpP]
getNegApp (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = e
getLambda :: Group -> [HsExpP]
getLambda (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = f
getLet :: Group -> [HsExpP]
getLet (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = g
getIf :: Group -> [HsExpP]
getIf (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = h
getCase :: Group -> [HsExpP]
getCase (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = i
getDo :: Group -> [HsExpP]
getDo (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = j
getTuple :: Group -> [HsExpP]
getTuple (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = k
getList :: Group -> [HsExpP]
getList (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = l
getParen :: Group -> [HsExpP]
getParen (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = m
getLeft :: Group -> [HsExpP]
getLeft (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = n
getRight :: Group -> [HsExpP]
getRight (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = o
getRecConstr :: Group -> [HsExpP]
getRecConstr (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = p
getRecUpdate :: Group -> [HsExpP]
getRecUpdate (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = q
getEnumFrom :: Group -> [HsExpP]
getEnumFrom (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = r
getEnumFromTo :: Group -> [HsExpP]
getEnumFromTo (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = s
getEnumFromThen :: Group -> [HsExpP]
getEnumFromThen (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = t
getEnumFromThenTo :: Group -> [HsExpP]
getEnumFromThenTo (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = u
getListComp :: Group -> [HsExpP]
getListComp (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = v
getTypeSig :: Group -> [HsExpP]
getTypeSig (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = w
getAsPat :: Group -> [HsExpP]
getAsPat (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = x
getWildCard :: Group -> [HsExpP]
getWildCard (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = y
getIrrPat :: Group -> [HsExpP]
getIrrPat (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = z



groupExps :: [HsExpP] -> Group -> Group
groupExps [] g = g
groupExps (e@(Exp (HsId x)):es) g = groupExps es (addId e g)
groupExps (e@(Exp (HsLit s i)):es) g = groupExps es (addLit e g)
groupExps (e@(Exp (HsInfixApp _ _ _)):es) g = groupExps es (addInfix e g)
groupExps (e@(Exp (HsApp _ _)):es) g = groupExps es (addApp e g)
groupExps (e@(Exp (HsNegApp _ _)):es) g = groupExps es (addNegApp e g)
groupExps (e@(Exp (HsLambda _ _)):es) g = groupExps es (addLambda e g)
groupExps (e@(Exp (HsLet _ _)):es) g = groupExps es (addLet e g)
groupExps (e@(Exp (HsIf _ _ _)):es) g = groupExps es (addIf e g)
groupExps (e@(Exp (HsCase _ _)):es) g = groupExps es (addCase e g)
groupExps (e@(Exp (HsDo _)):es) g = groupExps es (addDo e g)
groupExps (e@(Exp (HsTuple _)):es) g = groupExps es (addTuple e g)
groupExps (e@(Exp (HsList _)):es) g = groupExps es (addList e g)
groupExps (e@(Exp (HsParen _)):es) g = groupExps es (addParen e g)
groupExps (e@(Exp (HsLeftSection _ _)):es) g = groupExps es (addLeft e g)
groupExps (e@(Exp (HsRightSection _ _)):es) g = groupExps es (addRight e g)
groupExps (e@(Exp (HsRecConstr _ _ _)):es) g = groupExps es (addRecConstr e g)
groupExps (e@(Exp (HsRecUpdate _ _ _)):es) g = groupExps es (addRecUpdate e g)
groupExps (e@(Exp (HsEnumFrom _)):es) g = groupExps es (addEnumFrom e g)
groupExps (e@(Exp (HsEnumFromTo _ _)):es) g = groupExps es (addEnumFromTo e g)
groupExps (e@(Exp (HsEnumFromThen _ _)):es) g = groupExps es (addEnumFromThen e g)
groupExps (e@(Exp (HsEnumFromThenTo _ _ _)):es) g = groupExps es (addEnumFromThenTo e g)
groupExps (e@(Exp (HsListComp _)):es) g = groupExps es (addListComp e g)
groupExps (e@(Exp (HsExpTypeSig _ _ _ _)):es) g = groupExps es (addTypeSig e g)
groupExps (e@(Exp (HsAsPat _ _)):es) g = groupExps es (addAsPat e g)
groupExps (e@(Exp (HsWildCard)):es) g = groupExps es (addWildCard e g)
groupExps (e@(Exp (HsIrrPat _)):es) g = groupExps es (addIrrPat e g)

addId :: HsExpP -> Group -> Group
addId e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = ((a++[e1]),b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addLit :: HsExpP -> Group -> Group
addLit e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,(b++[e1]),c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addInfix :: HsExpP -> Group -> Group
addInfix e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,(c++[e1]),d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addApp :: HsExpP -> Group -> Group
addApp e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,(d++[e1]),e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addNegApp :: HsExpP -> Group -> Group
addNegApp e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,(e++[e1]),f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addLambda :: HsExpP -> Group -> Group
addLambda e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,(f++[e1]),g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addLet :: HsExpP -> Group -> Group
addLet e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,(g++[e1]),h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addIf :: HsExpP -> Group -> Group
addIf e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,(h++[e1]),i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addCase :: HsExpP -> Group -> Group
addCase e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,(i++[e1]),j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addDo :: HsExpP -> Group -> Group
addDo e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,(j++[e1]),k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addTuple :: HsExpP -> Group -> Group
addTuple e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,(k++[e1]),l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addList :: HsExpP -> Group -> Group
addList e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,(l++[e1]),m,n,o,p,q,r,s,t,u,v,w,x,y,z)
addParen :: HsExpP -> Group -> Group
addParen e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,(m++[e1]),n,o,p,q,r,s,t,u,v,w,x,y,z)
addLeft :: HsExpP -> Group -> Group
addLeft e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,(n++[e1]),o,p,q,r,s,t,u,v,w,x,y,z)
addRight :: HsExpP -> Group -> Group
addRight e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,(o++[e1]),p,q,r,s,t,u,v,w,x,y,z)
addRecConstr :: HsExpP -> Group -> Group
addRecConstr e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,(p++[e1]),q,r,s,t,u,v,w,x,y,z)
addRecUpdate :: HsExpP -> Group -> Group
addRecUpdate e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,(q++[e1]),r,s,t,u,v,w,x,y,z)
addEnumFrom :: HsExpP -> Group -> Group
addEnumFrom e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,(r++[e1]),s,t,u,v,w,x,y,z)
addEnumFromTo :: HsExpP -> Group -> Group
addEnumFromTo e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,(s++[e1]),t,u,v,w,x,y,z)
addEnumFromThen :: HsExpP -> Group -> Group
addEnumFromThen e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,(t++[e1]),u,v,w,x,y,z)
addEnumFromThenTo :: HsExpP -> Group -> Group
addEnumFromThenTo e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,(u++[e1]),v,w,x,y,z)
addListComp :: HsExpP -> Group -> Group
addListComp e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,(v++[e1]),w,x,y,z)
addTypeSig :: HsExpP -> Group -> Group
addTypeSig e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,(w++[e1]),x,y,z)
addAsPat :: HsExpP -> Group -> Group
addAsPat e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,(x++[e1]),y,z)
addWildCard :: HsExpP -> Group -> Group
addWildCard e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,w,r,s,t,u,v,w,x,(y++[e1]),z)
addIrrPat :: HsExpP -> Group -> Group
addIrrPat e1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z)
 = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,(z++[e1]))
loop _ [] = return []
loop eSize a@((x,y,m,g):xs)
  = do
        let list' = numberList 0 ((x,y,m,g):xs)
        dups <- mapM (calculateInstances eSize (x,y,m,g)) ((x,y,m,g):xs)
        dups' <- loop' eSize ((tail list')++[(x,y,m,g,0)]) 0
        return (dups ++ dups')
        -- return dups'
          where
             numberList _ [] = []
             numberList n ((x,y,m,g):xs) = (x,y,m,g,n):numberList (n+1) xs


loop' _ [] _ = return []
loop' eSize ((x,y,m,g,z):xs) n
 | z == n = return []
 | otherwise = do
                  dups <- mapM (calculateInstances eSize (x,y,m,g)) ((x,y,m,g):(map (\(x,y,m,g,z) -> (x,y,m,g)) xs))
                  rest <- loop' eSize (xs++[(x,y,m,g,z)]) n
                  -- return rest
                  return (dups ++ rest)


parseAll _ [] = return []
parseAll eSize ((m,f):xs) = do
                          (_,_,mod, tok) <- parseSourceFile f
                          rest <- parseAll eSize xs
                          modName <- fileNameToModName f
                          asts <- genExpList eSize tok mod
                          let groupAST = groupExps asts emptyGroup
                          return ((mod, tok, f, groupAST) : rest)

normaliseTokens f mod t
  = do
       let whiteRemoved = filter (not. isWhite') t
           normalised = removedIdents f mod whiteRemoved
           normalised' = stringIt normalised
       return normalised'
        where
          removedIdents :: Term t => String -> t -> [PosToken] -> [PosToken]
          removedIdents _ _ [] = []
          removedIdents f mod (a@(Varid, (Pos x y z,s)):xs)
             | findTopLevel f y z mod = a : removedIdents f mod xs
             | otherwise = (Varid, (Pos x y z,"$")) : removedIdents f mod xs
          removedIdents f mod (a@(Conid, (Pos x y z,s)):xs)
             | findTopLevel f y z mod = a : removedIdents f mod xs
             | otherwise = (Conid, (Pos x y z,"$")) : removedIdents f mod xs
          removedIdents f mod (a@(Varsym, (Pos x y z,s)):xs)
             | findTopLevel f y z mod = a : removedIdents f mod xs
             | otherwise = (Varsym, (Pos x y z,"$")) : removedIdents f mod xs
          removedIdents f mod (a@(Consym, (Pos x y z,s)):xs)
             | findTopLevel f y z mod = a : removedIdents f mod xs
             | otherwise = (Consym, (Pos x y z,"$")) : removedIdents f mod xs

          removedIdents f mod (a@(Qvarid, (Pos x y z,s)):xs)
             | findTopLevel f y z mod = a : removedIdents f mod xs
             | otherwise = (Qvarid, (Pos x y z,"$")) : removedIdents f mod xs
          removedIdents f mod (a@(Qconid, (Pos x y z,s)):xs)
             | findTopLevel f y z mod = a : removedIdents f mod xs
             | otherwise = (Qconid, (Pos x y z,"$")) : removedIdents f mod xs
          removedIdents f mod (a@(Qvarsym, (Pos x y z,s)):xs)
             | findTopLevel f y z mod = a : removedIdents f mod xs
             | otherwise = (Qvarsym, (Pos x y z,"$")) : removedIdents f mod xs
          removedIdents f mod (a@(Qconsym, (Pos x y z,s)):xs)
             | findTopLevel f y z mod = a : removedIdents f mod xs
             | otherwise = (Qconsym, (Pos x y z,"$")) : removedIdents f mod xs
          removedIdents f mod (a@(IntLit, (Pos x y z,s)):xs)
             = (IntLit, (Pos x y z, "$")) : removedIdents f mod xs
          removedIdents f mod (a@(FloatLit, (Pos x y z,s)):xs)
             = (FloatLit, (Pos x y z, "$")) : removedIdents f mod xs
          removedIdents f mod (a@(CharLit, (Pos x y z,s)):xs)
             = (CharLit, (Pos x y z, "$")) : removedIdents f mod xs
          removedIdents f mod (a@(StringLit, (Pos x y z,s)):xs)
             = (StringLit, (Pos x y z, "$")) : removedIdents f mod xs
          removedIdents f mod (x:xs) = x: removedIdents f mod xs

          findTopLevel :: Term t => String -> Int -> Int -> t -> Bool
          findTopLevel f x y t = isTopLevelPNT (locToPNT f (x,y) t)

getDirectory :: String -> String
getDirectory f
  = reverse $ dropWhile (=='/') (dropWhile (/='/') (reverse f))

stripServers :: [(ModuleName, String)] -> String -> [(ModuleName, String)]
stripServers [] d = []
stripServers (a@(x,y):xs)  d
 | d == getDirectory y = a : stripServers xs d
 | otherwise           = stripServers xs d

addIndex :: [ [(a,b)] ] -> [ [(a,b,Int)] ]
addIndex (x:xs) = addIndex' 0 x : addIndex xs
                    where
                      addIndex' i ((x,y):xs) = (x,y,i) : addIndex' (i+1) xs


-- removeDuplicates = groupBy (foldExp `on` fst) . nub . concat

removeDuplicates x = do let x' = nubBy sameOccurrence (sort (concat x))

                        es <- mapM renameExp' x'
                        let g' = groupBy (foldExpOrDo `on` (\(x,y,z) -> x)) es
                            x2 = removeSubEntities  $ nubBy (sameOccurrence2 `on` fst) (map (\(x,y,z) -> (y,z)) (concat (remove1Ele g')))
                        es2 <- mapM renameExp' x2
                        let g2 = groupBy (foldExpOrDo `on` (\(x,y,z) -> x)) es2

                        return g2

foldExpOrDo :: HsExpP -> HsExpP -> Bool
foldExpOrDo e@(Exp (HsDo _)) e2@(Exp (HsDo _))
 = foldDoNormal [] [] e e2
foldExpOrDo e1 e2 = foldExp [] [] e1 e2

remove1Ele [] = []
remove1Ele (x:xs)
 | length x == 1 = remove1Ele xs
 | otherwise = x : remove1Ele xs



removeSubEntities' x [] = False
removeSubEntities' (x,z) ((y,m):ys)
  | findEntityWithLocation x y && z == m = True
  | otherwise = removeSubEntities' (x,z) ys

removeSubEntities (x:xs)
  | removeSubEntities' x xs = removeSubEntities2  x (xs++[x])
  | otherwise = x : removeSubEntities2  x (xs++[x])
removeSubEntities [] = []

removeSubEntities2 x (y:ys)
 | x == y = []
 | removeSubEntities' y ys = removeSubEntities2  x (ys++[y])
 | otherwise = y : removeSubEntities2  x (ys++[y])

takeSubEntities (x:xs)
 | removeSubEntities' x xs = x : takeSubEntities2 x (xs++[x])
 | otherwise = takeSubEntities2 x (xs ++ [x])
takeSubEntities2 x (y:ys)
 | x == y = []
 | removeSubEntities' y ys = y : takeSubEntities2 x (ys++[y])
 | otherwise = takeSubEntities2 x (ys++[y])


renameExp' (a,b) = do
                       a' <- renameExp a
                       return (a',a,b)

-- a variation on groupBy; groups by comparing one element to all other elements...
-- groupBy' 		::  (a -> a -> Bool) -> [a] -> [b] -> [[b]]
groupBy' _  []	[]	=  []
groupBy' eq (x:xs) (a:as)	=  (a:ys) : groupBy' eq xs' as'
                              where ((ls,ys),(os, zs)) = span' (eq x) xs as
                                    (xs', as') = filterIt ys xs as

                                    filterIt _ [] [] = ([],[])
                                    filterIt _ [] _  = ([],[])
                                    filterIt _ _ []  = ([],[])
                                    filterIt list1 (x:xs) (y:ys)
                                      | y `elem` list1 = filterIt list1 xs ys
                                      | otherwise = let (ls, zs) = filterIt list1 xs ys in  (x:ls, y:zs)


span'                    :: (a -> Bool) -> [a] -> [b] -> (([a], [b]),([a], [b]))
span' _ xs@[] ys@[]           =  ((xs,ys),(xs, ys))
span' p xs@(x:xs') ds@(a:as')
         | p x          =  let ((ls,ys),(os,zs)) = span' p xs' as' in (((x:ls),(a:ys)),(os,zs))
         | otherwise    =  span' p xs' as'  -- (([],[]),(xs',as'))

calculateInstances expressionSize a@(mod1, tokList1, name1, group) b@(mod2, tokList2, name2, group2)
 = do
       rest <- (applyTU (full_tdTU (constTU [] `adhocTU` inExp)) mod1)
       return rest
     where
       inExp (e1::HsExpP)
         = do
             -- res <- traverseExp a b e1
             -- AbstractIO.putStrLn ("comparing " ++ name1 ++ " with " ++ name2)
             res <- findExp expressionSize a b e1
             if res == []
               then return []
               else return res


findExp _ _ _ (Exp (HsList [])) = return []
findExp _ _ _ (Exp (HsTuple [])) = return []
findExp _ _ _ (Exp (HsLet _ _)) = return []
findExp expressionSize (mod1, tokList1, name1, group1) (mod2, tokList2, name2, group2) e1@(Exp (HsDo _))
 = do
        let (start, end)  = getStartEndLoc tokList1 e1
        let tokExpression = getToks (start, end) tokList1
        if (length (filter (not. isWhite) tokExpression)) < expressionSize
             then return []
             else -- find occurrences of this expression within mod2
              do
               newE1 <- renameExp e1
               occurs <- findExpressionDo (e1,name1) newE1 (mod2, tokList2, name2) (getGroup newE1 group2)
               if occurs == []
                then return []
                else do
                  return [occurs]
findExp expressionSize (mod1, tokList1, name1, group1) (mod2, tokList2, name2, group2) e1
 = do
        -- tokenize expression
        -- tokenized expression must be bigger than
        -- expressionSize!
        let (start, end)  = getStartEndLoc tokList1 e1
        let tokExpression = getToks (start, end) tokList1
        if (length (filter (not. isWhite) tokExpression)) < expressionSize
                then return []
                else -- find occurrences of this expression within mod2
                 do
                  newE1 <- renameExp e1
                  occurs <- findExpression e1 newE1 (mod2, tokList2, name2) (getGroup newE1 group2)
                  if occurs == []
                   then return []
                   else do
                    return [ (e1, name1) : occurs]


-- find the occurrences of e1 within mod1
findExpressionDo (e1@(Exp (HsDo s)),name1) newE1 (mod1, tokList1, name2) (e2:exps)
       | sameOccurrence e1 e2 = do rest <- findExpressionDo (e1,name1) newE1 (mod1, tokList1, name1) exps
                                   return rest
       | otherwise
          = do newE2 <- renameExp e2
               let (pred, stmt2, stmt1) = foldDo [] [] (newE1,e1) (newE2,e2)
               -- error $ show stmt
               if pred
                  then
                    do
                       rest <- findExpressionDo (e1,name1) newE1 (mod1, tokList1, name1) exps
                       return ((stmt1, name1) : ((stmt2, name2) : rest ))
                  else do rest <- findExpressionDo (e1,name1) newE1 (mod1, tokList1, name1) exps
                          return rest
findExpressionDo _ _ _ _ = return []

findExpression _ _ _ [] = return []

findExpression e1 newE1 (mod1, tokList1, name1) (e2:exps)
       | sameOccurrence e1 e2 = do rest <- findExpression e1 newE1 (mod1, tokList1, name1) exps
                                   return rest
       | otherwise
           = do

                newE2 <- renameExp e2
                if foldExp [] [] newE1 newE2
                  then do  -- identify the function
                                 -- that defines this expression
                                 -- the find the free and declared variables from it...
                                 -- error $ show newE2
                         rest <- findExpression e1 newE1 (mod1, tokList1, name1) exps
                         return ( (e2, name1) : rest)

                  else do  rest <- findExpression e1 newE1 (mod1, tokList1, name1) exps
                           return rest

isWhite' x@(t,_) = t==Whitespace || t==Commentstart || t==Comment || t==NestedComment || isOpenBracket x || isCloseBracket x ||
                   isComma x || isOpenSquareBracket x || isCloseSquareBracket x || isIrrefute x


-- find the defining function for a given expression
definingFun e1
  = (fromJust) . (applyTU (once_tdTU (failTU `adhocTU` inFun)))
     where
       inFun d@(Dec (HsFunBind s ms)::HsDeclP)
        | findEntity e1 d = Just d
       inFun d@(Dec (HsPatBind s p e ds)::HsDeclP)
        | findEntity e1 d = Just d
       inFun _ = Nothing

-- foldExp compares two expressions for equality
-- via alpha-renaming
-- foldIdent :: (HsIdent PNT) -> (HsIdent PNT) -> Bool
foldIdent pats pats2 (HsVar x) (HsVar y)
 = x == y && ((not (checkPNTInPat pats x)) && (not (checkPNTInPat pats2 y)))
foldIdent _ _ (HsCon x) (HsCon y) -- constructors are treated like literals?
 = True -- x == y
foldIdent _ _ x y = False
foldWild (HsVar x)
 = isLocalPNT x
foldWild (HsCon x)
 = isLocalPNT x


checkPNTInPat :: [HsPatP] -> PNT -> Bool
checkPNTInPat [] _ = False
checkPNTInPat (p:ps) i
        | defineLoc i == (SrcLoc "__unknown__" 0 0 0) = False
        | defineLoc i == defineLoc (patToPNT p) = True
        | otherwise = checkPNTInPat ps i

findPNTInPat :: Int -> [HsPatP] -> PNT -> Int
findPNTInPat n [] _ = -1
findPNTInPat n (p:ps) i
        | defineLoc i == (SrcLoc "__unknown__" 0 0 0) = -1
        | defineLoc i == defineLoc (patToPNT p) = n
        | otherwise = findPNTInPat (n+1) ps i

foldExp :: [HsPatP] -> [HsPatP] -> HsExpP -> HsExpP -> Bool
foldExp pats pats2 (Exp (HsId x)) (Exp (HsId y))
 | pred1 x y && pos1 x == pos2 y = True
 | pred1 x y && pos1 x /= pos2 y = False
 | (foldIdent pats pats2 x y || (foldWild x && foldWild y)) = True
 | otherwise = False
    where
      pred1 (HsVar x) (HsVar y) = checkPNTInPat pats x && checkPNTInPat pats2 y
      pred1 _ _ = False
      pos1 (HsVar x) = findPNTInPat 0 pats x
      pos2 (HsVar y) = findPNTInPat 0 pats2 y
foldExp pats pats2 (Exp (HsId (HsVar x))) e  -- comparing a variable against any expression should be OK CHECK THIS!
 | isLocalPNT x && (not (checkPNTInPat pats x)) = True -- | pNTtoName x == "$" = True
 | otherwise = False
foldExp pats pats2 e (Exp (HsId (HsVar x)))   -- comparing a variable against any expression should be OK CHECK THIS!
 | isLocalPNT x && (not (checkPNTInPat pats2 x)) = True -- | pNTtoName x == "$" = True
 | otherwise = False
foldExp pats pats2 (Exp (HsParen e1)) e2
 | not (sameOccurrence e1 e2) = foldExp pats pats2 e1 e2
 | otherwise = False
foldExp pats pats2 e1 (Exp (HsParen e2))
 | not (sameOccurrence e1 e2) = foldExp pats pats2 e1 e2
 | otherwise = False
foldExp pats pats2 (Exp (HsLit s lit1)) x   -- (Exp (HsLit s2 (lit2))) -- comparing 2 literals is True!?
  = True -- lit1 == lit2
foldExp pats pats2 x (Exp (HsLit s lit1)) = True
foldExp pats pats2 (Exp (HsInfixApp e1 o1 e2)) (Exp (HsInfixApp e3 o2 e4))  -- check this (different ops!?)
 | foldWild o1 && (pred1 && pred2) = True
 | foldIdent pats pats2 o1 o2 && (pred1 && pred2) = True
     where
       pred1 = foldExp pats pats2 e1 e3
       pred2 = foldExp pats pats2 e2 e4
foldExp pats pats2 a@(Exp (HsApp e1 e2)) b@(Exp (HsApp e3 e4))
  = (foldExp pats pats2 e1 e3) && (foldExp pats pats2 e2 e4)
foldExp pats pats2 (Exp (HsNegApp s e1)) (Exp (HsNegApp s2 e2)) = foldExp pats pats2 e1 e2
foldExp pats pats2 e5@(Exp (HsLambda ps e11)) e4@(Exp (HsLambda ps2 e22))
 = False
foldExp pats pats2 (Exp (HsLet decs1 e1)) (Exp (HsLet decs2 e2)) = False -- check decs?
foldExp pats pats2 (Exp (HsIf e1 e2 e3)) (Exp (HsIf e4 e5 e6))
  = foldExp pats pats2 e1 e4 && foldExp pats pats2 e2 e5 && foldExp pats pats2 e3 e6
foldExp pats pats2 a@(Exp (HsCase e1 alts1)) b@(Exp (HsCase e2 alts2))
 = False
foldExp pats pats2 (Exp (HsList es1)) (Exp (HsList es2))
  = foldExpList pats pats2 es1 es2
foldExp pats pats2 (Exp (HsTuple es1)) (Exp (HsTuple es2))
  = foldExpList pats pats2 es1 es2
foldExp pats pats2 (Exp (HsLeftSection e1 x)) (Exp (HsLeftSection e2 y))
 | foldWild x && foldExp pats pats2 e1 e2 = True
 | foldIdent pats pats2 x y  && foldExp pats pats2 e1 e2 = True
 | otherwise = False
foldExp pats pats2 (Exp (HsRightSection x e1)) (Exp (HsRightSection y e2))
 | foldWild x && foldExp pats pats2 e1 e2 = True
 | foldIdent pats pats2 x y  && foldExp pats pats2 e1 e2 = True
 | otherwise = False
foldExp pats pats2 (Exp (HsEnumFrom e1)) (Exp (HsEnumFrom e2))
 = foldExp pats pats2 e1 e2
foldExp pats pats2 (Exp (HsEnumFromTo e1 e2)) (Exp (HsEnumFromTo e3 e4))
 = foldExp pats pats2 e1 e3 && foldExp pats pats2 e2 e4
foldExp pats pats2 (Exp (HsEnumFromThen e1 e2)) (Exp (HsEnumFromThen e3 e4))
 = foldExp pats pats2 e1 e3 && foldExp pats pats2 e2 e4
foldExp pats pats2 (Exp (HsExpTypeSig _ e1 _ _)) (Exp (HsExpTypeSig _ e2 _ _))
 = foldExp pats pats2 e1 e2
foldExp pats pats2 (Exp (HsAsPat i1 e1)) (Exp (HsAsPat i2 e2))
 | isLocalPNT i1 && foldExp pats pats2 e1 e2     = True
 | i1 == i2 && foldExp pats pats2 e1 e2 = True
 | otherwise = False
foldExp pats pats2 (Exp (HsWildCard)) (Exp (HsWildCard)) = True
foldExp pats pats2 (Exp (HsIrrPat e1)) (Exp (HsIrrPat e2)) = foldExp pats pats2 e1 e2

foldExp _ _ _ _ = False


{- foldAlt :: [HsAltP] -> [HsAltP] -> Bool
foldAlt [] [] = True
foldAlt [] _  = False
foldAlt _ []  = False
foldAlt ((HsAlt s p rhs ds):as) ((HsAlt s1 p1 rhs1 ds1):as1)
  = foldRHS rhs rhs1 && foldAlt as as1

foldRHS (HsBody e1) (HsBody e2)
 = foldExp e1 e2
foldRHS (HsGuard gs1) (HsGuard gs2)
 = foldGuards gs1 gs2
    where
      foldGuards [] [] = True
      foldGuards _ []  = False
      foldGuards [] _  = False
      foldGuards ((s1, e1, e2):gs1) ((s2, e3, e4):gs2)
       = foldExp e1 e3 && foldExp e2 e4 && foldGuards gs1 gs2 -}

foldExpList :: [HsPatP] -> [HsPatP] -> [HsExpP] -> [HsExpP] -> Bool
foldExpList p _ [] [] = True
foldExpList p _ [] _ = False
foldExpList p _ _ [] = False
foldExpList p p2 (x:xs) (y:ys)
  = (foldExp p p2 x y && foldExpList p p2 xs ys)


-- ==========================================================

foldDo :: [HsPatP] -> [HsPatP] -> (HsExpP, HsExpP) -> (HsExpP,HsExpP) -> (Bool, HsExpP, HsExpP)
foldDo pats pats2 (Exp (HsDo stmts1), Exp (HsDo stmts1')) ((Exp (HsDo stmts2)), Exp (HsDo stmts2'))
 | pred = (True, Exp (HsDo res), Exp (HsDo res2))
           where
             (pred, res, res2) = foldStmt pats pats2 (stmts1,stmts1') (stmts2, stmts2')
foldDo _ _ _ _ = (False, defaultExp, defaultExp)

foldStmt :: [HsPatP] -> [HsPatP] -> (HsStmtP, HsStmtP) -> (HsStmtP,HsStmtP) -> (Bool, HsStmtP, HsStmtP)
foldStmt pats pats2 (ss1@(HsGenerator s p1 e1 stmts1),ss2@(HsGenerator _ p1' e1' stmts1'))
                    (ss3@(HsGenerator _ p2 e2 stmts2),ss4@(HsGenerator _ p2' e2' stmts2'))
 {- | wildCardAllPNs p1 == wildCardAllPNs p2 && predExp && pred2
      = (True, ss1, res2')
  | wildCardAllPNs p1 == wildCardAllPNs p2 && predExp && pred3
      = (True, res3', ss3) -}
 -- | pred2 = (True, HsGenerator loc0 p1' e1' res1', res2')
 -- | pred3 = (True, res3', HsGenerator loc0 p2' e2' res4')
  | wildCardAllPNs p1 == wildCardAllPNs p2 && predExp && predStmt
       = (True, (HsGenerator s p1' e1' res1), (HsGenerator s p2' e2' res2))
  | wildCardAllPNs p1 == wildCardAllPNs p2 && predExp && (not predStmt)
       = (True, (HsGenerator s p1' e1' (HsLast defaultExp)),
                (HsGenerator s p2' e2' (HsLast defaultExp)))
  -- | pred2 = (True, ss1, (HsGenerator s p2' e2' res2'))

  | otherwise = foldStmt (pats++[p1]) (pats2++[p2]) (stmts1, stmts1') (stmts2, stmts2')
           where
             predExp = foldExp (pats++[p1]) (pats2++[p2]) e1 e2
             (pred2, res1', res2') = foldStmt (pats++[p1]) (pats2++[p2]) (ss1, ss2) (stmts2, stmts2')
             (pred3, res3', res4') = foldStmt (pats++[p1]) (pats2++[p2]) (stmts1, stmts1') (ss3, ss4)
             (predStmt, res1, res2) = foldStmt (pats++[p1]) (pats2++[p2]) (stmts1, stmts1') (stmts2, stmts2')
foldStmt pats pats2 (HsQualifier e1 stmts1, HsQualifier e1' stmts1')
                    (HsQualifier e2 stmts2, HsQualifier e2' stmts2')
 | foldExp pats pats2 e1 e2 = (True, HsQualifier e1' res1, HsQualifier e2' res2)
                     where
                       (_, res1, res2) = foldStmt (pats) pats2 (stmts1, stmts1') (stmts2, stmts2')
foldStmt pats pats2 (HsQualifier e1 stmts1, HsQualifier e1' stmts1')
              (HsLast e2, HsLast e2')
 | foldExp pats pats2 e1 e2 = (True, HsLast e1', HsLast e2')
foldStmt pats pats2 (HsLast e1, HsLast e1')
              (HsQualifier e2 stmts2, HsQualifier e2' stmts2')
 | foldExp pats pats2 e1 e2 = (True, HsLast e1', HsLast e2')
foldStmt pats pats2 (HsLast e1, HsLast e1')
              ((HsLast e2),(HsLast e2'))
 | foldExp pats pats2 e1 e2 = (True, HsLast e1', HsLast e2')
foldStmt a b c d = (False, HsLast defaultExp, HsLast defaultExp)

-- ===========================================================

foldDoNormal :: [HsPatP] -> [HsPatP] -> HsExpP -> HsExpP -> Bool
foldDoNormal pats pats2 (Exp (HsDo stmts1)) (Exp (HsDo stmts2))
 | pred = True
           where
             pred= foldStmtNormal pats pats2 stmts1 stmts2
foldDoNormal _ _ _ _ = False

foldStmtNormal :: [HsPatP] -> [HsPatP] -> HsStmtP -> HsStmtP -> Bool
foldStmtNormal pats pats2 ss@(HsGenerator s p1 e1 stmts1) ss2@(HsGenerator _ p2 e2 stmts2)
  -- | pred2 = True
  -- | pred3 = True
  | wildCardAllPNs p1 == wildCardAllPNs p2 && predExp && predStmt
       = True
  | otherwise = foldStmtNormal (pats++[p1]) (pats2++[p2]) stmts1 stmts2
           where
             pred2 = foldStmtNormal (pats++[p1]) (pats2++[p2]) ss stmts2
             pred3 = foldStmtNormal (pats++[p1]) (pats2++[p2]) stmts1 ss2
             predExp = foldExp (pats++[p1]) (pats2++[p2]) e1 e2
             predStmt = foldStmtNormal (pats++[p1]) (pats2++[p2]) stmts1 stmts2
foldStmtNormal pats pats2 (HsQualifier e1 stmts1) (HsQualifier e2 stmts2)
 = foldExp pats pats2 e1 e2 && predStmt
     where
       predStmt = foldStmtNormal pats pats2 stmts1 stmts2
foldStmtNormal pats pats2 (HsLast e1) (HsLast e2)
 | e1 == defaultExp && e2 == defaultExp = True
 | otherwise  = foldExp pats pats2 e1 e2
foldStmtNormal _ _ _ _ = False



-- renames all bound variables to "$" so we can
-- compare too expressions via alpha renaming...
-- renameExp :: HsExpP -> HsDeclP -> m HsExpP
renameExp exp = applyTP (full_buTP (idTP `adhocTP` renameVar)) exp
  where
    renameVar e@(p::PName)
      | isTopLevelPN p = return p
     -- | (pNTtoPN p) `elem` free = return p
     -- | not (defines (pNTtoPN x) fun) = return e
      | otherwise = do s <- renameStringPN p
                       return e
                       --   (nameToPN "$")
    -- renameVar e = return e
    renameStringPN p = applyTP (full_buTP (idTP `adhocTP` inS)) p
    inS (p::String) = return "$"


-- =====================================================================================
-- Pretty Printing
-- We pretty print our matches to a file. Displaying the expression, together with
-- its position and the number of occurrences.
--
--

prettyPrint :: [ [(HsExpP, HsExpP, String)] ] -> [ ([PosToken], String) ] ->  String
prettyPrint [] [] = []
prettyPrint [] _ = []
prettyPrint _ [] = []
prettyPrint (dups:xs) toks
  = prettyPrint' dups toks ++ prettyPrint xs toks

     where
       prettyPrint' :: [(HsExpP, HsExpP,String)] -> [ ([PosToken], String) ] -> String
       prettyPrint' [] _ = ""
       prettyPrint' dups toks
         | length dups == 1 = ""
         | otherwise =
          ( (concatMap renderIt dups)
               ++ "\n" ++ (show (length dups)) ++ " occurrences.\n\n" )

       renderIt :: (HsExpP, HsExpP, String) -> String
       renderIt (_, e, m)
         = "\n\t\t" ++ m ++ "  " ++ (pos e (toks' m)) ++ ": >" ++
                       (stringise e (toks' m)) ++ "<"

       toks' :: String -> [PosToken]
       toks' m = findTokens toks m

       findTokens :: [ ([PosToken], String) ] -> String -> [PosToken]
       findTokens ((x,m):xs) name
         | m == name = x
         | otherwise = findTokens xs name

       pos :: HsExpP -> [PosToken] -> String
       pos e@(Exp (HsDo stmts)) toks
        = show pos'
           where pos'
                  = let       s=getStmtList stmts
                              locs = map (startEndLoc toks) (removeDefault s)
                              (startLocs, endLocs) =(sort (map fst locs), sort (map snd locs))
                          in {- extendForwards toks (ghead "StartEndLoc::HsStmtP" startLocs) (glast "StartEndLoc::HsStmtP" endLocs) isLet -} ((ghead "StartEndLoc::HsStmtP" startLocs), (glast "StartEndLoc::HsStmtP" endLocs))

       pos e toks
        | e /= defaultExp
           = let (start, end) = getStartEndLoc toks e
                in ((show (start, end)))
        | otherwise = ""

       stringise :: HsExpP -> [ PosToken ] -> String
       stringise e@(Exp (HsDo stmts)) toks
        = stringIt (getToks pos' toks)
           where pos'
                  = let       s=getStmtList stmts
                              locs = map (startEndLoc toks) (removeDefault s)
                              (startLocs, endLocs) =(sort (map fst locs), sort (map snd locs))
                          in {- extendForwards toks (ghead "StartEndLoc::HsStmtP" startLocs) (glast "StartEndLoc::HsStmtP" endLocs) isLet -} ((ghead "StartEndLoc::HsStmtP" startLocs), (glast "StartEndLoc::HsStmtP" endLocs))

       stringise e toks
        | e /= defaultExp
           = let (start,end) = getStartEndLoc toks e
              in stringIt (getToks (start,end) toks)
        | otherwise = ""

removeDefault [] = []
removeDefault (s@ (HsLastAtom e):es)
  | e == defaultExp = removeDefault es
  | otherwise = s : removeDefault es
removeDefault (s:ss)
  = s : removeDefault ss
prettyPrint2 :: [ [(HsExpP, HsExpP, String)] ] -> [ ([PosToken], String) ] ->  [ [(HsExpP, String, String)] ]
prettyPrint2 [] [] = []
prettyPrint2 [] _ = []
prettyPrint2 _ [] = []
prettyPrint2 (dups:xs) toks
  = prettyPrint' dups toks : prettyPrint2 xs toks

     where
       prettyPrint' :: [(HsExpP,HsExpP,String)] -> [ ([PosToken], String) ] -> [(HsExpP, String, String)]
       prettyPrint' [] _ = []
       prettyPrint' ((_,e,m):ms) toks
         = (e,m,( (renderIt (e,m)) ++ "\n" )) : prettyPrint' ms toks

       renderIt :: (HsExpP, String) -> String
       renderIt (e, m)
         = "\n\t\t" ++ m ++ "  " ++ (pos e (toks' m)) ++ ": >" ++
                       (stringise e (toks' m)) ++ "<"

       toks' :: String -> [PosToken]
       toks' m = findTokens toks m

       findTokens :: [ ([PosToken], String) ] -> String -> [PosToken]
       findTokens ((x,m):xs) name
         | m == name = x
         | otherwise = findTokens xs name

       pos :: HsExpP -> [PosToken] -> String
       pos e@(Exp (HsDo stmts)) toks
        = show pos'
           where pos'
                  = let       s=getStmtList stmts
                              locs = map (startEndLoc toks) (removeDefault s)
                              (startLocs, endLocs) =(sort (map fst locs), sort (map snd locs))
                          in ((ghead "StartEndLoc::HsStmtP" startLocs), (glast "StartEndLoc::HsStmtP" endLocs))

       pos e toks
        = let (start, end) = getStartEndLoc toks e
             in ((show (start, end)))

       stringise :: HsExpP -> [ PosToken ] -> String
       stringise e@(Exp (HsDo stmts)) toks
        = stringIt (getToks pos' toks)
           where pos'
                  = let       s=getStmtList stmts
                              locs = map (startEndLoc toks) (removeDefault s)
                              (startLocs, endLocs) =(sort (map fst locs), sort (map snd locs))
                          in  ((ghead "StartEndLoc::HsStmtP" startLocs), (glast "StartEndLoc::HsStmtP" endLocs))

       stringise e toks
        | e /= defaultExp
            = let (start,end) = getStartEndLoc toks e
                in stringIt (getToks (start,end) toks)
        | otherwise = ""

stringIt :: [PosToken] -> String
stringIt [] = ""
stringIt (r@(x,(y, s) ):xs) = s ++ (stringIt xs)
