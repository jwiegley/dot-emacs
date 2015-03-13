{-# LANGUAGE DeriveDataTypeable #-}

module Expr where

-- container
import Data.Tree (Tree(Node,rootLabel))

-- syb
import Data.Generics (Data)

import Language.Astview.DataTree (data2tree)

-- local imports
import Language.Astview.Language

-- Parsec (CSV Parser)
import Text.ParserCombinators.Parsec as Parsec
 
import Data.Generics hiding (Infix)
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language (javaStyle)
import Text.ParserCombinators.Parsec.Expr

expr = 
  Language 
    "Expr" 
    [] 
    [".expr"] 
    parseExpr
    (data2tree::Expr -> Tree String)
    Nothing
    Nothing

parseExpr :: String -> Either Error Expr
parseExpr s = case Parsec.parse lexedExpr "unknown" s of
   Right p -> Right p
   _       -> Left Err



-- ------------ a parsec parser ----------------------

-- a very tiny expr language deriving data
data Expr = Add Expr Expr 
          | Sub Expr Expr 
          | I Integer deriving (Show,Data,Typeable)

runLex :: Show a => Parsec.Parser a -> String -> IO ()
runLex p input
        = parseTest (do{ whiteSpace
                 ; x <- p
                 ; eof
                 ; return x
                 }) input

lexedExpr = do { whiteSpace
               ; x <- expr'
               ; eof
               ; return x
               }

expr' :: Parsec.Parser Expr
expr' = buildExpressionParser table subexpr <?> "expression"

subexpr =     parens expr'
          <|> myint 
          <?> "subexpr"

myint = do {n <- natural; return (I n) }

table = [[op "+" Add AssocLeft, op "-" Sub AssocLeft]]
      where
        op s f assoc
           = Infix (do{ reservedOp s; return f}) assoc


lexer :: P.TokenParser ()
lexer = P.makeTokenParser
          (javaStyle { P.reservedOpNames = ["+","-"]  })

whiteSpace =  P.whiteSpace lexer
lexeme     =  P.lexeme lexer
symbol     =  P.symbol lexer
natural    =  P.natural lexer
parens     =  P.parens lexer
semi       =  P.semi lexer
identifier= P.identifier lexer
reserved = P.reserved lexer
reservedOp= P.reservedOp lexer

