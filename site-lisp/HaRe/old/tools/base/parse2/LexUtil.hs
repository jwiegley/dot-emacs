-- $Id: LexUtil.hs,v 1.1 2001/11/16 22:35:52 hallgren Exp $

module LexUtil (isIdent,isLower_,  -- Char -> Bool
		isSymbol,      -- Char -> Bool
		readInteger,   -- String -> Integer
		readNumber,    -- Integer -> String -> Integer
		readRational)  -- String -> Rational

where

import HsName(isSymbol)
import Data.Char(isDigit, isOctDigit, isHexDigit, digitToInt, isAlpha, isLower)
import Data.Ratio

isIdent  c = isAlpha c || isDigit c || c == '\'' || c == '_'
isLower_ c = isLower c || c == '_'

readInteger :: String -> Integer
readInteger ('0':'o':ds) = readInteger2  8 isOctDigit ds
readInteger ('0':'O':ds) = readInteger2  8 isOctDigit ds
readInteger ('0':'x':ds) = readInteger2 16 isHexDigit ds
readInteger ('0':'X':ds) = readInteger2 16 isHexDigit ds
readInteger          ds  = readInteger2 10 isDigit    ds

readNumber :: Integer -> String -> Integer
readNumber radix ds = readInteger2 radix (const True) ds

readInteger2 :: Integer -> (Char -> Bool) -> String -> Integer
readInteger2 radix isDig ds
  = foldl1 (\n d -> n * radix + d) (map (fromIntegral . digitToInt)
				    (takeWhile isDig ds))

readRational :: String -> Rational
readRational xs
    = (readInteger (i ++ m))%1 * 10^^((case e of
				       ""       -> 0
				       ('+':e2) -> read e2
				       _        -> read e) - length m)
      where (i, r1) = span isDigit xs
	    (m, r2) = span isDigit (dropWhile (== '.') r1)
	    e       = dropWhile (== 'e') r2

