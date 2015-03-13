-- Dummy Parsec module
module Parsec where

import Monad

type Parser a           = GenParser Char () a
newtype GenParser tok st a = Parser (State tok st -> Consumed (Reply tok st a))
data Consumed a         = Consumed a                --input is consumed
                        | Empty !a                  --no input is consumed
                    
data Reply tok st a     = Ok a (State tok st) ParseError      --parsing succeeded with "a"
                        | Error ParseError                    --parsing failed

data State tok st       = State { stateInput :: [tok]
                                , statePos   :: SourcePos
                                , stateUser  :: !st
                                }
data ParseError     = ParseError !SourcePos [Message]
instance Show ParseError where
    show _ = "*"

type SourceName     = String
type Line           = Int
type Column         = Int

data SourcePos      = SourcePos SourceName !Line !Column
		     deriving (Eq,Ord)
data Message        = SysUnExpect !String   --library generated unexpect            
                    | UnExpect    !String   --unexpected something     
                    | Expect      !String   --expecting something
                    | Message     !String   --raw message

instance Monad (GenParser tok st) where
    return = undefined
    a >>= b = undefined

instance MonadPlus (GenParser tok st) where
    mzero = undefined

(<|>) :: GenParser tok st a -> GenParser tok st a -> GenParser tok st a
p1 <|> p2           = undefined

parseFromFile :: Parser a -> SourceName -> IO (Either ParseError a)
parseFromFile = undefined

many :: GenParser tok st a -> GenParser tok st [a]
many = undefined

try :: GenParser tok st a -> GenParser tok st a
try = undefined

runParser :: GenParser tok st a -> st -> SourceName -> [tok] -> Either ParseError a
runParser = undefined

option :: a -> GenParser tok st a -> GenParser tok st a
option = undefined
