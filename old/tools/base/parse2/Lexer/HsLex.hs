
-- Automatically generated code for a DFA follows:
--Equal states: [[[2,3],[8,9],[5,31],[10,11],[36,37],[39,40]]]
module HsLex (haskellLex) where
import Data.Char hiding (isSymbol) -- NOTE: AZ++may apply to HsLexUtils below instead...
import HsLexUtils

type Output = [(Token,String)]
type Input = String
type Acc = Input -- reversed
type Lexer = Input -> Output
type LexerState = (Acc->Lexer) -> Acc -> Lexer

haskellLex :: Lexer
haskellLex is = start1 is

cclass :: Char -> Int
cclass c =
  case c of
    '\t' -> 1
    '\n' -> 2
    '\v' -> 3
    '\f' -> 4
    '\r' -> 5
    ' ' -> 6
    '\160' -> 6
    '!' -> 7
    '#' -> 7
    '$' -> 7
    '%' -> 7
    '*' -> 7
    '/' -> 7
    '?' -> 7
    '\161' -> 7
    '\162' -> 7
    '\163' -> 7
    '\164' -> 7
    '\165' -> 7
    '\166' -> 7
    '\167' -> 7
    '\168' -> 7
    '\169' -> 7
    '\172' -> 7
    '\173' -> 7
    '\174' -> 7
    '\175' -> 7
    '\176' -> 7
    '\177' -> 7
    '\180' -> 7
    '\182' -> 7
    '\183' -> 7
    '\184' -> 7
    '\191' -> 7
    '\215' -> 7
    '\247' -> 7
    '"' -> 8
    '&' -> 9
    '\'' -> 10
    '(' -> 11
    ')' -> 11
    ',' -> 11
    ';' -> 11
    '`' -> 11
    '}' -> 11
    '+' -> 12
    '-' -> 13
    '.' -> 14
    '0' -> 15
    '1' -> 16
    '2' -> 16
    '3' -> 16
    '4' -> 16
    '5' -> 17
    '6' -> 17
    '7' -> 17
    '8' -> 18
    '9' -> 18
    ':' -> 19
    '<' -> 20
    '=' -> 21
    '>' -> 22
    '@' -> 23
    'A' -> 24
    'B' -> 25
    'C' -> 26
    'D' -> 27
    'E' -> 28
    'F' -> 29
    'G' -> 30
    'H' -> 31
    'I' -> 32
    'P' -> 32
    'J' -> 33
    'W' -> 33
    'Z' -> 33
    'K' -> 34
    'L' -> 35
    'M' -> 36
    'N' -> 37
    'O' -> 38
    'Q' -> 39
    'R' -> 40
    'S' -> 41
    'T' -> 42
    'U' -> 43
    'V' -> 44
    'X' -> 45
    'Y' -> 46
    '[' -> 47
    ']' -> 47
    '\\' -> 48
    '^' -> 49
    '_' -> 50
    'a' -> 51
    'b' -> 52
    'c' -> 53
    'd' -> 54
    'e' -> 55
    'f' -> 56
    'g' -> 57
    'h' -> 58
    'i' -> 59
    'j' -> 60
    'k' -> 60
    'q' -> 60
    'z' -> 60
    '\223' -> 60
    '\224' -> 60
    '\225' -> 60
    '\226' -> 60
    '\227' -> 60
    '\228' -> 60
    '\229' -> 60
    '\230' -> 60
    '\231' -> 60
    '\232' -> 60
    '\233' -> 60
    '\234' -> 60
    '\235' -> 60
    '\236' -> 60
    '\237' -> 60
    '\238' -> 60
    '\239' -> 60
    '\240' -> 60
    '\241' -> 60
    '\242' -> 60
    '\243' -> 60
    '\244' -> 60
    '\245' -> 60
    '\246' -> 60
    '\248' -> 60
    '\249' -> 60
    '\250' -> 60
    '\251' -> 60
    '\252' -> 60
    '\253' -> 60
    '\254' -> 60
    '\255' -> 60
    'l' -> 61
    'm' -> 62
    'n' -> 63
    'o' -> 64
    'p' -> 65
    'r' -> 66
    's' -> 67
    't' -> 68
    'u' -> 69
    'v' -> 70
    'w' -> 71
    'x' -> 72
    'y' -> 73
    '{' -> 74
    '|' -> 75
    '~' -> 75
    '\170' -> 76
    '\171' -> 76
    '\178' -> 76
    '\179' -> 76
    '\181' -> 76
    '\185' -> 76
    '\186' -> 76
    '\187' -> 76
    '\188' -> 76
    '\189' -> 76
    '\190' -> 76
    '\192' -> 77
    '\193' -> 77
    '\194' -> 77
    '\195' -> 77
    '\196' -> 77
    '\197' -> 77
    '\198' -> 77
    '\199' -> 77
    '\200' -> 77
    '\201' -> 77
    '\202' -> 77
    '\203' -> 77
    '\204' -> 77
    '\205' -> 77
    '\206' -> 77
    '\207' -> 77
    '\208' -> 77
    '\209' -> 77
    '\210' -> 77
    '\211' -> 77
    '\212' -> 77
    '\213' -> 77
    '\214' -> 77
    '\216' -> 77
    '\217' -> 77
    '\218' -> 77
    '\219' -> 77
    '\220' -> 77
    '\221' -> 77
    '\222' -> 77
    c | isAscii c -> 0
      | isSpace c -> 3
      | isSymbol c -> 7
      | isDigit c -> 18
      | isLower c -> 60
      | isUpper c -> 77
      | otherwise -> 0

start1 :: Lexer
start1 is = state1 (\ as is -> gotError as is) "" is
state1 :: LexerState
state1 err as [] = gotEOF as
state1 err as iis@(i:is) =
  case cclass i of
    51 -> state162 err (i:as) is
    52 -> state162 err (i:as) is
    56 -> state162 err (i:as) is
    57 -> state162 err (i:as) is
    58 -> state162 err (i:as) is
    60 -> state162 err (i:as) is
    65 -> state162 err (i:as) is
    66 -> state162 err (i:as) is
    67 -> state162 err (i:as) is
    69 -> state162 err (i:as) is
    70 -> state162 err (i:as) is
    72 -> state162 err (i:as) is
    73 -> state162 err (i:as) is
    1 -> state2 err (i:as) is
    2 -> state2 err (i:as) is
    3 -> state2 err (i:as) is
    4 -> state2 err (i:as) is
    5 -> state2 err (i:as) is
    6 -> state2 err (i:as) is
    7 -> state4 err (i:as) is
    9 -> state4 err (i:as) is
    12 -> state4 err (i:as) is
    22 -> state4 err (i:as) is
    49 -> state4 err (i:as) is
    23 -> state79 err (i:as) is
    48 -> state79 err (i:as) is
    75 -> state79 err (i:as) is
    16 -> state87 err (i:as) is
    17 -> state87 err (i:as) is
    18 -> state87 err (i:as) is
    0 -> err as iis
    76 -> err as iis
    11 -> state73 err (i:as) is
    47 -> state73 err (i:as) is
    8 -> state5 err (i:as) is
    10 -> state41 err (i:as) is
    13 -> state74 err (i:as) is
    14 -> state80 err (i:as) is
    15 -> state81 err (i:as) is
    19 -> state92 err (i:as) is
    20 -> state95 err (i:as) is
    21 -> state96 err (i:as) is
    50 -> state161 err (i:as) is
    53 -> state163 err (i:as) is
    54 -> state169 err (i:as) is
    55 -> state182 err (i:as) is
    59 -> state183 err (i:as) is
    61 -> state195 err (i:as) is
    62 -> state196 err (i:as) is
    63 -> state200 err (i:as) is
    64 -> state205 err (i:as) is
    68 -> state206 err (i:as) is
    71 -> state209 err (i:as) is
    74 -> state212 err (i:as) is
    _ -> state97 err (i:as) is

state2 :: LexerState
state2 err as [] = err as []
  where err _ _ = output Whitespace as (start1 [])
state2 err as iis@(i:is) =
  case cclass i of
    1 -> state2 err (i:as) is
    2 -> state2 err (i:as) is
    3 -> state2 err (i:as) is
    4 -> state2 err (i:as) is
    5 -> state2 err (i:as) is
    6 -> state2 err (i:as) is
    _ -> err as iis
  where err _ _ = output Whitespace as (start1 iis)

state4 :: LexerState
state4 err as [] = err as []
  where err _ _ = output Varsym as (start1 [])
state4 err as iis@(i:is) =
  case cclass i of
    7 -> state4 err (i:as) is
    9 -> state4 err (i:as) is
    12 -> state4 err (i:as) is
    13 -> state4 err (i:as) is
    14 -> state4 err (i:as) is
    19 -> state4 err (i:as) is
    20 -> state4 err (i:as) is
    21 -> state4 err (i:as) is
    22 -> state4 err (i:as) is
    23 -> state4 err (i:as) is
    48 -> state4 err (i:as) is
    49 -> state4 err (i:as) is
    75 -> state4 err (i:as) is
    _ -> err as iis
  where err _ _ = output Varsym as (start1 iis)

start5 :: Lexer
start5 is = state5 (\ as is -> gotError as is) "" is
state5 :: LexerState
state5 err as [] = err as []
state5 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    8 -> state6 err (i:as) is
    48 -> state7 err (i:as) is
    _ -> state5 err (i:as) is

state6 :: LexerState
state6 err as is = output StringLit as (start1 is)

start7 :: Lexer
start7 is = state7 (\ as is -> gotError as is) "" is
state7 :: LexerState
state7 err as [] = err as []
state7 err as iis@(i:is) =
  case cclass i of
    8 -> state5 err (i:as) is
    9 -> state5 err (i:as) is
    10 -> state5 err (i:as) is
    48 -> state5 err (i:as) is
    51 -> state5 err (i:as) is
    52 -> state5 err (i:as) is
    56 -> state5 err (i:as) is
    63 -> state5 err (i:as) is
    66 -> state5 err (i:as) is
    68 -> state5 err (i:as) is
    70 -> state5 err (i:as) is
    1 -> state8 err (i:as) is
    2 -> state8 err (i:as) is
    3 -> state8 err (i:as) is
    4 -> state8 err (i:as) is
    5 -> state8 err (i:as) is
    6 -> state8 err (i:as) is
    15 -> state10 err (i:as) is
    16 -> state10 err (i:as) is
    17 -> state10 err (i:as) is
    18 -> state10 err (i:as) is
    30 -> state27 err (i:as) is
    40 -> state27 err (i:as) is
    43 -> state27 err (i:as) is
    31 -> state23 err (i:as) is
    44 -> state23 err (i:as) is
    24 -> state12 err (i:as) is
    25 -> state14 err (i:as) is
    26 -> state16 err (i:as) is
    27 -> state18 err (i:as) is
    28 -> state21 err (i:as) is
    29 -> state26 err (i:as) is
    35 -> state28 err (i:as) is
    37 -> state29 err (i:as) is
    41 -> state30 err (i:as) is
    49 -> state34 err (i:as) is
    64 -> state35 err (i:as) is
    72 -> state38 err (i:as) is
    _ -> err as iis

start8 :: Lexer
start8 is = state8 (\ as is -> gotError as is) "" is
state8 :: LexerState
state8 err as [] = err as []
state8 err as iis@(i:is) =
  case cclass i of
    1 -> state8 err (i:as) is
    2 -> state8 err (i:as) is
    3 -> state8 err (i:as) is
    4 -> state8 err (i:as) is
    5 -> state8 err (i:as) is
    6 -> state8 err (i:as) is
    48 -> state5 err (i:as) is
    _ -> err as iis

start10 :: Lexer
start10 is = state10 (\ as is -> gotError as is) "" is
state10 :: LexerState
state10 err as [] = err as []
state10 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    15 -> state10 err (i:as) is
    16 -> state10 err (i:as) is
    17 -> state10 err (i:as) is
    18 -> state10 err (i:as) is
    8 -> state6 err (i:as) is
    48 -> state7 err (i:as) is
    _ -> state5 err (i:as) is

start12 :: Lexer
start12 is = state12 (\ as is -> gotError as is) "" is
state12 :: LexerState
state12 err as [] = err as []
state12 err as iis@(i:is) =
  case cclass i of
    26 -> state13 err (i:as) is
    _ -> err as iis

start13 :: Lexer
start13 is = state13 (\ as is -> gotError as is) "" is
state13 :: LexerState
state13 err as [] = err as []
state13 err as iis@(i:is) =
  case cclass i of
    34 -> state5 err (i:as) is
    _ -> err as iis

start14 :: Lexer
start14 is = state14 (\ as is -> gotError as is) "" is
state14 :: LexerState
state14 err as [] = err as []
state14 err as iis@(i:is) =
  case cclass i of
    41 -> state5 err (i:as) is
    28 -> state15 err (i:as) is
    _ -> err as iis

start15 :: Lexer
start15 is = state15 (\ as is -> gotError as is) "" is
state15 :: LexerState
state15 err as [] = err as []
state15 err as iis@(i:is) =
  case cclass i of
    35 -> state5 err (i:as) is
    _ -> err as iis

start16 :: Lexer
start16 is = state16 (\ as is -> gotError as is) "" is
state16 :: LexerState
state16 err as [] = err as []
state16 err as iis@(i:is) =
  case cclass i of
    40 -> state5 err (i:as) is
    24 -> state17 err (i:as) is
    _ -> err as iis

start17 :: Lexer
start17 is = state17 (\ as is -> gotError as is) "" is
state17 :: LexerState
state17 err as [] = err as []
state17 err as iis@(i:is) =
  case cclass i of
    37 -> state5 err (i:as) is
    _ -> err as iis

start18 :: Lexer
start18 is = state18 (\ as is -> gotError as is) "" is
state18 :: LexerState
state18 err as [] = err as []
state18 err as iis@(i:is) =
  case cclass i of
    28 -> state15 err (i:as) is
    26 -> state19 err (i:as) is
    35 -> state20 err (i:as) is
    _ -> err as iis

start19 :: Lexer
start19 is = state19 (\ as is -> gotError as is) "" is
state19 :: LexerState
state19 err as [] = err as []
state19 err as iis@(i:is) =
  case cclass i of
    16 -> state5 err (i:as) is
    _ -> err as iis

start20 :: Lexer
start20 is = state20 (\ as is -> gotError as is) "" is
state20 :: LexerState
state20 err as [] = err as []
state20 err as iis@(i:is) =
  case cclass i of
    28 -> state5 err (i:as) is
    _ -> err as iis

start21 :: Lexer
start21 is = state21 (\ as is -> gotError as is) "" is
state21 :: LexerState
state21 err as [] = err as []
state21 err as iis@(i:is) =
  case cclass i of
    36 -> state5 err (i:as) is
    37 -> state22 err (i:as) is
    38 -> state23 err (i:as) is
    41 -> state24 err (i:as) is
    42 -> state25 err (i:as) is
    _ -> err as iis

start22 :: Lexer
start22 is = state22 (\ as is -> gotError as is) "" is
state22 :: LexerState
state22 err as [] = err as []
state22 err as iis@(i:is) =
  case cclass i of
    39 -> state5 err (i:as) is
    _ -> err as iis

start23 :: Lexer
start23 is = state23 (\ as is -> gotError as is) "" is
state23 :: LexerState
state23 err as [] = err as []
state23 err as iis@(i:is) =
  case cclass i of
    42 -> state5 err (i:as) is
    _ -> err as iis

start24 :: Lexer
start24 is = state24 (\ as is -> gotError as is) "" is
state24 :: LexerState
state24 err as [] = err as []
state24 err as iis@(i:is) =
  case cclass i of
    26 -> state5 err (i:as) is
    _ -> err as iis

start25 :: Lexer
start25 is = state25 (\ as is -> gotError as is) "" is
state25 :: LexerState
state25 err as [] = err as []
state25 err as iis@(i:is) =
  case cclass i of
    25 -> state5 err (i:as) is
    45 -> state5 err (i:as) is
    _ -> err as iis

start26 :: Lexer
start26 is = state26 (\ as is -> gotError as is) "" is
state26 :: LexerState
state26 err as [] = err as []
state26 err as iis@(i:is) =
  case cclass i of
    29 -> state5 err (i:as) is
    41 -> state5 err (i:as) is
    _ -> err as iis

start27 :: Lexer
start27 is = state27 (\ as is -> gotError as is) "" is
state27 :: LexerState
state27 err as [] = err as []
state27 err as iis@(i:is) =
  case cclass i of
    41 -> state5 err (i:as) is
    _ -> err as iis

start28 :: Lexer
start28 is = state28 (\ as is -> gotError as is) "" is
state28 :: LexerState
state28 err as [] = err as []
state28 err as iis@(i:is) =
  case cclass i of
    29 -> state5 err (i:as) is
    _ -> err as iis

start29 :: Lexer
start29 is = state29 (\ as is -> gotError as is) "" is
state29 :: LexerState
state29 err as [] = err as []
state29 err as iis@(i:is) =
  case cclass i of
    24 -> state13 err (i:as) is
    43 -> state15 err (i:as) is
    _ -> err as iis

start30 :: Lexer
start30 is = state30 (\ as is -> gotError as is) "" is
state30 :: LexerState
state30 err as [] = err as []
state30 err as iis@(i:is) =
  case cclass i of
    32 -> state5 err (i:as) is
    38 -> state5 err (i:as) is
    46 -> state17 err (i:as) is
    42 -> state32 err (i:as) is
    43 -> state33 err (i:as) is
    _ -> err as iis

start32 :: Lexer
start32 is = state32 (\ as is -> gotError as is) "" is
state32 :: LexerState
state32 err as [] = err as []
state32 err as iis@(i:is) =
  case cclass i of
    45 -> state5 err (i:as) is
    _ -> err as iis

start33 :: Lexer
start33 is = state33 (\ as is -> gotError as is) "" is
state33 :: LexerState
state33 err as [] = err as []
state33 err as iis@(i:is) =
  case cclass i of
    25 -> state5 err (i:as) is
    _ -> err as iis

start34 :: Lexer
start34 is = state34 (\ as is -> gotError as is) "" is
state34 :: LexerState
state34 err as [] = err as []
state34 err as iis@(i:is) =
  case cclass i of
    23 -> state5 err (i:as) is
    24 -> state5 err (i:as) is
    25 -> state5 err (i:as) is
    26 -> state5 err (i:as) is
    27 -> state5 err (i:as) is
    28 -> state5 err (i:as) is
    29 -> state5 err (i:as) is
    30 -> state5 err (i:as) is
    31 -> state5 err (i:as) is
    32 -> state5 err (i:as) is
    33 -> state5 err (i:as) is
    34 -> state5 err (i:as) is
    35 -> state5 err (i:as) is
    36 -> state5 err (i:as) is
    37 -> state5 err (i:as) is
    38 -> state5 err (i:as) is
    39 -> state5 err (i:as) is
    40 -> state5 err (i:as) is
    41 -> state5 err (i:as) is
    42 -> state5 err (i:as) is
    43 -> state5 err (i:as) is
    44 -> state5 err (i:as) is
    45 -> state5 err (i:as) is
    46 -> state5 err (i:as) is
    47 -> state5 err (i:as) is
    48 -> state5 err (i:as) is
    49 -> state5 err (i:as) is
    50 -> state5 err (i:as) is
    _ -> err as iis

start35 :: Lexer
start35 is = state35 (\ as is -> gotError as is) "" is
state35 :: LexerState
state35 err as [] = err as []
state35 err as iis@(i:is) =
  case cclass i of
    15 -> state36 err (i:as) is
    16 -> state36 err (i:as) is
    17 -> state36 err (i:as) is
    _ -> err as iis

start36 :: Lexer
start36 is = state36 (\ as is -> gotError as is) "" is
state36 :: LexerState
state36 err as [] = err as []
state36 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    15 -> state36 err (i:as) is
    16 -> state36 err (i:as) is
    17 -> state36 err (i:as) is
    8 -> state6 err (i:as) is
    48 -> state7 err (i:as) is
    _ -> state5 err (i:as) is

start38 :: Lexer
start38 is = state38 (\ as is -> gotError as is) "" is
state38 :: LexerState
state38 err as [] = err as []
state38 err as iis@(i:is) =
  case cclass i of
    15 -> state39 err (i:as) is
    16 -> state39 err (i:as) is
    17 -> state39 err (i:as) is
    18 -> state39 err (i:as) is
    24 -> state39 err (i:as) is
    25 -> state39 err (i:as) is
    26 -> state39 err (i:as) is
    27 -> state39 err (i:as) is
    28 -> state39 err (i:as) is
    29 -> state39 err (i:as) is
    51 -> state39 err (i:as) is
    52 -> state39 err (i:as) is
    53 -> state39 err (i:as) is
    54 -> state39 err (i:as) is
    55 -> state39 err (i:as) is
    56 -> state39 err (i:as) is
    _ -> err as iis

start39 :: Lexer
start39 is = state39 (\ as is -> gotError as is) "" is
state39 :: LexerState
state39 err as [] = err as []
state39 err as iis@(i:is) =
  case cclass i of
    15 -> state39 err (i:as) is
    16 -> state39 err (i:as) is
    17 -> state39 err (i:as) is
    18 -> state39 err (i:as) is
    24 -> state39 err (i:as) is
    25 -> state39 err (i:as) is
    26 -> state39 err (i:as) is
    27 -> state39 err (i:as) is
    28 -> state39 err (i:as) is
    29 -> state39 err (i:as) is
    51 -> state39 err (i:as) is
    52 -> state39 err (i:as) is
    53 -> state39 err (i:as) is
    54 -> state39 err (i:as) is
    55 -> state39 err (i:as) is
    56 -> state39 err (i:as) is
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    8 -> state6 err (i:as) is
    48 -> state7 err (i:as) is
    _ -> state5 err (i:as) is

start41 :: Lexer
start41 is = state41 (\ as is -> gotError as is) "" is
state41 :: LexerState
state41 err as [] = err as []
state41 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    10 -> err as iis
    48 -> state44 err (i:as) is
    _ -> state42 err (i:as) is

start42 :: Lexer
start42 is = state42 (\ as is -> gotError as is) "" is
state42 :: LexerState
state42 err as [] = err as []
state42 err as iis@(i:is) =
  case cclass i of
    10 -> state43 err (i:as) is
    _ -> err as iis

state43 :: LexerState
state43 err as is = output CharLit as (start1 is)

start44 :: Lexer
start44 is = state44 (\ as is -> gotError as is) "" is
state44 :: LexerState
state44 err as [] = err as []
state44 err as iis@(i:is) =
  case cclass i of
    8 -> state42 err (i:as) is
    9 -> state42 err (i:as) is
    10 -> state42 err (i:as) is
    48 -> state42 err (i:as) is
    51 -> state42 err (i:as) is
    52 -> state42 err (i:as) is
    56 -> state42 err (i:as) is
    63 -> state42 err (i:as) is
    66 -> state42 err (i:as) is
    68 -> state42 err (i:as) is
    70 -> state42 err (i:as) is
    15 -> state45 err (i:as) is
    16 -> state45 err (i:as) is
    17 -> state45 err (i:as) is
    18 -> state45 err (i:as) is
    30 -> state61 err (i:as) is
    40 -> state61 err (i:as) is
    43 -> state61 err (i:as) is
    31 -> state57 err (i:as) is
    44 -> state57 err (i:as) is
    24 -> state46 err (i:as) is
    25 -> state48 err (i:as) is
    26 -> state50 err (i:as) is
    27 -> state52 err (i:as) is
    28 -> state55 err (i:as) is
    29 -> state60 err (i:as) is
    35 -> state62 err (i:as) is
    37 -> state63 err (i:as) is
    41 -> state64 err (i:as) is
    49 -> state68 err (i:as) is
    64 -> state69 err (i:as) is
    72 -> state71 err (i:as) is
    _ -> err as iis

start45 :: Lexer
start45 is = state45 (\ as is -> gotError as is) "" is
state45 :: LexerState
state45 err as [] = err as []
state45 err as iis@(i:is) =
  case cclass i of
    15 -> state45 err (i:as) is
    16 -> state45 err (i:as) is
    17 -> state45 err (i:as) is
    18 -> state45 err (i:as) is
    10 -> state43 err (i:as) is
    _ -> err as iis

start46 :: Lexer
start46 is = state46 (\ as is -> gotError as is) "" is
state46 :: LexerState
state46 err as [] = err as []
state46 err as iis@(i:is) =
  case cclass i of
    26 -> state47 err (i:as) is
    _ -> err as iis

start47 :: Lexer
start47 is = state47 (\ as is -> gotError as is) "" is
state47 :: LexerState
state47 err as [] = err as []
state47 err as iis@(i:is) =
  case cclass i of
    34 -> state42 err (i:as) is
    _ -> err as iis

start48 :: Lexer
start48 is = state48 (\ as is -> gotError as is) "" is
state48 :: LexerState
state48 err as [] = err as []
state48 err as iis@(i:is) =
  case cclass i of
    41 -> state42 err (i:as) is
    28 -> state49 err (i:as) is
    _ -> err as iis

start49 :: Lexer
start49 is = state49 (\ as is -> gotError as is) "" is
state49 :: LexerState
state49 err as [] = err as []
state49 err as iis@(i:is) =
  case cclass i of
    35 -> state42 err (i:as) is
    _ -> err as iis

start50 :: Lexer
start50 is = state50 (\ as is -> gotError as is) "" is
state50 :: LexerState
state50 err as [] = err as []
state50 err as iis@(i:is) =
  case cclass i of
    40 -> state42 err (i:as) is
    24 -> state51 err (i:as) is
    _ -> err as iis

start51 :: Lexer
start51 is = state51 (\ as is -> gotError as is) "" is
state51 :: LexerState
state51 err as [] = err as []
state51 err as iis@(i:is) =
  case cclass i of
    37 -> state42 err (i:as) is
    _ -> err as iis

start52 :: Lexer
start52 is = state52 (\ as is -> gotError as is) "" is
state52 :: LexerState
state52 err as [] = err as []
state52 err as iis@(i:is) =
  case cclass i of
    28 -> state49 err (i:as) is
    26 -> state53 err (i:as) is
    35 -> state54 err (i:as) is
    _ -> err as iis

start53 :: Lexer
start53 is = state53 (\ as is -> gotError as is) "" is
state53 :: LexerState
state53 err as [] = err as []
state53 err as iis@(i:is) =
  case cclass i of
    16 -> state42 err (i:as) is
    _ -> err as iis

start54 :: Lexer
start54 is = state54 (\ as is -> gotError as is) "" is
state54 :: LexerState
state54 err as [] = err as []
state54 err as iis@(i:is) =
  case cclass i of
    28 -> state42 err (i:as) is
    _ -> err as iis

start55 :: Lexer
start55 is = state55 (\ as is -> gotError as is) "" is
state55 :: LexerState
state55 err as [] = err as []
state55 err as iis@(i:is) =
  case cclass i of
    36 -> state42 err (i:as) is
    37 -> state56 err (i:as) is
    38 -> state57 err (i:as) is
    41 -> state58 err (i:as) is
    42 -> state59 err (i:as) is
    _ -> err as iis

start56 :: Lexer
start56 is = state56 (\ as is -> gotError as is) "" is
state56 :: LexerState
state56 err as [] = err as []
state56 err as iis@(i:is) =
  case cclass i of
    39 -> state42 err (i:as) is
    _ -> err as iis

start57 :: Lexer
start57 is = state57 (\ as is -> gotError as is) "" is
state57 :: LexerState
state57 err as [] = err as []
state57 err as iis@(i:is) =
  case cclass i of
    42 -> state42 err (i:as) is
    _ -> err as iis

start58 :: Lexer
start58 is = state58 (\ as is -> gotError as is) "" is
state58 :: LexerState
state58 err as [] = err as []
state58 err as iis@(i:is) =
  case cclass i of
    26 -> state42 err (i:as) is
    _ -> err as iis

start59 :: Lexer
start59 is = state59 (\ as is -> gotError as is) "" is
state59 :: LexerState
state59 err as [] = err as []
state59 err as iis@(i:is) =
  case cclass i of
    25 -> state42 err (i:as) is
    45 -> state42 err (i:as) is
    _ -> err as iis

start60 :: Lexer
start60 is = state60 (\ as is -> gotError as is) "" is
state60 :: LexerState
state60 err as [] = err as []
state60 err as iis@(i:is) =
  case cclass i of
    29 -> state42 err (i:as) is
    41 -> state42 err (i:as) is
    _ -> err as iis

start61 :: Lexer
start61 is = state61 (\ as is -> gotError as is) "" is
state61 :: LexerState
state61 err as [] = err as []
state61 err as iis@(i:is) =
  case cclass i of
    41 -> state42 err (i:as) is
    _ -> err as iis

start62 :: Lexer
start62 is = state62 (\ as is -> gotError as is) "" is
state62 :: LexerState
state62 err as [] = err as []
state62 err as iis@(i:is) =
  case cclass i of
    29 -> state42 err (i:as) is
    _ -> err as iis

start63 :: Lexer
start63 is = state63 (\ as is -> gotError as is) "" is
state63 :: LexerState
state63 err as [] = err as []
state63 err as iis@(i:is) =
  case cclass i of
    24 -> state47 err (i:as) is
    43 -> state49 err (i:as) is
    _ -> err as iis

start64 :: Lexer
start64 is = state64 (\ as is -> gotError as is) "" is
state64 :: LexerState
state64 err as [] = err as []
state64 err as iis@(i:is) =
  case cclass i of
    32 -> state42 err (i:as) is
    46 -> state51 err (i:as) is
    38 -> state65 err (i:as) is
    42 -> state66 err (i:as) is
    43 -> state67 err (i:as) is
    _ -> err as iis

start65 :: Lexer
start65 is = state65 (\ as is -> gotError as is) "" is
state65 :: LexerState
state65 err as [] = err as []
state65 err as iis@(i:is) =
  case cclass i of
    31 -> state42 err (i:as) is
    10 -> state43 err (i:as) is
    _ -> err as iis

start66 :: Lexer
start66 is = state66 (\ as is -> gotError as is) "" is
state66 :: LexerState
state66 err as [] = err as []
state66 err as iis@(i:is) =
  case cclass i of
    45 -> state42 err (i:as) is
    _ -> err as iis

start67 :: Lexer
start67 is = state67 (\ as is -> gotError as is) "" is
state67 :: LexerState
state67 err as [] = err as []
state67 err as iis@(i:is) =
  case cclass i of
    25 -> state42 err (i:as) is
    _ -> err as iis

start68 :: Lexer
start68 is = state68 (\ as is -> gotError as is) "" is
state68 :: LexerState
state68 err as [] = err as []
state68 err as iis@(i:is) =
  case cclass i of
    23 -> state42 err (i:as) is
    24 -> state42 err (i:as) is
    25 -> state42 err (i:as) is
    26 -> state42 err (i:as) is
    27 -> state42 err (i:as) is
    28 -> state42 err (i:as) is
    29 -> state42 err (i:as) is
    30 -> state42 err (i:as) is
    31 -> state42 err (i:as) is
    32 -> state42 err (i:as) is
    33 -> state42 err (i:as) is
    34 -> state42 err (i:as) is
    35 -> state42 err (i:as) is
    36 -> state42 err (i:as) is
    37 -> state42 err (i:as) is
    38 -> state42 err (i:as) is
    39 -> state42 err (i:as) is
    40 -> state42 err (i:as) is
    41 -> state42 err (i:as) is
    42 -> state42 err (i:as) is
    43 -> state42 err (i:as) is
    44 -> state42 err (i:as) is
    45 -> state42 err (i:as) is
    46 -> state42 err (i:as) is
    47 -> state42 err (i:as) is
    48 -> state42 err (i:as) is
    49 -> state42 err (i:as) is
    50 -> state42 err (i:as) is
    _ -> err as iis

start69 :: Lexer
start69 is = state69 (\ as is -> gotError as is) "" is
state69 :: LexerState
state69 err as [] = err as []
state69 err as iis@(i:is) =
  case cclass i of
    15 -> state70 err (i:as) is
    16 -> state70 err (i:as) is
    17 -> state70 err (i:as) is
    _ -> err as iis

start70 :: Lexer
start70 is = state70 (\ as is -> gotError as is) "" is
state70 :: LexerState
state70 err as [] = err as []
state70 err as iis@(i:is) =
  case cclass i of
    15 -> state70 err (i:as) is
    16 -> state70 err (i:as) is
    17 -> state70 err (i:as) is
    10 -> state43 err (i:as) is
    _ -> err as iis

start71 :: Lexer
start71 is = state71 (\ as is -> gotError as is) "" is
state71 :: LexerState
state71 err as [] = err as []
state71 err as iis@(i:is) =
  case cclass i of
    15 -> state72 err (i:as) is
    16 -> state72 err (i:as) is
    17 -> state72 err (i:as) is
    18 -> state72 err (i:as) is
    24 -> state72 err (i:as) is
    25 -> state72 err (i:as) is
    26 -> state72 err (i:as) is
    27 -> state72 err (i:as) is
    28 -> state72 err (i:as) is
    29 -> state72 err (i:as) is
    51 -> state72 err (i:as) is
    52 -> state72 err (i:as) is
    53 -> state72 err (i:as) is
    54 -> state72 err (i:as) is
    55 -> state72 err (i:as) is
    56 -> state72 err (i:as) is
    _ -> err as iis

start72 :: Lexer
start72 is = state72 (\ as is -> gotError as is) "" is
state72 :: LexerState
state72 err as [] = err as []
state72 err as iis@(i:is) =
  case cclass i of
    15 -> state72 err (i:as) is
    16 -> state72 err (i:as) is
    17 -> state72 err (i:as) is
    18 -> state72 err (i:as) is
    24 -> state72 err (i:as) is
    25 -> state72 err (i:as) is
    26 -> state72 err (i:as) is
    27 -> state72 err (i:as) is
    28 -> state72 err (i:as) is
    29 -> state72 err (i:as) is
    51 -> state72 err (i:as) is
    52 -> state72 err (i:as) is
    53 -> state72 err (i:as) is
    54 -> state72 err (i:as) is
    55 -> state72 err (i:as) is
    56 -> state72 err (i:as) is
    10 -> state43 err (i:as) is
    _ -> err as iis

state73 :: LexerState
state73 err as is = output Special as (start1 is)

state74 :: LexerState
state74 err as [] = err as []
  where err _ _ = output Varsym as (start1 [])
state74 err as iis@(i:is) =
  case cclass i of
    7 -> state4 err (i:as) is
    9 -> state4 err (i:as) is
    12 -> state4 err (i:as) is
    14 -> state4 err (i:as) is
    19 -> state4 err (i:as) is
    20 -> state4 err (i:as) is
    21 -> state4 err (i:as) is
    23 -> state4 err (i:as) is
    48 -> state4 err (i:as) is
    49 -> state4 err (i:as) is
    75 -> state4 err (i:as) is
    13 -> state75 err (i:as) is
    22 -> state79 err (i:as) is
    _ -> err as iis
  where err _ _ = output Varsym as (start1 iis)

state75 :: LexerState
state75 err as [] = err as []
  where err _ _ = output Commentstart as (start76 [])
state75 err as iis@(i:is) =
  case cclass i of
    7 -> state4 err (i:as) is
    9 -> state4 err (i:as) is
    12 -> state4 err (i:as) is
    14 -> state4 err (i:as) is
    19 -> state4 err (i:as) is
    20 -> state4 err (i:as) is
    21 -> state4 err (i:as) is
    22 -> state4 err (i:as) is
    23 -> state4 err (i:as) is
    48 -> state4 err (i:as) is
    49 -> state4 err (i:as) is
    75 -> state4 err (i:as) is
    13 -> state75 err (i:as) is
    _ -> err as iis
  where err _ _ = output Commentstart as (start76 iis)

start76 :: Lexer
start76 is = state76 (\ as is -> gotError as is) "" is
state76 :: LexerState
state76 err as [] = err as []
state76 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    3 -> err as iis
    2 -> state77 err (i:as) is
    4 -> state77 err (i:as) is
    5 -> state78 err (i:as) is
    _ -> state76 err (i:as) is

state77 :: LexerState
state77 err as is = output Comment as (start1 is)

state78 :: LexerState
state78 err as [] = err as []
  where err _ _ = output Comment as (start1 [])
state78 err as iis@(i:is) =
  case cclass i of
    2 -> state77 err (i:as) is
    _ -> err as iis
  where err _ _ = output Comment as (start1 iis)

state79 :: LexerState
state79 err as [] = err as []
  where err _ _ = output Reservedop as (start1 [])
state79 err as iis@(i:is) =
  case cclass i of
    7 -> state4 err (i:as) is
    9 -> state4 err (i:as) is
    12 -> state4 err (i:as) is
    13 -> state4 err (i:as) is
    14 -> state4 err (i:as) is
    19 -> state4 err (i:as) is
    20 -> state4 err (i:as) is
    21 -> state4 err (i:as) is
    22 -> state4 err (i:as) is
    23 -> state4 err (i:as) is
    48 -> state4 err (i:as) is
    49 -> state4 err (i:as) is
    75 -> state4 err (i:as) is
    _ -> err as iis
  where err _ _ = output Reservedop as (start1 iis)

state80 :: LexerState
state80 err as [] = err as []
  where err _ _ = output Varsym as (start1 [])
state80 err as iis@(i:is) =
  case cclass i of
    7 -> state4 err (i:as) is
    9 -> state4 err (i:as) is
    12 -> state4 err (i:as) is
    13 -> state4 err (i:as) is
    19 -> state4 err (i:as) is
    20 -> state4 err (i:as) is
    21 -> state4 err (i:as) is
    22 -> state4 err (i:as) is
    23 -> state4 err (i:as) is
    48 -> state4 err (i:as) is
    49 -> state4 err (i:as) is
    75 -> state4 err (i:as) is
    14 -> state79 err (i:as) is
    _ -> err as iis
  where err _ _ = output Varsym as (start1 iis)

state81 :: LexerState
state81 err as [] = err as []
  where err _ _ = output IntLit as (start1 [])
state81 err as iis@(i:is) =
  case cclass i of
    15 -> state87 err (i:as) is
    16 -> state87 err (i:as) is
    17 -> state87 err (i:as) is
    18 -> state87 err (i:as) is
    38 -> state88 err (i:as) is
    64 -> state88 err (i:as) is
    45 -> state90 err (i:as) is
    72 -> state90 err (i:as) is
    14 -> state82 err (i:as) is
    _ -> err as iis
  where err _ _ = output IntLit as (start1 iis)

start82 :: Lexer
start82 is = state82 (\ as is -> gotError as is) "" is
state82 :: LexerState
state82 err as [] = err as []
state82 err as iis@(i:is) =
  case cclass i of
    15 -> state83 err (i:as) is
    16 -> state83 err (i:as) is
    17 -> state83 err (i:as) is
    18 -> state83 err (i:as) is
    _ -> err as iis

state83 :: LexerState
state83 err as [] = err as []
  where err _ _ = output FloatLit as (start1 [])
state83 err as iis@(i:is) =
  case cclass i of
    15 -> state83 err (i:as) is
    16 -> state83 err (i:as) is
    17 -> state83 err (i:as) is
    18 -> state83 err (i:as) is
    28 -> state84 err (i:as) is
    55 -> state84 err (i:as) is
    _ -> err as iis
  where err _ _ = output FloatLit as (start1 iis)

start84 :: Lexer
start84 is = state84 (\ as is -> gotError as is) "" is
state84 :: LexerState
state84 err as [] = err as []
state84 err as iis@(i:is) =
  case cclass i of
    15 -> state86 err (i:as) is
    16 -> state86 err (i:as) is
    17 -> state86 err (i:as) is
    18 -> state86 err (i:as) is
    12 -> state85 err (i:as) is
    13 -> state85 err (i:as) is
    _ -> err as iis

start85 :: Lexer
start85 is = state85 (\ as is -> gotError as is) "" is
state85 :: LexerState
state85 err as [] = err as []
state85 err as iis@(i:is) =
  case cclass i of
    15 -> state86 err (i:as) is
    16 -> state86 err (i:as) is
    17 -> state86 err (i:as) is
    18 -> state86 err (i:as) is
    _ -> err as iis

state86 :: LexerState
state86 err as [] = err as []
  where err _ _ = output FloatLit as (start1 [])
state86 err as iis@(i:is) =
  case cclass i of
    15 -> state86 err (i:as) is
    16 -> state86 err (i:as) is
    17 -> state86 err (i:as) is
    18 -> state86 err (i:as) is
    _ -> err as iis
  where err _ _ = output FloatLit as (start1 iis)

state87 :: LexerState
state87 err as [] = err as []
  where err _ _ = output IntLit as (start1 [])
state87 err as iis@(i:is) =
  case cclass i of
    15 -> state87 err (i:as) is
    16 -> state87 err (i:as) is
    17 -> state87 err (i:as) is
    18 -> state87 err (i:as) is
    14 -> state82 err (i:as) is
    _ -> err as iis
  where err _ _ = output IntLit as (start1 iis)

start88 :: Lexer
start88 is = state88 (\ as is -> gotError as is) "" is
state88 :: LexerState
state88 err as [] = err as []
state88 err as iis@(i:is) =
  case cclass i of
    15 -> state89 err (i:as) is
    16 -> state89 err (i:as) is
    17 -> state89 err (i:as) is
    _ -> err as iis

state89 :: LexerState
state89 err as [] = err as []
  where err _ _ = output IntLit as (start1 [])
state89 err as iis@(i:is) =
  case cclass i of
    15 -> state89 err (i:as) is
    16 -> state89 err (i:as) is
    17 -> state89 err (i:as) is
    _ -> err as iis
  where err _ _ = output IntLit as (start1 iis)

start90 :: Lexer
start90 is = state90 (\ as is -> gotError as is) "" is
state90 :: LexerState
state90 err as [] = err as []
state90 err as iis@(i:is) =
  case cclass i of
    15 -> state91 err (i:as) is
    16 -> state91 err (i:as) is
    17 -> state91 err (i:as) is
    18 -> state91 err (i:as) is
    24 -> state91 err (i:as) is
    25 -> state91 err (i:as) is
    26 -> state91 err (i:as) is
    27 -> state91 err (i:as) is
    28 -> state91 err (i:as) is
    29 -> state91 err (i:as) is
    51 -> state91 err (i:as) is
    52 -> state91 err (i:as) is
    53 -> state91 err (i:as) is
    54 -> state91 err (i:as) is
    55 -> state91 err (i:as) is
    56 -> state91 err (i:as) is
    _ -> err as iis

state91 :: LexerState
state91 err as [] = err as []
  where err _ _ = output IntLit as (start1 [])
state91 err as iis@(i:is) =
  case cclass i of
    15 -> state91 err (i:as) is
    16 -> state91 err (i:as) is
    17 -> state91 err (i:as) is
    18 -> state91 err (i:as) is
    24 -> state91 err (i:as) is
    25 -> state91 err (i:as) is
    26 -> state91 err (i:as) is
    27 -> state91 err (i:as) is
    28 -> state91 err (i:as) is
    29 -> state91 err (i:as) is
    51 -> state91 err (i:as) is
    52 -> state91 err (i:as) is
    53 -> state91 err (i:as) is
    54 -> state91 err (i:as) is
    55 -> state91 err (i:as) is
    56 -> state91 err (i:as) is
    _ -> err as iis
  where err _ _ = output IntLit as (start1 iis)

state92 :: LexerState
state92 err as [] = err as []
  where err _ _ = output Reservedop as (start1 [])
state92 err as iis@(i:is) =
  case cclass i of
    7 -> state93 err (i:as) is
    9 -> state93 err (i:as) is
    12 -> state93 err (i:as) is
    13 -> state93 err (i:as) is
    14 -> state93 err (i:as) is
    20 -> state93 err (i:as) is
    21 -> state93 err (i:as) is
    22 -> state93 err (i:as) is
    23 -> state93 err (i:as) is
    48 -> state93 err (i:as) is
    49 -> state93 err (i:as) is
    75 -> state93 err (i:as) is
    19 -> state94 err (i:as) is
    _ -> err as iis
  where err _ _ = output Reservedop as (start1 iis)

state93 :: LexerState
state93 err as [] = err as []
  where err _ _ = output Consym as (start1 [])
state93 err as iis@(i:is) =
  case cclass i of
    7 -> state93 err (i:as) is
    9 -> state93 err (i:as) is
    12 -> state93 err (i:as) is
    13 -> state93 err (i:as) is
    14 -> state93 err (i:as) is
    19 -> state93 err (i:as) is
    20 -> state93 err (i:as) is
    21 -> state93 err (i:as) is
    22 -> state93 err (i:as) is
    23 -> state93 err (i:as) is
    48 -> state93 err (i:as) is
    49 -> state93 err (i:as) is
    75 -> state93 err (i:as) is
    _ -> err as iis
  where err _ _ = output Consym as (start1 iis)

state94 :: LexerState
state94 err as [] = err as []
  where err _ _ = output Reservedop as (start1 [])
state94 err as iis@(i:is) =
  case cclass i of
    7 -> state93 err (i:as) is
    9 -> state93 err (i:as) is
    12 -> state93 err (i:as) is
    13 -> state93 err (i:as) is
    14 -> state93 err (i:as) is
    19 -> state93 err (i:as) is
    20 -> state93 err (i:as) is
    21 -> state93 err (i:as) is
    22 -> state93 err (i:as) is
    23 -> state93 err (i:as) is
    48 -> state93 err (i:as) is
    49 -> state93 err (i:as) is
    75 -> state93 err (i:as) is
    _ -> err as iis
  where err _ _ = output Reservedop as (start1 iis)

state95 :: LexerState
state95 err as [] = err as []
  where err _ _ = output Varsym as (start1 [])
state95 err as iis@(i:is) =
  case cclass i of
    7 -> state4 err (i:as) is
    9 -> state4 err (i:as) is
    12 -> state4 err (i:as) is
    14 -> state4 err (i:as) is
    19 -> state4 err (i:as) is
    20 -> state4 err (i:as) is
    21 -> state4 err (i:as) is
    22 -> state4 err (i:as) is
    23 -> state4 err (i:as) is
    48 -> state4 err (i:as) is
    49 -> state4 err (i:as) is
    75 -> state4 err (i:as) is
    13 -> state79 err (i:as) is
    _ -> err as iis
  where err _ _ = output Varsym as (start1 iis)

state96 :: LexerState
state96 err as [] = err as []
  where err _ _ = output Reservedop as (start1 [])
state96 err as iis@(i:is) =
  case cclass i of
    7 -> state4 err (i:as) is
    9 -> state4 err (i:as) is
    12 -> state4 err (i:as) is
    13 -> state4 err (i:as) is
    14 -> state4 err (i:as) is
    19 -> state4 err (i:as) is
    20 -> state4 err (i:as) is
    21 -> state4 err (i:as) is
    23 -> state4 err (i:as) is
    48 -> state4 err (i:as) is
    49 -> state4 err (i:as) is
    75 -> state4 err (i:as) is
    22 -> state79 err (i:as) is
    _ -> err as iis
  where err _ _ = output Reservedop as (start1 iis)

state97 :: LexerState
state97 err as [] = err as []
  where err _ _ = output Conid as (start1 [])
state97 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    14 -> state98 err (i:as) is
    _ -> state97 err (i:as) is
  where err _ _ = output Conid as (start1 iis)

start98 :: Lexer
start98 is = state98 (\ as is -> gotError as is) "" is
state98 :: LexerState
state98 err as [] = err as []
state98 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    8 -> err as iis
    10 -> err as iis
    11 -> err as iis
    15 -> err as iis
    16 -> err as iis
    17 -> err as iis
    18 -> err as iis
    47 -> err as iis
    74 -> err as iis
    76 -> err as iis
    51 -> state111 err (i:as) is
    52 -> state111 err (i:as) is
    56 -> state111 err (i:as) is
    57 -> state111 err (i:as) is
    58 -> state111 err (i:as) is
    60 -> state111 err (i:as) is
    65 -> state111 err (i:as) is
    66 -> state111 err (i:as) is
    67 -> state111 err (i:as) is
    69 -> state111 err (i:as) is
    70 -> state111 err (i:as) is
    72 -> state111 err (i:as) is
    73 -> state111 err (i:as) is
    7 -> state99 err (i:as) is
    9 -> state99 err (i:as) is
    12 -> state99 err (i:as) is
    22 -> state99 err (i:as) is
    49 -> state99 err (i:as) is
    23 -> state102 err (i:as) is
    48 -> state102 err (i:as) is
    75 -> state102 err (i:as) is
    13 -> state100 err (i:as) is
    14 -> state103 err (i:as) is
    19 -> state104 err (i:as) is
    20 -> state107 err (i:as) is
    21 -> state108 err (i:as) is
    50 -> state110 err (i:as) is
    53 -> state112 err (i:as) is
    54 -> state118 err (i:as) is
    55 -> state131 err (i:as) is
    59 -> state132 err (i:as) is
    61 -> state144 err (i:as) is
    62 -> state145 err (i:as) is
    63 -> state149 err (i:as) is
    64 -> state154 err (i:as) is
    68 -> state155 err (i:as) is
    71 -> state158 err (i:as) is
    _ -> state109 err (i:as) is

state99 :: LexerState
state99 err as [] = err as []
  where err _ _ = output Qvarsym as (start1 [])
state99 err as iis@(i:is) =
  case cclass i of
    7 -> state99 err (i:as) is
    9 -> state99 err (i:as) is
    12 -> state99 err (i:as) is
    13 -> state99 err (i:as) is
    14 -> state99 err (i:as) is
    19 -> state99 err (i:as) is
    20 -> state99 err (i:as) is
    21 -> state99 err (i:as) is
    22 -> state99 err (i:as) is
    23 -> state99 err (i:as) is
    48 -> state99 err (i:as) is
    49 -> state99 err (i:as) is
    75 -> state99 err (i:as) is
    _ -> err as iis
  where err _ _ = output Qvarsym as (start1 iis)

state100 :: LexerState
state100 err as [] = err as []
  where err _ _ = output Qvarsym as (start1 [])
state100 err as iis@(i:is) =
  case cclass i of
    7 -> state99 err (i:as) is
    9 -> state99 err (i:as) is
    12 -> state99 err (i:as) is
    14 -> state99 err (i:as) is
    19 -> state99 err (i:as) is
    20 -> state99 err (i:as) is
    21 -> state99 err (i:as) is
    23 -> state99 err (i:as) is
    48 -> state99 err (i:as) is
    49 -> state99 err (i:as) is
    75 -> state99 err (i:as) is
    13 -> state101 err (i:as) is
    22 -> state102 err (i:as) is
    _ -> err as iis
  where err _ _ = output Qvarsym as (start1 iis)

start101 :: Lexer
start101 is = state101 (\ as is -> gotError as is) "" is
state101 :: LexerState
state101 err as [] = err as []
state101 err as iis@(i:is) =
  case cclass i of
    7 -> state99 err (i:as) is
    9 -> state99 err (i:as) is
    12 -> state99 err (i:as) is
    14 -> state99 err (i:as) is
    19 -> state99 err (i:as) is
    20 -> state99 err (i:as) is
    21 -> state99 err (i:as) is
    22 -> state99 err (i:as) is
    23 -> state99 err (i:as) is
    48 -> state99 err (i:as) is
    49 -> state99 err (i:as) is
    75 -> state99 err (i:as) is
    13 -> state101 err (i:as) is
    _ -> err as iis

start102 :: Lexer
start102 is = state102 (\ as is -> gotError as is) "" is
state102 :: LexerState
state102 err as [] = err as []
state102 err as iis@(i:is) =
  case cclass i of
    7 -> state99 err (i:as) is
    9 -> state99 err (i:as) is
    12 -> state99 err (i:as) is
    13 -> state99 err (i:as) is
    14 -> state99 err (i:as) is
    19 -> state99 err (i:as) is
    20 -> state99 err (i:as) is
    21 -> state99 err (i:as) is
    22 -> state99 err (i:as) is
    23 -> state99 err (i:as) is
    48 -> state99 err (i:as) is
    49 -> state99 err (i:as) is
    75 -> state99 err (i:as) is
    _ -> err as iis

state103 :: LexerState
state103 err as [] = err as []
  where err _ _ = output Qvarsym as (start1 [])
state103 err as iis@(i:is) =
  case cclass i of
    7 -> state99 err (i:as) is
    9 -> state99 err (i:as) is
    12 -> state99 err (i:as) is
    13 -> state99 err (i:as) is
    19 -> state99 err (i:as) is
    20 -> state99 err (i:as) is
    21 -> state99 err (i:as) is
    22 -> state99 err (i:as) is
    23 -> state99 err (i:as) is
    48 -> state99 err (i:as) is
    49 -> state99 err (i:as) is
    75 -> state99 err (i:as) is
    14 -> state102 err (i:as) is
    _ -> err as iis
  where err _ _ = output Qvarsym as (start1 iis)

start104 :: Lexer
start104 is = state104 (\ as is -> gotError as is) "" is
state104 :: LexerState
state104 err as [] = err as []
state104 err as iis@(i:is) =
  case cclass i of
    7 -> state105 err (i:as) is
    9 -> state105 err (i:as) is
    12 -> state105 err (i:as) is
    13 -> state105 err (i:as) is
    14 -> state105 err (i:as) is
    20 -> state105 err (i:as) is
    21 -> state105 err (i:as) is
    22 -> state105 err (i:as) is
    23 -> state105 err (i:as) is
    48 -> state105 err (i:as) is
    49 -> state105 err (i:as) is
    75 -> state105 err (i:as) is
    19 -> state106 err (i:as) is
    _ -> err as iis

state105 :: LexerState
state105 err as [] = err as []
  where err _ _ = output Qconsym as (start1 [])
state105 err as iis@(i:is) =
  case cclass i of
    7 -> state105 err (i:as) is
    9 -> state105 err (i:as) is
    12 -> state105 err (i:as) is
    13 -> state105 err (i:as) is
    14 -> state105 err (i:as) is
    19 -> state105 err (i:as) is
    20 -> state105 err (i:as) is
    21 -> state105 err (i:as) is
    22 -> state105 err (i:as) is
    23 -> state105 err (i:as) is
    48 -> state105 err (i:as) is
    49 -> state105 err (i:as) is
    75 -> state105 err (i:as) is
    _ -> err as iis
  where err _ _ = output Qconsym as (start1 iis)

start106 :: Lexer
start106 is = state106 (\ as is -> gotError as is) "" is
state106 :: LexerState
state106 err as [] = err as []
state106 err as iis@(i:is) =
  case cclass i of
    7 -> state105 err (i:as) is
    9 -> state105 err (i:as) is
    12 -> state105 err (i:as) is
    13 -> state105 err (i:as) is
    14 -> state105 err (i:as) is
    19 -> state105 err (i:as) is
    20 -> state105 err (i:as) is
    21 -> state105 err (i:as) is
    22 -> state105 err (i:as) is
    23 -> state105 err (i:as) is
    48 -> state105 err (i:as) is
    49 -> state105 err (i:as) is
    75 -> state105 err (i:as) is
    _ -> err as iis

state107 :: LexerState
state107 err as [] = err as []
  where err _ _ = output Qvarsym as (start1 [])
state107 err as iis@(i:is) =
  case cclass i of
    7 -> state99 err (i:as) is
    9 -> state99 err (i:as) is
    12 -> state99 err (i:as) is
    14 -> state99 err (i:as) is
    19 -> state99 err (i:as) is
    20 -> state99 err (i:as) is
    21 -> state99 err (i:as) is
    22 -> state99 err (i:as) is
    23 -> state99 err (i:as) is
    48 -> state99 err (i:as) is
    49 -> state99 err (i:as) is
    75 -> state99 err (i:as) is
    13 -> state102 err (i:as) is
    _ -> err as iis
  where err _ _ = output Qvarsym as (start1 iis)

start108 :: Lexer
start108 is = state108 (\ as is -> gotError as is) "" is
state108 :: LexerState
state108 err as [] = err as []
state108 err as iis@(i:is) =
  case cclass i of
    7 -> state99 err (i:as) is
    9 -> state99 err (i:as) is
    12 -> state99 err (i:as) is
    13 -> state99 err (i:as) is
    14 -> state99 err (i:as) is
    19 -> state99 err (i:as) is
    20 -> state99 err (i:as) is
    21 -> state99 err (i:as) is
    23 -> state99 err (i:as) is
    48 -> state99 err (i:as) is
    49 -> state99 err (i:as) is
    75 -> state99 err (i:as) is
    22 -> state102 err (i:as) is
    _ -> err as iis

state109 :: LexerState
state109 err as [] = err as []
  where err _ _ = output Qconid as (start1 [])
state109 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    14 -> state98 err (i:as) is
    _ -> state109 err (i:as) is
  where err _ _ = output Qconid as (start1 iis)

start110 :: Lexer
start110 is = state110 (\ as is -> gotError as is) "" is
state110 :: LexerState
state110 err as [] = err as []
state110 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    _ -> state111 err (i:as) is

state111 :: LexerState
state111 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state111 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state112 :: LexerState
state112 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state112 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    51 -> state113 err (i:as) is
    61 -> state115 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state113 :: LexerState
state113 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state113 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    67 -> state114 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state114 :: LexerState
state114 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state114 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    55 -> state110 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state115 :: LexerState
state115 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state115 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    51 -> state116 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state116 :: LexerState
state116 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state116 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    67 -> state117 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state117 :: LexerState
state117 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state117 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    67 -> state110 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state118 :: LexerState
state118 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state118 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    64 -> state110 err (i:as) is
    51 -> state119 err (i:as) is
    55 -> state121 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state119 :: LexerState
state119 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state119 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    68 -> state120 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state120 :: LexerState
state120 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state120 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    51 -> state110 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state121 :: LexerState
state121 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state121 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    56 -> state122 err (i:as) is
    66 -> state126 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state122 :: LexerState
state122 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state122 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    51 -> state123 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state123 :: LexerState
state123 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state123 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    69 -> state124 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state124 :: LexerState
state124 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state124 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    61 -> state125 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state125 :: LexerState
state125 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state125 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    68 -> state110 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state126 :: LexerState
state126 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state126 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    59 -> state127 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state127 :: LexerState
state127 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state127 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    70 -> state128 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state128 :: LexerState
state128 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state128 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    59 -> state129 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state129 :: LexerState
state129 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state129 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    63 -> state130 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state130 :: LexerState
state130 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state130 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    57 -> state110 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state131 :: LexerState
state131 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state131 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    61 -> state113 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state132 :: LexerState
state132 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state132 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    56 -> state110 err (i:as) is
    62 -> state133 err (i:as) is
    63 -> state136 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state133 :: LexerState
state133 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state133 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    65 -> state134 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state134 :: LexerState
state134 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state134 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    64 -> state135 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state135 :: LexerState
state135 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state135 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    66 -> state125 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

start136 :: Lexer
start136 is = state136 (\ as is -> gotError as is) "" is
state136 :: LexerState
state136 err as [] = err as []
state136 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    56 -> state137 err (i:as) is
    67 -> state140 err (i:as) is
    _ -> state111 err (i:as) is

state137 :: LexerState
state137 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state137 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    59 -> state138 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state138 :: LexerState
state138 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state138 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    72 -> state139 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

start139 :: Lexer
start139 is = state139 (\ as is -> gotError as is) "" is
state139 :: LexerState
state139 err as [] = err as []
state139 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    61 -> state110 err (i:as) is
    66 -> state110 err (i:as) is
    _ -> state111 err (i:as) is

state140 :: LexerState
state140 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state140 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    68 -> state141 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state141 :: LexerState
state141 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state141 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    51 -> state142 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state142 :: LexerState
state142 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state142 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    63 -> state143 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state143 :: LexerState
state143 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state143 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    53 -> state114 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state144 :: LexerState
state144 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state144 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    55 -> state125 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state145 :: LexerState
state145 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state145 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    64 -> state146 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state146 :: LexerState
state146 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state146 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    54 -> state147 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state147 :: LexerState
state147 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state147 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    69 -> state148 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state148 :: LexerState
state148 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state148 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    61 -> state114 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state149 :: LexerState
state149 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state149 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    55 -> state150 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state150 :: LexerState
state150 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state150 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    71 -> state151 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state151 :: LexerState
state151 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state151 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    68 -> state152 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state152 :: LexerState
state152 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state152 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    73 -> state153 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state153 :: LexerState
state153 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state153 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    65 -> state114 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state154 :: LexerState
state154 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state154 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    56 -> state110 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state155 :: LexerState
state155 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state155 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    73 -> state153 err (i:as) is
    58 -> state156 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state156 :: LexerState
state156 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state156 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    55 -> state157 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state157 :: LexerState
state157 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state157 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    63 -> state110 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state158 :: LexerState
state158 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state158 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    58 -> state159 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state159 :: LexerState
state159 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state159 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    55 -> state160 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state160 :: LexerState
state160 err as [] = err as []
  where err _ _ = output Qvarid as (start1 [])
state160 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    66 -> state114 err (i:as) is
    _ -> state111 err (i:as) is
  where err _ _ = output Qvarid as (start1 iis)

state161 :: LexerState
state161 err as [] = err as []
  where err _ _ = output Reservedid as (start1 [])
state161 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    _ -> state162 err (i:as) is
  where err _ _ = output Reservedid as (start1 iis)

state162 :: LexerState
state162 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state162 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state163 :: LexerState
state163 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state163 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    51 -> state164 err (i:as) is
    61 -> state166 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state164 :: LexerState
state164 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state164 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    67 -> state165 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state165 :: LexerState
state165 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state165 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    55 -> state161 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state166 :: LexerState
state166 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state166 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    51 -> state167 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state167 :: LexerState
state167 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state167 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    67 -> state168 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state168 :: LexerState
state168 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state168 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    67 -> state161 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state169 :: LexerState
state169 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state169 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    64 -> state161 err (i:as) is
    51 -> state170 err (i:as) is
    55 -> state172 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state170 :: LexerState
state170 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state170 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    68 -> state171 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state171 :: LexerState
state171 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state171 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    51 -> state161 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state172 :: LexerState
state172 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state172 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    56 -> state173 err (i:as) is
    66 -> state177 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state173 :: LexerState
state173 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state173 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    51 -> state174 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state174 :: LexerState
state174 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state174 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    69 -> state175 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state175 :: LexerState
state175 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state175 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    61 -> state176 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state176 :: LexerState
state176 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state176 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    68 -> state161 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state177 :: LexerState
state177 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state177 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    59 -> state178 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state178 :: LexerState
state178 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state178 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    70 -> state179 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state179 :: LexerState
state179 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state179 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    59 -> state180 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state180 :: LexerState
state180 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state180 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    63 -> state181 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state181 :: LexerState
state181 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state181 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    57 -> state161 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state182 :: LexerState
state182 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state182 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    61 -> state164 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state183 :: LexerState
state183 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state183 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    56 -> state161 err (i:as) is
    62 -> state184 err (i:as) is
    63 -> state187 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state184 :: LexerState
state184 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state184 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    65 -> state185 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state185 :: LexerState
state185 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state185 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    64 -> state186 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state186 :: LexerState
state186 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state186 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    66 -> state176 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state187 :: LexerState
state187 err as [] = err as []
  where err _ _ = output Reservedid as (start1 [])
state187 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    56 -> state188 err (i:as) is
    67 -> state191 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Reservedid as (start1 iis)

state188 :: LexerState
state188 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state188 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    59 -> state189 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state189 :: LexerState
state189 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state189 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    72 -> state190 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state190 :: LexerState
state190 err as [] = err as []
  where err _ _ = output Reservedid as (start1 [])
state190 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    61 -> state161 err (i:as) is
    66 -> state161 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Reservedid as (start1 iis)

state191 :: LexerState
state191 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state191 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    68 -> state192 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state192 :: LexerState
state192 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state192 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    51 -> state193 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state193 :: LexerState
state193 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state193 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    63 -> state194 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state194 :: LexerState
state194 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state194 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    53 -> state165 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state195 :: LexerState
state195 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state195 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    55 -> state176 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state196 :: LexerState
state196 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state196 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    64 -> state197 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state197 :: LexerState
state197 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state197 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    54 -> state198 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state198 :: LexerState
state198 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state198 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    69 -> state199 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state199 :: LexerState
state199 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state199 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    61 -> state165 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state200 :: LexerState
state200 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state200 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    55 -> state201 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state201 :: LexerState
state201 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state201 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    71 -> state202 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state202 :: LexerState
state202 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state202 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    68 -> state203 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state203 :: LexerState
state203 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state203 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    73 -> state204 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state204 :: LexerState
state204 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state204 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    65 -> state165 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state205 :: LexerState
state205 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state205 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    56 -> state161 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state206 :: LexerState
state206 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state206 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    73 -> state204 err (i:as) is
    58 -> state207 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state207 :: LexerState
state207 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state207 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    55 -> state208 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state208 :: LexerState
state208 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state208 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    63 -> state161 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state209 :: LexerState
state209 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state209 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    58 -> state210 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state210 :: LexerState
state210 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state210 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    55 -> state211 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state211 :: LexerState
state211 err as [] = err as []
  where err _ _ = output Varid as (start1 [])
state211 err as iis@(i:is) =
  case cclass i of
    0 -> err as iis
    1 -> err as iis
    2 -> err as iis
    3 -> err as iis
    4 -> err as iis
    5 -> err as iis
    6 -> err as iis
    7 -> err as iis
    8 -> err as iis
    9 -> err as iis
    11 -> err as iis
    12 -> err as iis
    13 -> err as iis
    14 -> err as iis
    19 -> err as iis
    20 -> err as iis
    21 -> err as iis
    22 -> err as iis
    23 -> err as iis
    47 -> err as iis
    48 -> err as iis
    49 -> err as iis
    74 -> err as iis
    75 -> err as iis
    76 -> err as iis
    66 -> state165 err (i:as) is
    _ -> state162 err (i:as) is
  where err _ _ = output Varid as (start1 iis)

state212 :: LexerState
state212 err as [] = err as []
  where err _ _ = output Special as (start1 [])
state212 err as iis@(i:is) =
  case cclass i of
    13 -> state213 err (i:as) is
    _ -> err as iis
  where err _ _ = output Special as (start1 iis)

state213 :: LexerState
state213 err as is = nestedComment as is state214

state214 :: LexerState
state214 err as is = output NestedComment as (start1 is)


