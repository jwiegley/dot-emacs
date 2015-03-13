module ParseMyDoc where

import MyDoc

import Control.Monad
import Data.List
import Data.Maybe
import Data.Char

import StateM
--import MUtils

-- Constants
tabWidth    = 8

data CharClass = CodeChar | ItemChar | UnderChar
                deriving Eq


chars =
    [ (CodeChar, ['>', '|'])
    , (ItemChar, ['*', '-'])
    , (UnderChar, ['=', '-', '~'])
    ]

get x = fromJust (lookup x chars)


-- Character classes
is t c = c `elem` get t


-- Line types
codeL (n,x:xs)  = n == 0 && is CodeChar x
codeL _         = False
blankL (n,x)    = null x
underL (n,x:xs) = is UnderChar x && all (== x) xs
underL _        = False
itemL (n,x:y:_) = is ItemChar x && isSpace y
itemL _         = False

-- underline types
lvl (_,x:_)
    | is UnderChar x    = fromJust $ elemIndex x (get UnderChar)
    | otherwise         = error "not underline character"

stripList = drop 2

-- Utilities
indent x = (foldr add 0 (takeWhile isSpace x), dropWhile isSpace x)
    where
    add '\t'    = (+ tabWidth)
    add _       = (+ 1)

eIf p a b = either (const a) (const b) p
eMap f g  = either (Left . f) (Right . g)

grpEither :: [Either a b] -> [Either [a] [b]]
grpEither = map grp . groupBy eq
    where
    eq x y          = eIf x (eIf y True False) (eIf y False True)
    grp xs@(x: _)   = eIf x (Left $ unL `map` xs) (Right $ unR `map` xs)
    unL = either id undefined
    unR = either undefined id


parse =  map (eMap f id) . sepCodeAndText . map indent . lines
    where
    f = proc initSt
    initSt  = [ St
        { offset = 0
        , curTxt = []
        , curItem = []
        , curList = []
        } ]



sepCodeAndText = grpEither . map identify
    where
    identify l@(n,txt)
        | codeL l   = Right (tail txt)
        | otherwise = Left l

data St = St
    { offset    :: Integer
    , curTxt    :: [String]
    , curItem   :: [Paragraph]
    , curList   :: [TxtBlock]
    }
    deriving Show


newList m txt = St
    { offset    = m
    , curTxt    = [stripList txt]
    , curItem   = []
    , curList   = []
    }

newItem txt st  = (endItem st) { curTxt = [stripList txt] }

-- add the blank text to compensate for the removed underlining
-- it is at the front becuase it will later be reversed
newHeading h st = endItem $ newLine $ (endItem st) { curItem = [h] }
newTxt txt st   = st { curTxt = txt : curTxt st }
newLine st      = st { curTxt = [] : curTxt st }

endTxt st
    | null (curTxt st)  = st
    | otherwise = st
        { curTxt = []
        , curItem = toPar (curTxt st) : curItem st
        }
    where
    toPar = Txt . dec . reverse
{-
    unl []          = []
    unl [x]         = x
    unl (x:y:zs)    = x ++ "\n" ++ y ++ unl zs
-}

endItem st = let s = endTxt st in
    if null (curItem s) then s
    else s
    { curItem = []
    , curList = toItm (curItem s) : curList s
    }
    where
    toItm = reverse

endList []          = error "endList: []"
endList [x]         = [x]
endList (st:x:xs)   = x { curItem = l : curItem x } : xs
    where
    l = Lst $ reverse $ curList (endItem st)

endAllLists []  = error "endAllLists: []"
endAllLists [x] = [endItem x]
endAllLists xss = endAllLists (endList xss)


proc [] _   = error "proc: [] _"

proc sts [] = reverse $ curList $ top (endAllLists sts)

proc sts (l1:l2:ls)
    | underL l2
        = let [st]  = endAllLists sts
              st'   = newHeading (H (lvl l2, getTxt l1)) st
          in proc [st'] ls


proc [st] (l:ls)
    | blankL l  = let st' = endItem st
                  in proc [newLine st'] ls


proc stack (l:ls)
    | blankL l  = proc (apTop newLine stack) ls
    | m == n && itemL l = proc (apTop (newItem txt) stack) ls
    | n >= m = if itemL l
                then proc (push (newList n txt) (apTop endTxt stack)) ls
                else proc (apTop (newTxt txt) stack) ls
    | otherwise = let x:xs = endList stack
                  in proc (apTop (newTxt txt) (endList stack)) ls
    where
    m   = offset (top stack)
    n   = getPos l
    txt = getTxt l


getPos = fst
getTxt = snd

push = (:)
top = head

apTop f (x:xs)  = f x : xs
apTop _ _       = error "apTop: []"



dec = decorate Plain

decorate _ [] = []
decorate t (xs:xss)
    = let (_,(ws,a,s))= withStS ([],"",t) (mapM_ toAct xs)
      in reverse ((s,reverse a):ws) : decorate s xss

toAct '_' = act '_' Emph
toAct '#' = act '#' Code
toAct '$' = act '$' Math
toAct x   = addChar x

chgTo s = do
    (ws,a,t) <- getSt
    setSt_ ((t,reverse a):ws,"",s)

addChar c = do
    (ws,a,t) <- getSt
    setSt_ (ws,c:a,t)

act c state = do
    (ws,a,s) <- getSt
    case s of
        Plain   -> chgTo state
        x
            | x == state    -> chgTo Plain
            | otherwise     -> addChar c


