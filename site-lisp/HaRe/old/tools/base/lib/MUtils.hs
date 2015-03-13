-- Thomas' misc utils (things that are missing in the standard libraries)
module MUtils where
import Control.Monad(ap,unless,when)
import Data.List(groupBy,sortBy,sort)
import Data.Maybe(fromMaybe)
--import ExceptM()

-- all eta expansions because of the stupid monomorphism restriction

infixl 1 #,#.,<#,@@, >#<

-- Infix versions of two essential operators:
f # x = fmap f x
mf <# mx  = ap mf mx

--Kleisli composition, another essential operator, sadly lacking from the
--Haskell 98 libraries:
m1 @@ m2 = \ x -> m1 =<< m2 x

f #. m = \ x -> f # m x

done :: Monad m => m ()
done = return ()

unlessM m1 m2 = do b <- m1
		   unless b m2

whenM m1 m2 = do b <- m1
		 when b m2

ifM bM tM eM = do b <- bM; if b then tM else eM
aM &&& bM = ifM aM bM (return False)
andM ms = foldr (&&&) (return True) ms
allM p = andM . map p

seqMaybe m = maybe (return Nothing) (Just # ) m

-- Property: f # x == return f <# x

(f >#< g) (x,y) = (,) # f x <# g y

mapFstM f = mapM (apFstM f)
apFstM f (x,y) = flip (,) y # f x
mapSndM f = mapM (apSndM f)
apSndM f (x,y) = (,) x # f y

concatMapM f xs = concat # mapM f xs

mapFst f = map (apFst f)
mapSnd f = map (apSnd f)
apSnd f (x,y) = (x,f y)
apFst f (x,y) = (f x,y)

mapBoth f = map (apBoth f)
apBoth f (x,y) = (f x,f y)
dup x = (x,x)
pairWith f x = (x,f x)
-- pairWith f = apSnd f . dup

mapPartition f [] = ([],[])
mapPartition f (x:xs) = either (apFst.(:)) (apSnd.(:)) (f x) (mapPartition f xs)


collectBySnd x =
    map pick .
    groupBy eqSnd .
    sortBy cmpSnd $ x
  where
    pick xys@((_,y):_) = ({-sort $-} map fst xys,y)

collectByFst x = map swap . collectBySnd . map swap $ x

onFst f (x1,_) (x2,_) = f x1 x2
onSnd f (_,y1) (_,y2) = f y1 y2
cmpFst x = onFst compare x
cmpSnd x = onSnd compare x
eqFst x = onFst (==) x
eqSnd x = onSnd (==) x

swap (x,y) = (y,x)

mapEither f g = either (Left . f) (Right . g)
seqEither x = either (Left # ) (Right # ) x

-- squeezeDups removes adjacent duplicates (cheaper than nub):
squeezeDups (r1:rrs@(r2:_)) = if r1==r2
			      then squeezeDups rrs
			      else r1:squeezeDups rrs
squeezeDups rs = rs

usort xs = squeezeDups (sort xs)

read' s = read'' "MUtils.read'" s

read'' msg s =
  case reads s of
    [(x,r)] | readAtEnd r -> x
    [] -> error $ msg++" no parse: "++take 60 s
    _ ->  error $ msg++" ambiguous parse: "++take 60 s

readAtEnd r = lex r == [("","")]

fromJust' = fromMaybe . error

--instance Functor ((->) a) where fmap = (.)

{-
instance Functor (Either err) where
  fmap = mapEither id

instance Monad (Either err) where
  return = Right
  Left err >>= _ = Left err
  Right ans >>= m = m ans
-}
