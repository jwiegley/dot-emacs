------------------------------------------------------------------------------
-- Standard Library: Random numbers
--
-- Suitable for use with Hugs 98
--
-- The code in this file draws heavily from several different sources,
-- including the implementations in previous Hugs and GHC implementations.
-- Much of this was done by Sigbjorn Finne.  If there are mistakes here,
-- blame me.  The random number generation itself is based on a published
-- article by L'Ecuyer that was transliterated into Haskell by Lennart
-- Augustsson.  See the comments below for further details.
------------------------------------------------------------------------------

module Random(
	RandomGen(next, split),
	StdGen, mkStdGen,
	Random( random,   randomR,
		randoms,  randomRs,
		randomIO, randomRIO ),
	getStdRandom, getStdGen, setStdGen, newStdGen
  ) where

import IOExts  ( IORef, newIORef, writeIORef, readIORef,
		 unsafePerformIO
	       )
import Numeric ( showInt, showSigned, readDec )
import Char(ord,chr,isSpace)

-- The RandomGen class: ------------------------------------------------------

class RandomGen g where
   next  :: g -> (Int, g)
   split :: g -> (g, g)


-- An efficient and portable combined random number generator: ---------------
--
-- The June 1988 (v31 #6) issue of the Communications of the ACM has an
-- article by Pierre L'Ecuyer called, "Efficient and Portable Combined
-- Random Number Generators".  Here is the Portable Combined Generator of
-- L'Ecuyer for 32-bit computers.  It has a period of roughly 2.30584e18.
-- 
-- Transliterator: Lennart Augustsson
-- sof 1/99 - code brought (kicking and screaming) into the new Random
-- world..
------------------------------------------------------------------------------

data StdGen = StdGen Int Int

mkStdGen	      :: Int -> StdGen
mkStdGen seed          = StdGen (s1+1) (s2+1)
                         where s       = abs seed
			       (q, s1) = s `divMod` 2147483562
			       s2      = q `mod` 2147483398

stdFromString         :: String -> (StdGen, String)
stdFromString s        = (mkStdGen num, rest)
	where (cs, rest) = splitAt 6 s
              num        = foldl (\a x -> x + 3 * a) 1 (map ord cs)

stdNext               :: StdGen -> (Int, StdGen)
stdNext (StdGen s1 s2) = (z', StdGen s1'' s2'')
	where	z'   = if z < 1 then z + 2147483562 else z
		z    = s1'' - s2''

		k    = s1 `quot` 53668
		s1'  = 40014 * (s1 - k * 53668) - k * 12211
		s1'' = if s1' < 0 then s1' + 2147483563 else s1'
    
		k'   = s2 `quot` 52774
		s2'  = 40692 * (s2 - k' * 52774) - k' * 3791
		s2'' = if s2' < 0 then s2' + 2147483399 else s2'

stdSplit            :: StdGen -> (StdGen, StdGen)
stdSplit std@(StdGen s1 s2)
                     = (left, right)
                       where
                        -- no statistical foundation for this!
                        left    = StdGen new_s1 t2
                        right   = StdGen t1 new_s2

                        new_s1 | s1 == 2147483562 = 1
                               | otherwise        = s1 + 1

                        new_s2 | s2 == 1          = 2147483398
                               | otherwise        = s2 - 1

                        StdGen t1 t2 = snd (next std)

-- A standard instance of RandomGen: -----------------------------------------

instance RandomGen StdGen where
  next  = stdNext
  split = stdSplit

instance Show StdGen where
  showsPrec p (StdGen s1 s2)
    = showSigned showInt p s1 .  showChar ' ' . showSigned showInt p s2

instance Read StdGen where
  readsPrec p = \ r ->
    case try_read r of
       r@[_] -> r
       _     -> [stdFromString r] -- because it shouldn't ever fail.
    where 
      try_read r = do
         (s1, r1) <- readDec (dropWhile isSpace r)
	 (s2, r2) <- readDec (dropWhile isSpace r1)
	 return (StdGen s1 s2, r2)


-- The Random class: ---------------------------------------------------------

class Random a where
  -- Minimal complete definition: random and randomR
  random          :: RandomGen g => g -> (a, g)
  randomR         :: RandomGen g => (a,a) -> g -> (a,g)
  
  randoms         :: RandomGen g => g -> [a]

  randomRs        :: RandomGen g => (a,a) -> g -> [a]

  randomIO        :: IO a

  randomRIO       :: (a,a) -> IO a

  randomRIO range  = getStdRandom (randomR range)
  randomRs ival g  = x : randomRs ival g' where (x,g') = randomR ival g
  randomIO	   = getStdRandom random
  randoms  g       = x : randoms g' where (x,g') = random g

instance Random Int where
  random g        = randomR (minBound,maxBound) g
  randomR (a,b) g = randomIvalInteger (toInteger a, toInteger b) g

instance Random Char where
  random g	  = randomR (minBound,maxBound) g
  randomR (a,b) g = 
      case (randomIvalInteger (toInteger (ord a), toInteger (ord b)) g) of
        (x,g) -> (chr x, g)

instance Random Bool where
  random g	  = randomR (minBound,maxBound) g
  randomR (a,b) g = 
      case (randomIvalInteger (toInteger (bool2Int a), toInteger (bool2Int b)) g) of
        (x, g) -> (int2Bool x, g)
       where
         bool2Int False = 0
         bool2Int True  = 1

	 int2Bool 0	= False
	 int2Bool _	= True
 
instance Random Integer where
  random g	 = randomR (toInteger (minBound::Int),
                            toInteger (maxBound::Int)) g
  randomR ival g = randomIvalInteger ival g

instance Random Double where
  random g       = randomR (0::Double,1) g
  randomR ival g = randomIvalDouble ival id g
  
-- hah, so you thought you were saving cycles by using Float?
instance Random Float where
  random g        = randomIvalDouble (0::Double,1) realToFrac g
  randomR (a,b) g = randomIvalDouble (realToFrac a, realToFrac b) realToFrac g


-- Auxiliary functions: ------------------------------------------------------

randomIvalInteger :: (RandomGen g, Num a) => (Integer, Integer) -> g -> (a, g)
randomIvalInteger (l,h) rng
 | l > h     = randomIvalInteger (h,l) rng
 | otherwise = case (f n 1 rng) of
                 (v, rng') -> (fromInteger (l + v `mod` k), rng')
   where
     k = h - l + 1
     b = 2147483561
     n = iLogBase b k

     f 0 acc g = (acc, g)
     f n acc g = let (x,g') = next g
		 in f (n-1) (fromIntegral x + acc * b) g'

randomIvalDouble :: (RandomGen g, Fractional a)
			=> (Double, Double) -> (Double -> a) -> g -> (a, g)
randomIvalDouble (l,h) fromDouble rng 
  | l > h     = randomIvalDouble (h,l) fromDouble rng
  | otherwise = 
       case (randomIvalInteger (toInteger (minBound::Int), toInteger (maxBound::Int)) rng) of
         (x, rng') -> 
	    let
	     scaled_x = 
		fromDouble ((l+h)/2) + 
                fromDouble ((h-l) / realToFrac intRange) *
		fromIntegral (x::Int)
	    in
	    (scaled_x, rng')

intRange :: Integer
intRange  = toInteger (maxBound::Int) - toInteger (minBound::Int)

iLogBase :: Integer -> Integer -> Integer
iLogBase b i = if i < b then 1 else 1 + iLogBase b (i `div` b)


-- The global standard random number generator: ------------------------------

foreign import getRandomSeed :: IO Integer

global_rng    :: IORef StdGen
global_rng     = unsafePerformIO (do seed <- getRandomSeed
                                     newIORef (mkStdGen (fromIntegral seed)))

setStdGen     :: StdGen -> IO ()
setStdGen sgen = writeIORef global_rng sgen

getStdGen     :: IO StdGen
getStdGen      = readIORef global_rng

newStdGen     :: IO StdGen
newStdGen      = do rng <- getStdGen
                    let (a,b) = split rng
                    setStdGen a
                    return b

getStdRandom  :: (StdGen -> (a,StdGen)) -> IO a
getStdRandom f = do rng	<- getStdGen
                    let (v, new_rng) = f rng
                    setStdGen new_rng
                    return v


------------------------------------------------------------------------------
