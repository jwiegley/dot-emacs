module Fourier where

import Complex
import Complex_Vectors
import List(transpose)

splitAtN :: Int -> [a] -> [[a]]
splitAtN n [] = []
splitAtN n xs = ys : splitAtN n zs
           where (ys,zs) = splitAt n xs

ffth :: [ComplexF] -> [ComplexF] -> [ComplexF]
ffth xs us
 -- do not use PAR_FFT
 | n>1    = (ffmups (replikate fftEvn)  (ffmus us  (replikate fftOdd)))
 | n==1   = xs
 where
   rvv = ffmus us  (replikate fftOdd)
   rvv1 = replikate fftEvn 
   fftEvn = ffth (evns xs) uEvns
   fftOdd = ffth (odds xs) uEvns
   uEvns = evns us
   evns = everyNth 2
   odds = everyNth 2 . tail
   n = length xs

    ----  Discrete Fourier Transform (fft generalized to non-binary orders)
ffmus :: [ComplexF] -> [ComplexF] -> [ComplexF]
ffmus ns ms =  zipWith (*) ns ms 

ffmups :: [ComplexF] -> [ComplexF] -> [ComplexF]
ffmups ns ms =  zipWith (+) ns ms 

          
dft:: [ComplexF] -> [ComplexF] 
     -- time=O(n*sum(map (^2) (factors n))) algorithm
     --     =O(n*log(n)) when n is a product of small primes
dft xs
 = (map((1/(fromInt n))*) (dfth fs xs us)) 
 where
   us = replikate(map conjugate (rootsOfUnity n))
   fs = factors n
   n = length xs
   fromInt = fromInteger . toInteger -- partain addition
dftinv:: [ComplexF] -> [ComplexF]
     -- time=O(n*sum(map (^2) (factors n))) algorithm
     --     =O(n*log(n)) when n is a product of small primes
dftinv xs
 = dfth fs xs us
 where
   us = replikate(rootsOfUnity n)
   fs = factors n
   n = length xs

dfth:: [Int] -> [ComplexF] -> [ComplexF] -> [ComplexF]
dfth (f:fs) xs us
 | fs==[]      = sfth f xs us
 | otherwise   =( map   sum (transpose pfts)) 
  where
   pfts = [(dftOfSection k) `times` (us `toThe` k)| k<-[0..f-1]]
   dftOfSection k = repl f (dfth fs (fsectionOfxs k) (us `toThe` f))
   fsectionOfxs k = everyNth f (drop k xs)


-- Slow Fourier Transform

sft:: [ComplexF] -> [ComplexF]     -- time=O(n^2) algorithm
sft xs
 = map((1/(fromInt n))*) (sfth n xs us)
 where
   us = replikate(map conjugate (rootsOfUnity n))
   n = length xs
   fromInt = fromInteger . toInteger -- partain addition

sftinv:: [ComplexF] -> [ComplexF]  -- time=O(n^2) algorithm
sftinv xs
 = sfth n xs us
 where
   us = replikate(rootsOfUnity n)
   n = length xs
sfth:: Int -> [ComplexF] -> [ComplexF] -> [ComplexF]
sfth n xs us
 = [sum(xs `times` upowers)| upowers<-[us `toThe` k| k<-[0..n-1]]]

--  Slow Cosine Transform

sct:: [Double] -> [Double]  -- time=O(n^2) algorithm -- computes n^2 cosines
sct xs = concat((splitAtN 20 (map (\k -> (xs_dot (map  (cos.((fromInt k)*)) (thetas n)))) [k | k<-[0 .. n-1]]))) 






 
-- [xs_dot (map  (cos.((fromInt k)*)) (thetas n))| k<-[0 .. n-1]]

 where
   n = length xs
   xs_dot = sum.(zipWith (*) xs)
   fromInt = fromInteger . toInteger -- partain addition


--   Utilities

plus  = zipWith (+)
times = zipWith (*)
replikate = cycle
repl n = concat . take n . repeat
everyNth n = (map head).(takeWhile (/=[])).(iterate (drop n))
toThe:: [ComplexF] -> Int -> [ComplexF]
rootsOfUnity `toThe` k = everyNth k rootsOfUnity

factors:: Int -> [Int]
factors n = factorsh n primes

factorsh:: Int -> [Int] -> [Int]
factorsh n (p:ps)
 | n==1             = []
 | n `mod` p == 0   = p: factorsh (n `div` p) (p:ps)
 | otherwise        = factorsh n ps

primes:: [Int]
primes = map head (iterate sieve [2..])
sieve(p:xs) = [x| x<-xs, x `mod` p /= 0]