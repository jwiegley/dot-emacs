module Complex_Vectors
        (ComplexF, rootsOfUnity,thetas, norm,distance)
where
import Complex --
--import Strategies
-- import Parallel

type ComplexF = Complex Double
rootsOfUnity:: Int -> [ComplexF]
rootsOfUnity n =( zipWith (:+) cvar svar)  -- (map cos (thetas n))- (map sin (thetas n))
          where
             cvar = (map cos (thetas n))
             svar = (map sin (thetas n))

thetas:: Int -> [Double]
thetas n = --[(2*pi/fromInt n)*fromInt k | k<-[0 .. n-1]]
          (map(\k -> ((2*pi/fromInt n)*fromInt k)) [k | k<-[0 .. n-1]]) --`using` parListChunk 20 rnf  


fromInt :: (Num a) => Int -> a
fromInt i = fromInteger (toInteger i)
norm:: [ComplexF] -> Double
norm = sqrt.sum.map((^2).magnitude)
distance:: [ComplexF] -> [ComplexF] -> Double
distance z w = norm(zipWith (-) z w)

