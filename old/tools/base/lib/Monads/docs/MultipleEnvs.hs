import IxEnvMT
import StateMT
import ImpUtils

{- An exmaple of using two environments -}


type M = WithEnv Int 
       ( WithState Bool 
       ( WithEnv Char 
         IO ))

intOne = at :: Z
intTwo = at :: S Z


test :: M ()
test = do
    int <- getEnv intOne
    char <- getEnv intTwo
    io $ print int
    io $ print char

main = withEnv 'a' $ withSt True $ withEnv 4 test


