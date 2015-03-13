module MyDoc where

import Text.PrettyPrint
import EnvM
import MUtils 
import Control.Monad
import Data.Char(isSpace)


type Heading    = (Int,String)
data TxtDec     = Plain | Emph | Code | Math    deriving (Eq,Show)
type DecString  = (TxtDec,String)

type Code       = [String]
type TxtBlock   = [Paragraph]
data Paragraph  = Txt [[DecString]] | Lst [TxtBlock] | H Heading  deriving Show

type MyDoc      = [Either TxtBlock Code]


data Style = Style 
    { ppHeading   :: Heading -> Doc
    , ppDecStr    :: DecString -> Doc
    , ppCode      :: Code -> Doc

    , ppList      :: [Doc] -> Doc
    , ppItem      :: Doc -> Doc

    , ppParagraph :: Doc -> Doc

    , ppText      :: Doc -> Doc
    , ppFinalize  :: Doc -> Doc
    }


env f x = do e <- getEnv
             return (f e x)

ppH x = env ppHeading x
ppS x = env ppDecStr x
ppC x = env ppCode x

ppL x = env ppList x
ppI x = env ppItem x

ppP x = env ppParagraph x
ppT x = env ppText x
ppF x = env ppFinalize x


ppMyDoc d = ppF =<< (vcat # mapM (either topLevel ppC) d)

topLevel d = ppT =<< (vcat # mapM prt d)
    where
    prt ((H h):xs)  = liftM2 ($$) (ppH h) (prt xs)
    prt ((Txt as):xs) 
        | emp as    = (text "" $$) # prt xs

    prt x           = vcat # mapM (ppP @@ ppPar) x
    

ppTxtBlock d    = vcat # mapM ppPar d

ppPar (Txt tss) = vcat # mapM (\ts -> hcat # mapM ppS ts) tss
ppPar (Lst is)  = ppL =<< mapM (ppI @@ ppTxtBlock) is
ppPar (H _)     = error "inner heading? (MyDoc.hs)"

emp []          = True
emp ([]:xss)    = emp xss
emp (xs:xss)    = all (all isSpace.snd) xs && emp xss




