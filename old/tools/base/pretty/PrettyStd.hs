module PrettyStd where
import PrettyPrint2
import Data.Ratio

-- Predefined instances:


instance Printable Bool    where wrap = ppi
instance Printable Int     where wrap = ppi
instance Printable Integer where wrap = ppi
instance Printable Float   where wrap = ppi
instance Printable Double  where wrap = ppi
instance (Integral a,Show a) => Printable (Ratio a) where wrap = ppi

instance Printable a => Printable (Maybe a) where
    ppi (Just a) = ppi a
    ppi Nothing  = empty

    wrap (Just a) = wrap a
    wrap Nothing  = empty

instance Printable () where
    ppi () = parens empty
    wrap = ppi

instance (Printable a, Printable b) => Printable (a, b) where
    ppi (a, b) = parens $ ppi a <> ',' <+> ppi b
    wrap = ppi

instance (Printable a, Printable b, Printable c) => Printable (a, b, c) where
    ppi (a, b, c) = parens $ ppi a <> ',' <+>
                             ppi b <> ',' <+>
                             ppi c
    wrap = ppi

instance (Printable a, Printable b, Printable c, Printable d) =>
    Printable (a, b, c, d) where
    ppi (a, b, c, d) = parens $ ppi a <> ',' <+>
                                ppi b <> ',' <+>
                                ppi c <> ',' <+>
				ppi d
    wrap = ppi

instance (Printable a, Printable b, Printable c, Printable d, Printable e) =>
    Printable (a, b, c, d, e) where
    ppi (a, b, c, d, e) = parens $ ppi a <> ',' <+>
                                   ppi b <> ',' <+>
                                   ppi c <> ',' <+>
				   ppi d <> ',' <+>
				   ppi e
    wrap = ppi
