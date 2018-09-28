module StriDi.DSL where

import Prelude hiding ((**), (*))
import StriDi.Cells

infixr 6 **
infixl 7 *

class Composable a where
    (*) :: a -> a -> a
    (**) :: a -> a -> a

instance Composable A1Cell where
    (*) = flip cmpA1
    (**) = (*)

instance Composable A2Cell where
    (*) = cmpA2
    (**) = flip tensorA2

