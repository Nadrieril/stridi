module StriDi.DSL where

import Prelude hiding ((**), (*))
import Data.Text
import Control.Monad.RWS.Strict
import Control.Monad.Identity
import Text.LaTeX
import StriDi.Cells


class Composable a where
    (*) :: a -> a -> a
    (**) :: a -> a -> a

instance Composable A1Cell where
    (*) = cmpA1
    (**) = (*)

instance Composable A2Cell where
    (*) = cmpA2
    (**) = tensorA2

monoidal0Cell :: A0Cell
monoidal0Cell = mkA0 $ ZeroCellData (raw $ pack "*")

new1C :: LaTeX -> A1Cell
new1C s = mkA1 (OneCellData s) monoidal0Cell monoidal0Cell

id1 :: A1Cell
id1 = idA1 monoidal0Cell

new2C :: LaTeX -> A1Cell -> A1Cell -> A2Cell
new2C s = mkA2 (TwoCellData s)

id2 :: A1Cell -> A2Cell
id2 = idA2


class Sealable a where
    seal :: LaTeX -> a -> a

instance Sealable A2Cell where
    seal s (A2Cell c) = A2Cell $ seal2Cell (TwoCellData s) c

