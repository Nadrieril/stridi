module StriDi.DSL where

import Prelude hiding ((.), (*), id)
import Data.Text
import Control.Monad.RWS.Strict


type Identifier = text

class Composable a where
    (.) :: a -> a -> a
    (*) :: a -> a -> a


data A0Cell = A0Cell {
    name0 :: Identifier,
    label0 :: Text
} deriving (Eq)


data A1Atom = A1Atom {
    name1 :: Identifier,
    label1 :: Text,
    src1 :: A0Cell,
    tgt1 :: A0Cell
} deriving (Eq)

data A1Cell = A1Cell [A1Atom]

instance Composable A1Cell where
    (A1Cell x) . (A1Cell y) = A1Cell $ x ++ y
    (*) = (.)


data A2Atom = A2Atom {
    name2 :: Identifier,
    label2 :: Text,
    src2 :: A1Cell,
    tgt2 :: A1Cell
} deriving (Eq)

data A2Cell =
    Atom2 A2Atom
    | Id2 A1Cell
    | Cmp2 A2Cell A2Cell
    | Tensor2 A2Cell A2Cell

instance Composable A2Cell where
    (.) = Cmp2
    (*) = Tensor2


-- data Definition = Def0 A0Cell | Def1 A1Cell | Def2 A2Cell

-- type StriDiMonadT = RWST () () (Map Identifier Definition)
