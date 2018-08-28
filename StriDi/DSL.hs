module StriDi.DSL where

import Prelude hiding ((.), (*), id)
import Data.Text
import Control.Monad.RWS.Strict
import Control.Monad.Identity
import StriDi.Cells


class Composable a where
    (*) :: a -> a -> a
    (**) :: a -> a -> a

instance Composable A1Cell where
    (A1Cell x) * (A1Cell y) = A1Cell $ x ++ y
    (**) = (*)

instance Composable A2Cell where
    (*) = ACmp2
    (**) = ATensor2

monoidal0Cell :: A0Cell
monoidal0Cell = A0Cell (AutoId 0) (pack "$*$")

new1C :: Text -> A1Cell
new1C s = A1Cell [A1Atom {
    identifier1 = CustomId s,
    label1 = s,
    src1 = monoidal0Cell,
    tgt1 = monoidal0Cell
}]

new2C :: Text -> A1Cell -> A1Cell -> A2Cell
new2C s src tgt = AAtom2 $ A2Atom {
    identifier2 = CustomId s,
    label2 = s,
    src2 = src,
    tgt2 = tgt
}


-- data StriDiState = StriDiState {

-- }

-- data Definition = Def0 A0Cell | Def1 A1Cell | Def2 A2Cell

-- type StriDiMonadT = RWST () () StriDiState
-- type StriDiMonad = StriDiMonadT Identity

-- example :: StriDiMonad A2Cell
-- example = do
--     a <- new0C
--     b <- new0C
--     f <- new1C "f" a b
--     g <- new1C "g" b b
--     al <- new2C "$\\alpha$" f (f . g)
--     be <- new2C "$\\beta$" g f
--     return $ al . (id f * be)
