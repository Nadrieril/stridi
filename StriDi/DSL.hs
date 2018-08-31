module StriDi.DSL where

import Prelude hiding ((**), (*))
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


srcA2Cell :: A2Cell -> A1Cell
srcA2Cell (AId2 c) = c
srcA2Cell (AAtom2 atom) = src2 atom
srcA2Cell (c `ACmp2` _) = srcA2Cell c
srcA2Cell (c1 `ATensor2` c2) = srcA2Cell c1 * srcA2Cell c2

tgtA2Cell :: A2Cell -> A1Cell
tgtA2Cell = srcA2Cell . revA2Cell


class Sealable a where
    seal :: Text -> a -> a

instance Sealable A2Cell where
    seal s c = new2C s (srcA2Cell c) (tgtA2Cell c)

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
