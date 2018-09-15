{-# LANGUAGE OverloadedStrings #-}
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
    (*) = flip cmpA1
    (**) = (*)

instance Composable A2Cell where
    (*) = cmpA2
    (**) = flip tensorA2

monoidal0Cell :: A0Cell
monoidal0Cell = mkA0 $ ZeroCellData "*"

id1 :: A1Cell
id1 = idA1 monoidal0Cell

new1COptions :: LaTeX -> [Text] -> [Text] -> A1Cell
new1COptions s o d = mkA1 (OneCellData s o d) monoidal0Cell monoidal0Cell

new1C :: LaTeX -> A1Cell
new1C s = new1COptions s default1COptions []

default1COptions :: [Text]
default1COptions = []


id2 :: A1Cell -> A2Cell
id2 = idA2

new2COptions :: LaTeX -> [Text] -> A1Cell -> A1Cell -> A2Cell
new2COptions s o f g = mkA2 (TwoCellData s o) f g

new2C :: LaTeX -> A1Cell -> A1Cell -> A2Cell
new2C s f g = new2COptions s default2COptions f g

default2COptions :: [Text]
default2COptions = ["rectangle", "draw", "fill=white"]


class Sealable a where
    seal :: LaTeX -> a -> a

instance Sealable A1Cell where
    seal s (A1Cell c) = A1Cell $ seal1Cell (OneCellData s default1COptions []) c

instance Sealable A2Cell where
    seal s (A2Cell c) = A2Cell $ seal2Cell (TwoCellData s default2COptions) c

