{-# LANGUAGE OverloadedStrings #-}
module StriDi.DSL.PROP where

import Prelude hiding ((**), (*))
import Data.Text
import Control.Monad.RWS.Strict
import Control.Monad.Identity
import Text.LaTeX hiding (dot)
import StriDi.Cells
import StriDi.DSL
import StriDi.DSL.Monoidal hiding (new2C, new1COptions, new2COptions)

generating1Cell :: A1Cell
generating1Cell = new1C ""

mk1C :: Int -> A1Cell
mk1C 0 = idA1 monoidal0Cell
mk1C n = generating1Cell ** mk1C (n-1)

id2 :: Int -> A2Cell
id2 = idA2 . mk1C

new2COptions :: LaTeX -> [Text] -> Int -> Int -> A2Cell
new2COptions s o f g = mkA2 (D2Cell s o) (mk1C f) (mk1C g)

new2C :: Int -> Int -> A2Cell
new2C f g = new2COptions "" dot f g

dot :: [Text]
dot = ["circle", "draw=black", "fill=black", "minimum size=1mm", "inner sep=0mm"]
