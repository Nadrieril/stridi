{-# LANGUAGE OverloadedStrings, DataKinds, TypeOperators, TypeApplications #-}
module Text.LaTeX.StriDi where

import qualified Data.Text as T
import qualified Data.Text.IO as T
import Text.LaTeX
import Text.LaTeX.Base.Syntax
import Text.LaTeX.Base.Class
import StriDi.Render

instance Texy (f :--> g) where
    texy c = texy $ TeXEnv "tikzpicture" [] $ raw $ draw2Cell c

