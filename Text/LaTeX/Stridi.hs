{-# LANGUAGE OverloadedStrings, DataKinds, TypeOperators, TypeApplications #-}
module Text.LaTeX.Stridi where

import qualified Data.Text as T
import qualified Data.Text.IO as T
import Text.LaTeX
import Text.LaTeX.Base.Syntax
import Text.LaTeX.Base.Class
import Stridi.Render

instance Texy (f :--> g) where
    texy c = texy $ TeXEnv "tikzpicture" [] $ raw $ draw2Cell c

