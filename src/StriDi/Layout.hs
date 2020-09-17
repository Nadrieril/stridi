{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, FlexibleContexts,
    RecordWildCards, AllowAmbiguousTypes, ViewPatterns, TypeFamilies, TypeFamilyDependencies,
    ConstraintKinds #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}

module StriDi.Layout
    (
    ) where

import Data.Kind (type Type)
import Data.Type.Equality
import Data.Proxy
import Data.List
import Data.List.Extra
import Control.Arrow ((***))
import Control.Monad.State.Strict
import Control.Monad.Writer.Class
import Control.Monad.RWS.Strict
import Control.Exception.Base (assert)
import qualified Data.Text as T
import Debug.Trace

import StriDi.TypedSeq
import StriDi.Cells

traceShowIdLbl lbl x = trace (lbl ++ ": " ++ show x) x

data Simple2Cell a =
    S2CAtom a
    | S2CId Int
    | S2CCmp (Simple2Cell a) (Simple2Cell a)
    | S2CTensor (Simple2Cell a) (Simple2Cell a)

