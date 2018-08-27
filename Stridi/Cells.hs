{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, TypeApplications,
    ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, AllowAmbiguousTypes #-}
module Stridi.Cells where

import GHC.TypeLits
import Data.Promotion.Prelude.List
import Data.Monoid ((<>))
import Data.Proxy
import qualified Data.Text as T
import Data.Text (Text)


type A1Cell = [Symbol]
type Id1 = '[]
type Cmp1 a b = a ++ b


type Sing (f :: [Symbol]) = [Text]

data (f :: A1Cell) :--> (g :: A1Cell) where
    Labelled2 :: Text -> Sing f -> Sing g -> f :--> g
    Id2 :: Sing f -> f :--> f
    Cmp2 :: (f :--> g) -> (g :--> h) -> (f :--> h)
    Tensor2 :: (f :--> g) -> (f' :--> g') -> (Cmp1 f f' :--> Cmp1 g g')

flip2Cell :: f :--> g -> g :--> f
flip2Cell (Id2 sf) = Id2 sf
flip2Cell (Labelled2 n sf sg) = Labelled2 (n <> "'") sg sf
flip2Cell (Cmp2 c1 c2) = Cmp2 (flip2Cell c2) (flip2Cell c1)
flip2Cell (Tensor2 c1 c2) = Tensor2 (flip2Cell c1) (flip2Cell c2)

extractLeftRep :: f :--> g -> Sing f
extractLeftRep (Id2 sf) = sf
extractLeftRep (Labelled2 _ sf _) = sf
extractLeftRep (Cmp2 c1 _) = extractLeftRep c1
extractLeftRep (Tensor2 c1 c2) = let
        r1 = extractLeftRep c1
        r2 = extractLeftRep c2
    in r1 ++ r2

class Reify1 (f :: [Symbol]) where
    reify1 :: Sing f
instance Reify1 '[] where
    reify1 = []
instance (KnownSymbol s, Reify1 f) => Reify1 (s ': f) where
    reify1 = T.pack (symbolVal (Proxy @s)) : reify1 @f

labelled2 :: forall f g. (Reify1 f, Reify1 g) => Text -> f :--> g
labelled2 l = Labelled2 l (reify1 @f) (reify1 @g)

id2 :: forall f. Reify1 f => f :--> f
id2 = Id2 (reify1 @f)

seal2Cell :: Text -> f :--> g -> f :--> g
seal2Cell s c = Labelled2 s (extractLeftRep c) (extractLeftRep (flip2Cell c))
