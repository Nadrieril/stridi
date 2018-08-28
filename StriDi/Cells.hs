{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, TypeApplications,
    ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, AllowAmbiguousTypes, RecordWildCards #-}
module StriDi.Cells where

import GHC.TypeLits
import Data.Promotion.Prelude.List
import Data.Monoid ((<>))
import Data.Proxy
import qualified Data.Text as T
import Data.Text (Text)
import Unsafe.Coerce (unsafeCoerce)
import Data.String (IsString(..))


type OneCell = [Symbol]
type Id1 = '[]
type Cmp1 a b = a ++ b


type Sing (f :: [Symbol]) = [Text]

data (f :: OneCell) :--> (g :: OneCell) where
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

-- id2 :: forall f. Reify1 f => f :--> f
-- id2 = Id2 (reify1 @f)

seal2Cell :: Text -> f :--> g -> f :--> g
seal2Cell s c = Labelled2 s (extractLeftRep c) (extractLeftRep (flip2Cell c))



data Identifier = AutoId Int | CustomId Text
    deriving (Eq)

instance IsString Identifier where
    fromString s = CustomId $ T.pack s


data A0Cell = A0Cell {
    identifier0 :: Identifier,
    label0 :: Text
} deriving (Eq)


data A1Atom = A1Atom {
    identifier1 :: Identifier,
    label1 :: Text,
    src1 :: A0Cell,
    tgt1 :: A0Cell
} deriving (Eq)

data A1Cell = A1Cell [A1Atom]
    deriving (Eq)


data A2Atom = A2Atom {
    identifier2 :: Identifier,
    label2 :: Text,
    src2 :: A1Cell,
    tgt2 :: A1Cell
} deriving (Eq)

data A2Cell =
    AAtom2 A2Atom
    | AId2 A1Cell
    | ACmp2 A2Cell A2Cell
    | ATensor2 A2Cell A2Cell

id2 :: A1Cell -> A2Cell
id2 = AId2

typeifyA1Cell :: A1Cell -> (forall f. Sing f -> r) -> r
typeifyA1Cell (A1Cell l) f = f (fmap label1 l)

typeifyA2Cell :: A2Cell -> (forall f g. f :--> g -> r) -> r
typeifyA2Cell (AAtom2 A2Atom{..}) f =
    typeifyA1Cell src2 $ \sf ->
    typeifyA1Cell tgt2 $ \sg ->
    f $ Labelled2 label2 sf sg
typeifyA2Cell (AId2 src) f =
    typeifyA1Cell src $ \sf ->
    f $ Id2 sf
typeifyA2Cell (ACmp2 c1 c2) f =
    typeifyA2Cell c1 $ \c1 ->
    typeifyA2Cell c2 $ \c2 ->
    f $ c1 `Cmp2` unsafeCoerce c2
typeifyA2Cell (ATensor2 c1 c2) f =
    typeifyA2Cell c1 $ \c1 ->
    typeifyA2Cell c2 $ \c2 ->
    f $ c1 `Tensor2` unsafeCoerce c2

