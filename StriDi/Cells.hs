{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, TypeApplications,
    ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, AllowAmbiguousTypes, RecordWildCards, TypeFamilies #-}
module StriDi.Cells where

import GHC.TypeLits
import Data.Type.Equality
import Data.Promotion.Prelude.List
import Data.Monoid ((<>))
import Data.Proxy
import qualified Data.Text as T
import Data.Text (Text)
import Unsafe.Coerce (unsafeCoerce)
import Data.String (IsString(..))
import Text.LaTeX



data ZeroCellData = ZeroCellData {
    label0 :: LaTeX
} deriving (Eq)

data OneCellData = OneCellData {
    label1 :: LaTeX
} deriving (Eq, Show)

data TwoCellData = TwoCellData {
    label2 :: LaTeX
} deriving (Eq)


-- Type-level
data ZeroCell = ZeroCell

data OneCell (a::ZeroCell) (b::ZeroCell) = OneCell

data (a::ZeroCell) :-> (b::ZeroCell) where
    TId1 :: a :-> a
    TCons1 :: OneCell a b -> b :-> c -> a :-> c

type family Cmp1 (x :: a :-> b) (y :: b :-> c) :: a :-> c where
    Cmp1 TId1 y = y
    Cmp1 (TCons1 c q) y = TCons1 c (Cmp1 q y)

unit1Proof :: Sing1 f -> (f `Cmp1` TId1) :~: f
unit1Proof f = unsafeCoerce Refl

assoc1Proof :: Sing1 f -> Sing1 g -> Sing1 h -> (f `Cmp1` g) `Cmp1` h :~: f `Cmp1` (g `Cmp1` h)
assoc1Proof f g h = unsafeCoerce Refl


-- Statically-typed
data Sing0 (a :: ZeroCell) = Sing0 ZeroCellData

data Sing1 (f :: a :-> b) where
    Mk1 :: OneCellData -> Sing0 a -> Sing0 b -> Sing1 (f :: a :-> b)
    Id1 :: Sing0 a -> Sing1 (TId1 :: a :-> a)
    Cmp1 :: Sing1 (f :: a :-> b) -> Sing1 (g :: b :-> c) -> Sing1 (f `Cmp1` g)

data (f :: a :-> b) :--> (g :: a :-> b) where
    Mk2 :: TwoCellData -> Sing1 f -> Sing1 g -> f :--> g
    Id2 :: Sing1 f -> f :--> f
    Cmp2 :: (f :--> g) -> (g :--> h) -> (f :--> h)
    Tensor2 :: (f :--> g) -> (f' :--> g') -> (Cmp1 f f' :--> Cmp1 g g')


instance TestEquality Sing0 where
    testEquality (Sing0 x1) (Sing0 x2) =
        if x1 == x2
           then Just $ unsafeCoerce Refl
           else Nothing

instance TestEquality Sing1 where
    testEquality c1 c2 =
        case testAligned1 c1 c2 of
            Just (Refl, Refl)
                | list1Cells c1 == list1Cells c2 -> Just $ unsafeCoerce Refl
            _ -> Nothing

testAligned1 :: Sing1 (f :: a :-> b) -> Sing1 (g :: c :-> d) -> Maybe (a :~: c, b :~: d)
testAligned1 c1 c2 =
    case (testEquality (src1 c1) (src1 c2), testEquality (tgt1 c1) (tgt1 c2)) of
       (Just Refl, Just Refl) -> Just (Refl, Refl)
       _ -> Nothing


cmp1 :: Sing1 f -> Sing1 g -> Sing1 (f `Cmp1` g)
cmp1 = Cmp1

length1 :: Sing1 f -> Int
length1 (Mk1 _ _ _) = 1
length1 (Id1 _) = 0
length1 (Cmp1 f g) = length1 f + length1 g

src1 :: Sing1 (f :: a :-> b) -> Sing0 a
src1 (Mk1 _ a _) = a
src1 (Id1 a) = a
src1 (Cmp1 f _) = src1 f

tgt1 :: Sing1 (f :: a :-> b) -> Sing0 b
tgt1 (Mk1 _ _ b) = b
tgt1 (Id1 a) = a
tgt1 (Cmp1 _ g) = tgt1 g

list1Cells :: Sing1 f -> [OneCellData]
list1Cells (Mk1 d _ _) = [d]
list1Cells (Id1 _) = []
list1Cells (Cmp1 f g) = list1Cells f ++ list1Cells g

-- flip1Cell :: Sing1 (f :: a :-> b) -> Sing1 (g :: b :-> a)
-- flip1Cell (Mk1 l a b) = Mk1 l b a
-- flip1Cell (Cmp1 f g) = Cmp1 (flip1Cell f) (flip1Cell g)


src2 :: f :--> g -> Sing1 f
src2 (Id2 sf) = sf
src2 (Mk2 _ sf _) = sf
src2 (Cmp2 c1 _) = src2 c1
src2 (Tensor2 c1 c2) = src2 c1 `Cmp1` src2 c2

tgt2 :: f :--> g -> Sing1 g
tgt2 = src2 . flip2Cell

flip2Cell :: f :--> g -> g :--> f
flip2Cell (Id2 sf) = Id2 sf
flip2Cell (Mk2 n sf sg) = Mk2 n sg sf
flip2Cell (Cmp2 c1 c2) = Cmp2 (flip2Cell c2) (flip2Cell c1)
flip2Cell (Tensor2 c1 c2) = Tensor2 (flip2Cell c1) (flip2Cell c2)

seal2Cell :: TwoCellData -> f :--> g -> f :--> g
seal2Cell s c = Mk2 s (src2 c) (tgt2 c)



-- Dynamically-typed
data A0Cell where
    A0Cell :: Sing0 a -> A0Cell

data A1Cell where
    A1Cell :: Sing1 f -> A1Cell

data A2Cell where
    A2Cell :: f :--> g -> A2Cell


mkA0 :: ZeroCellData -> A0Cell
mkA0 s = A0Cell $ Sing0 s


mkA1 :: OneCellData -> A0Cell -> A0Cell -> A1Cell
mkA1 d (A0Cell a) (A0Cell b) = A1Cell $ Mk1 d a b

idA1 :: A0Cell -> A1Cell
idA1 (A0Cell a) = A1Cell $ Id1 a

srcA1 :: A1Cell -> A0Cell
srcA1 (A1Cell c) = A0Cell $ src1 c

tgtA1 :: A1Cell -> A0Cell
tgtA1 (A1Cell c) = A0Cell $ tgt1 c

cmpA1 :: A1Cell -> A1Cell -> A1Cell
cmpA1 (A1Cell c1) (A1Cell c2) =
    case testAligned1 c1 c2 of
        Just (Refl, Refl) -> case testEquality (tgt1 c1) (src1 c2) of
            Just Refl -> A1Cell $ Cmp1 c1 c2
            _ -> error "Type error in cmpA1"
        _ -> error "Type error in cmpA1"


mkA2 :: TwoCellData -> A1Cell -> A1Cell -> A2Cell
mkA2 s (A1Cell f) (A1Cell g) =
    case testAligned1 f g of
        Just (Refl, Refl) -> A2Cell $ Mk2 s f g
        Nothing -> error $ "Type error in mkA2 " ++ show (label2 s)

idA2 :: A1Cell -> A2Cell
idA2 (A1Cell f) = A2Cell $ Id2 f

srcA2 :: A2Cell -> A1Cell
srcA2 (A2Cell c) = A1Cell $ src2 c

tgtA2 :: A2Cell -> A1Cell
tgtA2 (A2Cell c) = A1Cell $ tgt2 c

cmpA2 :: A2Cell -> A2Cell -> A2Cell
cmpA2 (A2Cell c1) (A2Cell c2) =
    case testAligned1 (tgt2 c1) (src2 c2) of
        Just (Refl, Refl) -> case testEquality (tgt2 c1) (src2 c2) of
            Just Refl -> A2Cell (c1 `Cmp2` c2)
            Nothing -> error $ "Type error in cmpA2: cannot match "
                               ++ show (list1Cells $ tgt2 c1) ++ " and " ++ show (list1Cells $ src2 c2)
        Nothing -> error $ "Type error in cmpA2: cannot match types of "
                            ++ show (list1Cells $ tgt2 c1) ++ " and " ++ show (list1Cells $ src2 c2)

tensorA2 :: A2Cell -> A2Cell -> A2Cell
tensorA2 (A2Cell c1) (A2Cell c2) =
    case testEquality (tgt1 $ src2 c1) (src1 $ src2 c2) of
        Just Refl -> A2Cell (c1 `Tensor2` c2)
        Nothing -> error "Type error in tensorA2"

