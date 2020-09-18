{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, TypeApplications,
    ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, AllowAmbiguousTypes, RecordWildCards, TypeFamilies #-}
module StriDi.Cells where

import GHC.TypeLits
import Data.Type.Equality
import Data.Singletons.Prelude.List
import Data.Monoid ((<>))
import Data.Proxy
import Data.List
import qualified Data.Text as T
import Data.Text (Text)
import Unsafe.Coerce (unsafeCoerce)
import Data.String (IsString(..))
import Text.LaTeX



-- Carried data
data D0Cell = D0Cell {
    label0 :: LaTeX
} deriving (Eq)

data D1Cell = D1Cell {
    label1 :: LaTeX,
    tikzOptions1 :: [Text],
    tikzDecorations1 :: [Text]
} deriving (Eq, Show)

data D2Cell = D2Cell {
    label2 :: LaTeX,
    tikzOptions2 :: [Text]
} deriving (Eq)


-- Kind-level
data K0Cell = K0Cell

data K1CellAtom (a::K0Cell) (b::K0Cell) = K1CellAtom

type a :-> b = K1Cell a b
data K1Cell (a::K0Cell) (b::K0Cell) where
    K1Id :: a :-> a
    K1Cons :: K1CellAtom a b -> b :-> c -> a :-> c

type family K1Cmp (x :: a :-> b) (y :: b :-> c) :: a :-> c where
    K1Cmp K1Id y = y
    K1Cmp (K1Cons c q) y = K1Cons c (K1Cmp q y)


-- Value-level, statically-typed
data V0Cell (a :: K0Cell) = V0Cell D0Cell

data V1Cell (f :: a :-> b) where
    V1Atom :: D1Cell -> V0Cell a -> V0Cell b -> V1Cell (f :: a :-> b)
    V1Id :: V0Cell a -> V1Cell (K1Id :: a :-> a)
    V1Cmp :: V1Cell (f :: a :-> b) -> V1Cell (g :: b :-> c) -> V1Cell (f `K1Cmp` g)

type (f :: a :-> b) :--> (g :: a :-> b) = V2Cell f g
data V2Cell (f :: a :-> b) (g :: a :-> b) where
    V2Atom :: D2Cell -> V1Cell f -> V1Cell g -> f :--> g
    V2Id :: V1Cell f -> V2Cell f f
    V2Cmp :: V2Cell f g -> V2Cell g h -> V2Cell f h
    V2Tensor :: V2Cell f g -> V2Cell f' g' -> V2Cell (K1Cmp f f') (K1Cmp g g')


instance TestEquality V0Cell where
    testEquality (V0Cell x1) (V0Cell x2) =
        if x1 == x2
           then Just $ unsafeCoerce Refl
           else Nothing

instance TestEquality V1Cell where
    testEquality c1 c2 =
        case testAligned1 c1 c2 of
            Just (Refl, Refl)
                | list1Cells c1 == list1Cells c2 -> Just $ unsafeCoerce Refl
            _ -> Nothing


unit1Proof :: V1Cell f -> (f `K1Cmp` K1Id) :~: f
unit1Proof f = unsafeCoerce Refl

assoc1Proof :: V1Cell f -> V1Cell g -> V1Cell h -> (f `K1Cmp` g) `K1Cmp` h :~: f `K1Cmp` (g `K1Cmp` h)
assoc1Proof f g h = unsafeCoerce Refl

testAligned1 :: V1Cell (f :: a :-> b) -> V1Cell (g :: c :-> d) -> Maybe (a :~: c, b :~: d)
testAligned1 c1 c2 =
    case (testEquality (src1 c1) (src1 c2), testEquality (tgt1 c1) (tgt1 c2)) of
       (Just Refl, Just Refl) -> Just (Refl, Refl)
       _ -> Nothing


cmp1 :: V1Cell f -> V1Cell g -> V1Cell (f `K1Cmp` g)
cmp1 = V1Cmp

length1 :: V1Cell f -> Int
length1 (V1Atom _ _ _) = 1
length1 (V1Id _) = 0
length1 (V1Cmp f g) = length1 f + length1 g

src1 :: V1Cell (f :: a :-> b) -> V0Cell a
src1 (V1Atom _ a _) = a
src1 (V1Id a) = a
src1 (V1Cmp f _) = src1 f

tgt1 :: V1Cell (f :: a :-> b) -> V0Cell b
tgt1 (V1Atom _ _ b) = b
tgt1 (V1Id a) = a
tgt1 (V1Cmp _ g) = tgt1 g

list1Cells :: V1Cell f -> [D1Cell]
list1Cells (V1Atom d _ _) = [d]
list1Cells (V1Id _) = []
list1Cells (V1Cmp f g) = list1Cells f ++ list1Cells g

seal1Cell :: D1Cell -> V1Cell f -> V1Cell f
seal1Cell s c = V1Atom s (src1 c) (tgt1 c)

-- flip1Cell :: V1Cell (f :: a :-> b) -> V1Cell (g :: b :-> a)
-- flip1Cell (V1Atom l a b) = V1Atom l b a
-- flip1Cell (V1Cmp f g) = V1Cmp (flip1Cell f) (flip1Cell g)


src2 :: f :--> g -> V1Cell f
src2 (V2Id sf) = sf
src2 (V2Atom _ sf _) = sf
src2 (V2Cmp c1 _) = src2 c1
src2 (V2Tensor c1 c2) = src2 c1 `V1Cmp` src2 c2

tgt2 :: f :--> g -> V1Cell g
tgt2 = src2 . flip2Cell

flip2Cell :: f :--> g -> g :--> f
flip2Cell (V2Id sf) = V2Id sf
flip2Cell (V2Atom n sf sg) = V2Atom n sg sf
flip2Cell (V2Cmp c1 c2) = V2Cmp (flip2Cell c2) (flip2Cell c1)
flip2Cell (V2Tensor c1 c2) = V2Tensor (flip2Cell c1) (flip2Cell c2)

seal2Cell :: D2Cell -> f :--> g -> f :--> g
seal2Cell s c = V2Atom s (src2 c) (tgt2 c)



-- Value-level, dynamically-typed
data A0Cell where
    A0Cell :: V0Cell a -> A0Cell

data A1Cell where
    A1Cell :: V1Cell f -> A1Cell

data A2Cell where
    A2Cell :: V2Cell f g -> A2Cell


mkA0 :: D0Cell -> A0Cell
mkA0 s = A0Cell $ V0Cell s


mkA1 :: D1Cell -> A0Cell -> A0Cell -> A1Cell
mkA1 d (A0Cell a) (A0Cell b) = A1Cell $ V1Atom d a b

idA1 :: A0Cell -> A1Cell
idA1 (A0Cell a) = A1Cell $ V1Id a

srcA1 :: A1Cell -> A0Cell
srcA1 (A1Cell c) = A0Cell $ src1 c

tgtA1 :: A1Cell -> A0Cell
tgtA1 (A1Cell c) = A0Cell $ tgt1 c

cmpA1 :: A1Cell -> A1Cell -> A1Cell
cmpA1 (A1Cell c1) (A1Cell c2) =
    case testAligned1 c1 c2 of
        Just (Refl, Refl) -> case testEquality (tgt1 c1) (src1 c2) of
            Just Refl -> A1Cell $ V1Cmp c1 c2
            _ -> error "Type error in cmpA1"
        _ -> error "Type error in cmpA1"


mkA2 :: D2Cell -> A1Cell -> A1Cell -> A2Cell
mkA2 s (A1Cell f) (A1Cell g) =
    case testAligned1 f g of
        Just (Refl, Refl) -> A2Cell $ V2Atom s f g
        Nothing -> error $ "Type error in mkA2 " ++ show (label2 s)

idA2 :: A1Cell -> A2Cell
idA2 (A1Cell f) = A2Cell $ V2Id f

srcA2 :: A2Cell -> A1Cell
srcA2 (A2Cell c) = A1Cell $ src2 c

tgtA2 :: A2Cell -> A1Cell
tgtA2 (A2Cell c) = A1Cell $ tgt2 c

cmpA2 :: A2Cell -> A2Cell -> A2Cell
cmpA2 (A2Cell c1) (A2Cell c2) =
    case testAligned1 (tgt2 c1) (src2 c2) of
        Just (Refl, Refl) -> case testEquality (tgt2 c1) (src2 c2) of
            Just Refl -> A2Cell (c1 `V2Cmp` c2)
            Nothing -> error $ "Type error in cmpA2: cannot match "
                               ++ show (show1CellLabel $ tgt2 c1) ++ " and " ++ show (show1CellLabel $ src2 c2)
        Nothing -> error $ "Type error in cmpA2: cannot match types of "
                            ++ show (show1CellLabel $ tgt2 c1) ++ " and " ++ show (show1CellLabel $ src2 c2)

tensorA2 :: A2Cell -> A2Cell -> A2Cell
tensorA2 (A2Cell c1) (A2Cell c2) =
    case testEquality (tgt1 $ src2 c1) (src1 $ src2 c2) of
        Just Refl -> A2Cell (c1 `V2Tensor` c2)
        Nothing -> error "Type error in tensorA2"

lengthA1 :: A1Cell -> Int
lengthA1 (A1Cell c) = length1 c

show1CellLabel :: V1Cell f -> String
show1CellLabel c = intercalate (" . ") $ fmap (show . label1) $ list1Cells c

latex1CellLabel :: V1Cell f -> LaTeX
latex1CellLabel c = mconcat $ intersperse (raw " \\circ ") $ fmap label1 $ list1Cells c
