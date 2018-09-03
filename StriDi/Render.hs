{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, FlexibleContexts,
    RecordWildCards, AllowAmbiguousTypes, ViewPatterns, TypeFamilies, TypeFamilyDependencies #-}
module StriDi.Render
    ( draw2Cell
    , drawA2Cell
    , RenderOptions(..)
    , defaultRenderOpts
    , largeRenderOpts
    ) where

import Data.Kind (type Type)
import Data.Type.Equality
import Data.Proxy
import Data.List
import Control.Monad.State.Strict
import Control.Monad.Writer.Class
import Control.Monad.RWS.Strict
import Control.Exception.Base (assert)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)
import Text.LaTeX
import Text.LaTeX.Base.Class (comm1, LaTeXC, fromLaTeX)
import Text.LaTeX.Base.Syntax (LaTeX(..))

import StriDi.TypedSeq
import StriDi.Cells



data Point = Point Rational Rational
instance Show Point where
    show (Point x y) = "(" ++ show (approx $ realToFrac x) ++ "," ++ show (approx $ realToFrac y) ++ ")"
        where approx x = realToFrac (round (10*x)) / 10
instance Render Point where
    render = T.pack . show

y :: Point -> Rational
y (Point _ y) = y

translate :: Rational -> Rational -> Point -> Point
translate dx dy (Point x y) = Point (x+dx) (y+dy)

translateh :: Rational -> Point -> Point
translateh dx = translate dx 0

translatev :: Rational -> Point -> Point
translatev dy = translate 0 dy



ensuremath :: LaTeXC l => l -> l
ensuremath = comm1 "ensuremath"

mkLine a1 a2 p1 p2 = "\\draw " <> render p1 <> " to[out=" <> a1 <> ", in=" <> a2 <> "] " <> render p2 <> ";\n"
mkLabel p anchor label = "\\node at " <> render p <> " [anchor=" <> anchor <> "] {"
            <> render (ensuremath $ label1 label) <> "};\n"
mkNode p label = "\\node at " <> render p <> " [rectangle, draw, fill=white] {"
            <> render (ensuremath $ label2 label) <> "};\n"

data RenderOptions = RenderOptions {
    renderWidth2Cell :: Rational,
    renderLength2Cell :: Rational
}
defaultRenderOpts = RenderOptions 1 1
largeRenderOpts = RenderOptions 2 5

draw2Cell :: LaTeXC l => RenderOptions -> (f :--> g) -> l
draw2Cell opts = fromLaTeX . TeXEnv "tikzpicture" [] . raw
    . drawLO2C (Point 0 0) opts
    . layOut2Cell (renderWidth2Cell opts)
    . twoCellToCanonForm

drawA2Cell :: LaTeXC l => RenderOptions -> A2Cell -> l
drawA2Cell opts (A2Cell c) = draw2Cell opts c


-- data Rep1 where
--     RSing1 :: Rep1

-- type family UnRep1 (rep :: Rep1) (f :: a :-> b) :: (r :: Type) | r -> rep f where
--     UnRep1 RSing1 f = Sing1 f

-- class IsRep1 (rep :: Rep1) where
-- --     data UnRep1 rep :: (a :-> b) -> Type
--     singRep1 :: UnRep1 rep f -> Sing1 f
--     idRep1 :: Sing0 a -> UnRep1 rep (TId1 :: a :-> a)
--     cmpRep1 :: UnRep1 rep f -> UnRep1 rep g -> UnRep1 rep (f `Cmp1` g)

-- instance IsRep1 RSing1 where
-- --     data UnRep1 RSing1 f = URSing1 (Sing1 f)
--     singRep1 = id
--     idRep1 = Id1
--     cmpRep1 = cmp1

data TwoCellAtom (f :: a :-> b) (g :: a :-> b) where
    IdAtom :: Sing1 f -> TwoCellAtom f f
    MkAtom :: TwoCellData -> Sing1 f -> Sing1 g -> TwoCellAtom f g

data TwoCellSlice (f :: a :-> b) (g :: a :-> b) where
    EmptySlice :: Sing0 a -> TwoCellSlice (TId1 :: a :-> a) (TId1 :: a :-> a)
    ConsSlice :: TwoCellAtom (f :: a :-> b) (g :: a :-> b)
            -> TwoCellSlice h i -> TwoCellSlice (f `Cmp1` h) (g `Cmp1` i)

type TwoCellCanonForm = Interleaved TwoCellSlice Sing1


srcAtom :: TwoCellAtom f g -> Sing1 f
srcAtom (IdAtom f) = f
srcAtom (MkAtom _ f _) = f

tgtAtom :: TwoCellAtom f g -> Sing1 g
tgtAtom (IdAtom f) = f
tgtAtom (MkAtom _ _ g) = g

srcSlice :: TwoCellSlice f g -> Sing1 f
srcSlice (EmptySlice a) = Id1 a
srcSlice (ConsSlice atom q) = srcAtom atom `cmp1` srcSlice q

tgtSlice :: TwoCellSlice f g -> Sing1 g
tgtSlice (EmptySlice a) = Id1 a
tgtSlice (ConsSlice atom q) = tgtAtom atom `cmp1` tgtSlice q

singSlice :: TwoCellAtom f g -> TwoCellSlice f g
singSlice atom =
    case unit1Proof (srcAtom atom) of
      Refl -> case unit1Proof (tgtAtom atom) of
        Refl -> ConsSlice atom (EmptySlice $ tgt1 $ srcAtom atom)

idSlice :: Sing1 f -> TwoCellSlice f f
idSlice f = singSlice (IdAtom f)

tensorSlice :: TwoCellSlice f g -> TwoCellSlice h i -> TwoCellSlice (f `Cmp1` h) (g `Cmp1` i)
tensorSlice (EmptySlice _) s = s
tensorSlice (ConsSlice atom q) s2 =
    case assoc1Proof (srcAtom atom) (srcSlice q) (srcSlice s2) of
        Refl -> case assoc1Proof (tgtAtom atom) (tgtSlice q) (tgtSlice s2) of
            Refl -> ConsSlice atom $ tensorSlice q s2


tensorCanonForm :: TwoCellCanonForm f g -> TwoCellCanonForm h i -> TwoCellCanonForm (f `Cmp1` h) (g `Cmp1` i)
tensorCanonForm (NilIntl f) (NilIntl h) =
    NilIntl (f `cmp1` h)
tensorCanonForm (NilIntl f) (CmpIntl h s q) =
    CmpIntl (f `cmp1` h) (tensorSlice (idSlice f) s) (tensorCanonForm (NilIntl f) q)
tensorCanonForm (CmpIntl f s q) (NilIntl h) =
    CmpIntl (f `cmp1` h) (tensorSlice s (idSlice h)) (tensorCanonForm q (NilIntl h))
tensorCanonForm (CmpIntl f s1 q1) (CmpIntl h s2 q2) =
    CmpIntl (f `cmp1` h) (tensorSlice s1 s2) (tensorCanonForm q1 q2)


twoCellToCanonForm :: f :--> g -> TwoCellCanonForm f g
twoCellToCanonForm (Id2 f) = CmpIntl f (singSlice $ IdAtom f) $ NilIntl f
twoCellToCanonForm (Mk2 n f g) = CmpIntl f (singSlice $ MkAtom n f g) $ NilIntl g
twoCellToCanonForm (Cmp2 c1 c2) = twoCellToCanonForm c1 `mergeInterleaved` twoCellToCanonForm c2
twoCellToCanonForm (Tensor2 c1 c2) = twoCellToCanonForm c1 `tensorCanonForm` twoCellToCanonForm c2


draw2CellAtom :: RenderOptions -> Point -> TwoCellBoundary f -> TwoCellBoundary g -> TwoCellAtom f g -> Text
draw2CellAtom opts pl (unBdy -> bdyl) (unBdy -> bdyr) (IdAtom f) =
    let pr = translateh (renderLength2Cell opts) pl
     in mconcat [ mkLine "0" "180" p1 p2
        | p1 <- init $ tail $ scanl (flip translatev) pl bdyl
        | p2 <- init $ tail $ scanl (flip translatev) pr bdyr
        ]
draw2CellAtom opts pl (unBdy -> bdyl) (unBdy -> bdyr) (MkAtom label f g) =
    let pr = translateh (renderLength2Cell opts) pl
        inputs = length1 f
        outputs = length1 g

        (start, width) = case () of
            _ | inputs == 0 && outputs == 0 -> (0, sum bdyl)
            _ | inputs == 0 -> (head bdyr, sum (init $ tail bdyr))
            _  -> (head bdyl, sum (init $ tail bdyl))
        pnode = translate (renderLength2Cell opts / 2) (start + width / 2) pl

        drawnInputs = mconcat
            [ let angle = if y pnode == y p1 then "180" else if y pnode < y p1 then "90" else "-90"
               in mkLine "0" angle p1 pnode
            | p1 <- init $ tail $ scanl (flip translatev) pl bdyl ]
        drawnOutputs = mconcat
            [ let angle = if y pnode == y p2 then "0" else if y pnode < y p2 then "90" else "-90"
               in mkLine angle "180" pnode p2
            | p2 <- init $ tail $ scanl (flip translatev) pr bdyr ]
    in drawnInputs <> drawnOutputs <> mkNode pnode label

draw2CellSlice :: RenderOptions -> Point -> TwoCellBoundary f -> TwoCellBoundary g -> TwoCellSlice f g -> Text
draw2CellSlice opts p0 bdyf bdyg (EmptySlice _) = ""
draw2CellSlice opts p0 bdyf bdyg (ConsSlice atom q) = let
        (bdySrcAtom, bdySrcQ) = splitBoundaryR (srcAtom atom) (srcSlice q) bdyf
        (bdyTgtAtom, bdyTgtQ) = splitBoundaryR (tgtAtom atom) (tgtSlice q) bdyg
        addToHead x l = [x + head l] ++ tail l
        addToHeadBdy x (Bdy f bdy) = Bdy f $ addToHead x bdy
        drawnAtom = draw2CellAtom opts p0 bdySrcAtom bdyTgtAtom atom
        drawnQ = draw2CellSlice opts p0 (addToHeadBdy (sum $ unBdy bdySrcAtom) bdySrcQ) (addToHeadBdy (sum $ unBdy bdyTgtAtom) bdyTgtQ) q
    in drawnAtom <> drawnQ


data TwoCellBoundary f = Bdy {
    repBdy :: Sing1 f,
    unBdy :: [Rational]
}

defaultBoundary :: Rational -> Sing1 f -> TwoCellBoundary f
defaultBoundary baseWidth f = Bdy f $ replicate (length1 f + 1) baseWidth

splitBoundaryL :: Sing1 f -> Sing1 g -> TwoCellBoundary (f `Cmp1` g) -> (TwoCellBoundary f, TwoCellBoundary g)
splitBoundaryL f g (Bdy _ l) = let
        n = length1 f
        before = take n l
        mid = l !! n
        after = drop (n + 1) l
    in ( Bdy f (before ++ [0])
        , Bdy g ([mid] ++ after))

splitBoundaryR :: Sing1 f -> Sing1 g -> TwoCellBoundary (f `Cmp1` g) -> (TwoCellBoundary f, TwoCellBoundary g)
splitBoundaryR f g (Bdy _ l) = let
        n = length1 f
        before = take n l
        mid = l !! n
        after = drop (n + 1) l
    in ( Bdy f (before ++ [mid])
        , Bdy g ([0] ++ after))

mapBoundaryR :: Sing1 f -> Sing1 g -> (TwoCellBoundary g -> TwoCellBoundary h)
                -> TwoCellBoundary (f `Cmp1` g) -> TwoCellBoundary (f `Cmp1` h)
mapBoundaryR f g map bdy = let
    (bdyf, bdyg) = splitBoundaryL f g bdy
    in bdyf `mergeBoundary` map bdyg

mapBoundaryL :: Sing1 f -> Sing1 g -> (TwoCellBoundary f -> TwoCellBoundary h)
                -> TwoCellBoundary (f `Cmp1` g) -> TwoCellBoundary (h `Cmp1` g)
mapBoundaryL f g map bdy = let
    (bdyf, bdyg) = splitBoundaryR f g bdy
    in map bdyf `mergeBoundary` bdyg



mergeBoundary :: TwoCellBoundary f -> TwoCellBoundary g -> TwoCellBoundary (f `Cmp1` g)
mergeBoundary (Bdy f lf) (Bdy g lg) = Bdy (f `cmp1` g) (init lf ++ [last lf + head lg] ++ tail lg)

backpropBoundaryAtom :: Rational -> TwoCellAtom f g -> TwoCellBoundary g -> TwoCellBoundary f
backpropBoundaryAtom baseWidth (IdAtom _) bdy = bdy
backpropBoundaryAtom baseWidth (MkAtom _ f g) (unBdy -> bdy) = let
        inputs = length1 f
        outputs = length1 g
        outputWidth = sum bdy
        inputWidth = realToFrac (inputs + 1) * baseWidth

        addToHead x l = [x + head l] ++ tail l
        addToTail x l = init l ++ [x + last l]
        newbdy = replicate (inputs + 1) baseWidth
        -- If there is already enough space to fit the cell, spread the leftover space evenly,
        -- so that the cell remains centered wrt its outputs.
        -- we use addToHead/addToTail because bdy may have length 1
        deltaWidth = outputWidth - inputWidth
        (dhead, dtail) = if deltaWidth < 0
            then (0, 0)
            else let (x1, x2) = (head bdy, last bdy)
                  in (deltaWidth/2 + x1 - (x1 + x2) / 2 , deltaWidth/2 + x2 - (x1 + x2) / 2)
    in Bdy f $ addToHead dhead $ addToTail dtail newbdy

backpropBoundarySlice :: Rational -> TwoCellSlice f g -> TwoCellBoundary g -> TwoCellBoundary f
backpropBoundarySlice baseWidth (EmptySlice _) = id
backpropBoundarySlice baseWidth (ConsSlice atom q) =
    mapBoundaryR (srcAtom atom) (tgtSlice q) (backpropBoundarySlice baseWidth q)
    . mapBoundaryL (tgtAtom atom) (tgtSlice q) (backpropBoundaryAtom baseWidth atom)


type BdyDelta f = (Int, Rational)
type BdyDeltas f = [BdyDelta f]

propagateDeltaAtom :: TwoCellAtom f g -> BdyDelta f -> [BdyDelta g]
propagateDeltaAtom (IdAtom _) (i, delta) = [(i, delta)]
propagateDeltaAtom (MkAtom _ f g) (i, delta) = let
        inputs = length1 f
        outputs = length1 g
    in
    -- If the delta is inside the cell, spread it out evenly to keep the cell centered;
    -- otherwise, imply propagate it
    if inputs > 0 && i == 0
        then [(i, delta)]
    else if inputs > 0 && i == inputs
       then [(i - inputs + outputs, delta)]
    else [(0, delta/2), (outputs, delta/2)]

mapDelta :: Sing1 f -> Sing1 f' -> Sing1 g -> Sing1 g'
            -> (BdyDeltas f -> BdyDeltas f')
            -> (BdyDeltas g -> BdyDeltas g')
            -> BdyDeltas (f `Cmp1` g) -> BdyDeltas (f' `Cmp1` g')
mapDelta f1 f2 g1 g2 mapf mapg deltas = let
        nf1 = length1 f1
        nf2 = length1 f2
        (deltasf1, deltasg1) = partition (\(i, _) -> i <= nf1) deltas
        deltasf2 = mapf deltasf1
        deltasg2 = fmap (\(i, d) -> (i + nf2, d)) $ mapg $ fmap (\(i, d) -> (i - nf1, d)) deltasg1
    in deltasf2 ++ deltasg2

propagateDeltaSlice :: TwoCellSlice f g -> BdyDeltas f -> BdyDeltas g
propagateDeltaSlice (EmptySlice _) = id
propagateDeltaSlice (ConsSlice atom q) =
    mapDelta (srcAtom atom) (tgtAtom atom) (srcSlice q) (tgtSlice q) (propagateDeltaAtom atom =<<) (propagateDeltaSlice q)

applyDelta :: BdyDelta f -> TwoCellBoundary f -> TwoCellBoundary f
applyDelta (i, delta) (Bdy sf bdy) =
    Bdy sf $ take i bdy ++ [bdy!!i + delta] ++ drop (i+1) bdy

backpropDeltaAtom :: Rational -> TwoCellAtom f g -> TwoCellBoundary g -> [BdyDelta g]
backpropDeltaAtom baseWidth (IdAtom _) _ = []
backpropDeltaAtom baseWidth (MkAtom _ f g) (unBdy -> bdy) = let
        inputs = length1 f
        outputs = length1 g
        h = sum bdy
        newh = realToFrac (inputs+1) * baseWidth
     in if newh > h
        then [(0, (newh - h)/2), (outputs, (newh - h)/2)]
        else []

backpropDeltaSlice :: Rational -> TwoCellSlice f g -> TwoCellBoundary g -> [BdyDelta g]
backpropDeltaSlice baseWidth (EmptySlice _) _ = []
backpropDeltaSlice baseWidth (ConsSlice atom q) bdy = let
        (bdyTgtAtom, _) = splitBoundaryR (tgtAtom atom) (tgtSlice q) bdy
        (_, bdyTgtQ) = splitBoundaryL (tgtAtom atom) (tgtSlice q) bdy
        deltasAtom = backpropDeltaAtom baseWidth atom bdyTgtAtom
        deltasQ = backpropDeltaSlice baseWidth q bdyTgtQ
     in deltasAtom ++ fmap (\(i, d) -> (i + length1 (srcAtom atom), d)) deltasQ


type LayedOut2Cell = Interleaved TwoCellSlice TwoCellBoundary

layOut2Cell :: forall f g. Rational -> TwoCellCanonForm f g -> LayedOut2Cell f g
layOut2Cell baseWidth c =
    propagateDeltasLO2C baseWidth [] $
    interleaveInComposite (backpropBoundarySlice baseWidth) lastBdy $
    compositeFromInterleaved c
    where
        lastBdy :: TwoCellBoundary g
        lastBdy = defaultBoundary baseWidth $ lastInterleaved c

applyDeltas :: forall f. [BdyDelta f] -> TwoCellBoundary f -> TwoCellBoundary f
applyDeltas = flip $ foldr applyDelta

propagateAndAccumulateDeltas :: forall f g. Rational -> [BdyDelta f] -> TwoCellSlice f g -> TwoCellBoundary g -> [BdyDelta g]
propagateAndAccumulateDeltas baseWidth deltas s bdy =
    propagateDeltaSlice s deltas ++ backpropDeltaSlice baseWidth s bdy

-- Peel off the slices atom per atom
propagateDeltasLO2C :: forall f g. Rational -> BdyDeltas f -> LayedOut2Cell f g -> LayedOut2Cell f g
propagateDeltasLO2C baseWidth deltas (NilIntl bdy) = NilIntl $ applyDeltas deltas bdy
propagateDeltasLO2C baseWidth deltas (CmpIntl bdy (EmptySlice _) q) =
    propagateDeltasLO2C baseWidth deltas q
propagateDeltasLO2C baseWidth deltas (CmpIntl bdy s@(ConsSlice (MkAtom _ f _) innerq) q) =
    propagateDeltasLO2C baseWidth deltas (CmpIntl bdy (ConsSlice (IdAtom (Id1 (src1 f))) s) q)
propagateDeltasLO2C baseWidth deltas (CmpIntl bdy (ConsSlice (IdAtom _) (EmptySlice _)) q) =
    propagateDeltasLO2C baseWidth deltas q
propagateDeltasLO2C baseWidth deltas (CmpIntl bdy (ConsSlice (IdAtom f) (ConsSlice (IdAtom g) q)) outerq) =
    case assoc1Proof f g (srcSlice q) of
        Refl -> case assoc1Proof f g (tgtSlice q) of
            Refl -> propagateDeltasLO2C baseWidth deltas (CmpIntl bdy (ConsSlice (IdAtom (f `cmp1` g)) q) outerq)
propagateDeltasLO2C baseWidth deltas
    (CmpIntl bdy
      (ConsSlice (IdAtom (f :: Sing1 f1))
        (ConsSlice (atom :: TwoCellAtom f2 g2)
          (q :: TwoCellSlice f3 g3)))
      (outerq :: LayedOut2Cell f4 g4)) =
    let
        s0 = ConsSlice (IdAtom f) $ ConsSlice atom $ idSlice (srcSlice q)
        s1 = case assoc1Proof f (tgtAtom atom) (srcSlice q) of
            Refl -> case assoc1Proof f (tgtAtom atom) (tgtSlice q) of
                Refl -> ConsSlice (IdAtom (f `cmp1` tgtAtom atom)) q
        bdy0 = applyDeltas deltas bdy
        bdy1 = backpropBoundarySlice baseWidth s1 (headInterleaved outerq)
        newdeltas = propagateAndAccumulateDeltas baseWidth deltas s0 bdy1
     in CmpIntl bdy0 s0 $ propagateDeltasLO2C baseWidth newdeltas (CmpIntl bdy1 s1 outerq)


drawLO2C :: Point -> RenderOptions -> LayedOut2Cell f g -> Text
drawLO2C p0 opts c =
    let (pend, output) = (\x -> execRWS x () p0) $ sequence_
            (iterInterleaved c $ \(bdyl, atom, bdyr) -> do
                p <- get
                tell $ draw2CellSlice opts p bdyl bdyr (atom)
                put (translateh (renderLength2Cell opts) p)
            )
    in output
       <> drawBdyLabels (headInterleaved c) p0 "east"
       <> drawBdyLabels (lastInterleaved c) pend "west"
    where
        drawBdyLabels (Bdy rep bdy) p0 dir =
            T.unlines [ mkLabel p dir d
                | d <- list1Cells rep
                | p <- tail $ scanl (flip translatev) p0 bdy ]

