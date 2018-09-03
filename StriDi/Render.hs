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
import Control.Arrow ((***))
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


data TwoCellBdyDelta f = BdyDelta {
    deltaRep :: Sing1 f,
    unDelta :: [(Int, Rational)]
}
type BdyDelta f = (Int, Rational)

nilDelta :: Sing1 f -> TwoCellBdyDelta f
nilDelta f = BdyDelta f []

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

mergeDeltas :: TwoCellBdyDelta f -> TwoCellBdyDelta f -> TwoCellBdyDelta f
mergeDeltas (BdyDelta f d1) (BdyDelta _ d2) = BdyDelta f $ d1 ++ d2

concatDeltas :: Sing1 f -> [TwoCellBdyDelta f] -> TwoCellBdyDelta f
concatDeltas f = foldr mergeDeltas (nilDelta f)

tensorDeltas :: TwoCellBdyDelta f -> TwoCellBdyDelta g -> TwoCellBdyDelta (f `Cmp1` g)
tensorDeltas (BdyDelta f deltasf) (BdyDelta g deltasg) =
    BdyDelta (f `cmp1` g) $ deltasf ++ fmap (\(i, d) -> (i + length1 f, d)) deltasg

splitDeltas :: Sing1 f -> Sing1 g -> TwoCellBdyDelta (f `Cmp1` g) -> (TwoCellBdyDelta f, TwoCellBdyDelta g)
splitDeltas f g (unDelta -> deltas) = let
        nf = length1 f
        (deltasf, deltasg) = partition (\(i, _) -> i <= nf) deltas
    in (BdyDelta f deltasf, BdyDelta g $ fmap (\(i, d) -> (i - nf, d)) deltasg)

mapDeltas :: Sing1 f -> Sing1 f' -> Sing1 g -> Sing1 g'
            -> (TwoCellBdyDelta f -> TwoCellBdyDelta f')
            -> (TwoCellBdyDelta g -> TwoCellBdyDelta g')
            -> TwoCellBdyDelta (f `Cmp1` g) -> TwoCellBdyDelta (f' `Cmp1` g')
mapDeltas f1 f2 g1 g2 mapf mapg = uncurry tensorDeltas . (mapf *** mapg) . splitDeltas f1 g1

propagateDeltaSlice :: TwoCellSlice f g -> TwoCellBdyDelta f -> TwoCellBdyDelta g
propagateDeltaSlice (EmptySlice _) = id
propagateDeltaSlice (ConsSlice atom q) =
    mapDeltas (srcAtom atom) (tgtAtom atom) (srcSlice q) (tgtSlice q)
        (BdyDelta (tgtAtom atom) . concatMap (propagateDeltaAtom atom) . unDelta)
        (propagateDeltaSlice q)

generateDeltaAtom :: Rational -> TwoCellAtom f g -> TwoCellBoundary g -> TwoCellBdyDelta g
generateDeltaAtom baseWidth (IdAtom f) _ = nilDelta f
generateDeltaAtom baseWidth (MkAtom _ f g) (unBdy -> bdy) = let
        inputs = length1 f
        outputs = length1 g
        h = sum bdy
        newh = realToFrac (inputs+1) * baseWidth
     in BdyDelta g $ if newh > h
            then [(0, (newh - h)/2), (outputs, (newh - h)/2)]
            else []

generateDeltaSlice :: forall f g. Rational -> TwoCellSlice f g -> TwoCellBoundary g -> TwoCellBdyDelta g
generateDeltaSlice baseWidth s bdy = snd (aux s bdy)
    where
        aux :: forall f g. TwoCellSlice f g -> TwoCellBoundary g -> (TwoCellBoundary f, TwoCellBdyDelta g)
        aux (EmptySlice a) bdy = (bdy, nilDelta $ Id1 a)
        aux s@(ConsSlice atom q) bdy =
            let (bdyTgtAtom, bdyTgtQ) = splitBoundaryL (tgtAtom atom) (tgtSlice q) bdy
                (bdySrcQ, deltasQ) = aux q bdyTgtQ
                midbdy = bdyTgtAtom `mergeBoundary` bdySrcQ
                (bdyTgtAtom2, bdySrcQ2) = splitBoundaryR (tgtAtom atom) (srcSlice q) midbdy
                deltasAtom = generateDeltaAtom baseWidth atom bdyTgtAtom2
             in ( backpropBoundaryAtom baseWidth atom bdyTgtAtom2 `mergeBoundary` bdySrcQ2
                , tensorDeltas deltasAtom deltasQ)


type LayedOut2Cell = Interleaved TwoCellSlice TwoCellBoundary

layOut2Cell :: forall f g. Rational -> TwoCellCanonForm f g -> LayedOut2Cell f g
layOut2Cell baseWidth c =
    propagateDeltasLO2C baseWidth (nilDelta $ headInterleaved c) $
    interleaveInComposite (backpropBoundarySlice baseWidth) lastBdy $
    compositeFromInterleaved c
    where
        lastBdy :: TwoCellBoundary g
        lastBdy = defaultBoundary baseWidth $ lastInterleaved c


applyDeltas :: forall f. TwoCellBdyDelta f -> TwoCellBoundary f -> TwoCellBoundary f
applyDeltas (BdyDelta f1 deltas) (Bdy f2 bdy) = Bdy f2 $ foldr aux bdy deltas
    where
        aux (i, delta) bdy = take i bdy ++ [bdy!!i + delta] ++ drop (i+1) bdy

propagateAndAccumulateDeltas :: forall f g. Rational -> TwoCellBdyDelta f -> TwoCellSlice f g -> TwoCellBoundary g -> TwoCellBdyDelta g
propagateAndAccumulateDeltas baseWidth deltas s bdyg =
    propagateDeltaSlice s deltas `mergeDeltas` generateDeltaSlice baseWidth s bdyg

propagateDeltasLO2C :: forall f g. Rational -> TwoCellBdyDelta f -> LayedOut2Cell f g -> LayedOut2Cell f g
propagateDeltasLO2C baseWidth deltas (NilIntl bdy) = NilIntl $ applyDeltas deltas bdy
propagateDeltasLO2C baseWidth deltas (CmpIntl bdy s q) = let
        newdeltas = propagateAndAccumulateDeltas baseWidth deltas s (headInterleaved q)
        newbdy = applyDeltas deltas bdy
     in CmpIntl newbdy s $ propagateDeltasLO2C baseWidth newdeltas q


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

