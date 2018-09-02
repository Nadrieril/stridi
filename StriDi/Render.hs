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

evalRWS' :: r -> s -> RWS r w s a -> w
evalRWS' r s rws = snd $ evalRWS rws r s



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
    . twoCellToCanonForm'

drawA2Cell :: LaTeXC l => RenderOptions -> A2Cell -> l
drawA2Cell opts (A2Cell c) = draw2Cell opts c



data TwoCellAtom (f :: a :-> b) (g :: a :-> b) = TwoCellAtom {
    before :: Int,
    after :: Int,
    inputs :: Int,
    outputs :: Int,
    inRep :: Sing1 f,
    outRep :: Sing1 g,
    label :: TwoCellData
}

type TwoCellCanonForm = Composite TwoCellAtom


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

data TwoCellAtom' (f :: a :-> b) (g :: a :-> b) where
    IdAtom :: Sing1 f -> TwoCellAtom' f f
    MkAtom :: TwoCellData -> Sing1 f -> Sing1 g -> TwoCellAtom' f g

data TwoCellSlice (f :: a :-> b) (g :: a :-> b) where
    EmptySlice :: Sing0 a -> TwoCellSlice (TId1 :: a :-> a) (TId1 :: a :-> a)
    ConsSlice :: TwoCellAtom' (f :: a :-> b) (g :: a :-> b)
            -> TwoCellSlice h i -> TwoCellSlice (f `Cmp1` h) (g `Cmp1` i)

type TwoCellCanonForm' = Interleaved TwoCellSlice Sing1


srcAtom :: TwoCellAtom f g -> Sing1 f
srcAtom = inRep

tgtAtom :: TwoCellAtom f g -> Sing1 g
tgtAtom = outRep

srcAtom' :: TwoCellAtom' f g -> Sing1 f
srcAtom' (IdAtom f) = f
srcAtom' (MkAtom _ f _) = f

tgtAtom' :: TwoCellAtom' f g -> Sing1 g
tgtAtom' (IdAtom f) = f
tgtAtom' (MkAtom _ _ g) = g

srcSlice :: TwoCellSlice f g -> Sing1 f
srcSlice (EmptySlice a) = Id1 a
srcSlice (ConsSlice atom q) = srcAtom' atom `cmp1` srcSlice q

tgtSlice :: TwoCellSlice f g -> Sing1 g
tgtSlice (EmptySlice a) = Id1 a
tgtSlice (ConsSlice atom q) = tgtAtom' atom `cmp1` tgtSlice q

singSlice :: TwoCellAtom' f g -> TwoCellSlice f g
singSlice atom =
    case unit1Proof (srcAtom' atom) of
      Refl -> case unit1Proof (tgtAtom' atom) of
        Refl -> ConsSlice atom (EmptySlice $ tgt1 $ srcAtom' atom)

idSlice :: Sing1 f -> TwoCellSlice f f
idSlice f = singSlice (IdAtom f)

tensorSlice :: TwoCellSlice f g -> TwoCellSlice h i -> TwoCellSlice (f `Cmp1` h) (g `Cmp1` i)
tensorSlice (EmptySlice _) s = s
tensorSlice (ConsSlice atom q) s2 =
    case assoc1Proof (srcAtom' atom) (srcSlice q) (srcSlice s2) of
        Refl -> case assoc1Proof (tgtAtom' atom) (tgtSlice q) (tgtSlice s2) of
            Refl -> ConsSlice atom $ tensorSlice q s2


atomPrimeToAtom :: TwoCellAtom' f g -> TwoCellAtom f g
atomPrimeToAtom (IdAtom f) = TwoCellAtom {
    before = length1 f,
    after = 0,
    inputs = 0,
    outputs = 0,
    inRep = f,
    outRep = f,
    label = TwoCellData "id"
}
atomPrimeToAtom (MkAtom d f g) = TwoCellAtom {
    before = 0,
    after = 0,
    inputs = length1 f,
    outputs = length1 g,
    inRep = f,
    outRep = g,
    label = d
}

tensorCanonForm' :: TwoCellCanonForm' f g -> TwoCellCanonForm' h i -> TwoCellCanonForm' (f `Cmp1` h) (g `Cmp1` i)
tensorCanonForm' (NilIntl f) (NilIntl h) =
    NilIntl (f `cmp1` h)
tensorCanonForm' (NilIntl f) (CmpIntl h s q) =
    CmpIntl (f `cmp1` h) (tensorSlice (idSlice f) s) (tensorCanonForm' (NilIntl f) q)
tensorCanonForm' (CmpIntl f s q) (NilIntl h) =
    CmpIntl (f `cmp1` h) (tensorSlice s (idSlice h)) (tensorCanonForm' q (NilIntl h))
tensorCanonForm' (CmpIntl f s1 q1) (CmpIntl h s2 q2) =
    CmpIntl (f `cmp1` h) (tensorSlice s1 s2) (tensorCanonForm' q1 q2)

sliceToLO2C :: Rational -> TwoCellSlice f g -> TwoCellBoundary f -> TwoCellBoundary g -> LayedOut2Cell f g
sliceToLO2C baseWidth (EmptySlice _) bdyf bdyg = NilIntl bdyf
sliceToLO2C baseWidth (ConsSlice atom q) bdyf bdyg =
    let (_, bdySrcQ) = splitBoundaryR (srcAtom' atom) (srcSlice q) bdyf
        (bdyTgtAtom, bdyTgtQ) = splitBoundaryL (tgtAtom' atom) (tgtSlice q) bdyg
        qLO2C = sliceToLO2C baseWidth q bdySrcQ bdyTgtQ
        midbdy = bdyTgtAtom `mergeBoundary` headInterleaved qLO2C
     in CmpIntl
        (mapBoundaryL (tgtAtom' atom) (srcSlice q) (backpropBoundaryAtom baseWidth atom) midbdy)
        (tensor2CellAtomR (srcSlice q) $ atomPrimeToAtom atom)
        (tensorLO2CL bdyTgtAtom qLO2C)


tensorLO2CL :: TwoCellBoundary x -> LayedOut2Cell f g -> LayedOut2Cell (x `Cmp1` f) (x `Cmp1` g)
tensorLO2CL topbdy (NilIntl bdy) = NilIntl (topbdy `mergeBoundary` bdy)
tensorLO2CL topbdy (CmpIntl bdy atom q) = CmpIntl (topbdy `mergeBoundary` bdy) (tensor2CellAtomL (repBdy topbdy) atom) $ tensorLO2CL topbdy q

twoCellToCanonForm' :: f :--> g -> TwoCellCanonForm' f g
twoCellToCanonForm' (Id2 f) = CmpIntl f (singSlice $ IdAtom f) $ NilIntl f
twoCellToCanonForm' (Mk2 n f g) = CmpIntl f (singSlice $ MkAtom n f g) $ NilIntl g
twoCellToCanonForm' (Cmp2 c1 c2) = twoCellToCanonForm' c1 `mergeInterleaved` twoCellToCanonForm' c2
twoCellToCanonForm' (Tensor2 c1 c2) = twoCellToCanonForm' c1 `tensorCanonForm'` twoCellToCanonForm' c2


tensor2CellAtomL :: forall x f g. Sing1 x -> TwoCellAtom f g -> TwoCellAtom (x `Cmp1` f) (x `Cmp1` g)
tensor2CellAtomL sx ca = ca {
        before = before ca + length1 sx,
        inRep = sx `cmp1` inRep ca,
        outRep = sx `cmp1` outRep ca
    }

tensor2CellAtomR :: forall x f g. Sing1 x -> TwoCellAtom f g -> TwoCellAtom (f `Cmp1` x) (g `Cmp1` x)
tensor2CellAtomR sx ca = ca {
        after = after ca + length1 sx,
        inRep = inRep ca `cmp1` sx,
        outRep = outRep ca `cmp1` sx
    }


draw2CellAtom :: RenderOptions -> Point -> TwoCellBoundary f -> TwoCellBoundary g -> TwoCellAtom f g -> Text
draw2CellAtom opts pl (unBdy -> bdyl) (unBdy -> bdyr) TwoCellAtom{..} =
    let pr = translateh (renderLength2Cell opts) pl
        popleft = do
            (p1, p2, bdyl, bdyr) <- get
            let p1' = translatev (head bdyl) p1
            put (p1', p2, tail bdyl, bdyr)
            return p1'
        popright = do
            (p1, p2, bdyl, bdyr) <- get
            let p2' = translatev (head bdyr) p2
            put (p1, p2', bdyl, tail bdyr)
            return p2'
    in evalRWS' () (pl, pr, bdyl, bdyr) $ do
        replicateM_ before $ do
            p1 <- popleft
            p2 <- popright
            tell $ mkLine "0" "180" p1 p2
        (p1, _, bdyl, bdyr) <- get
        let width = case () of
                _ | inputs == 0 && outputs == 0 -> head bdyl
                _ | inputs == 0 -> head bdyr + sum (take outputs bdyr)
                _  -> head bdyl + sum (take inputs bdyl)
        let p = translate ((renderLength2Cell opts) / 2) (width / 2) p1
        replicateM_ inputs $ do
            p1 <- popleft
            let angle = if y p == y p1 then "180" else if y p < y p1 then "90" else "-90"
            tell $ mkLine "0" angle p1 p
        replicateM_ outputs $ do
            p2 <- popright
            let angle = if y p == y p2 then "0" else if y p < y p2 then "90" else "-90"
            tell $ mkLine angle "180" p p2
        tell $ mkNode p label
        replicateM_ after $ do
            p1 <- popleft
            p2 <- popright
            tell $ mkLine "0" "180" p1 p2


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

backpropBoundaryAtom :: Rational -> TwoCellAtom' f g -> TwoCellBoundary g -> TwoCellBoundary f
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
backpropBoundarySlice baseWidth (EmptySlice _) bdy = bdy
backpropBoundarySlice baseWidth (ConsSlice atom q) bdy = let
        newbdy = mapBoundaryR (tgtAtom' atom) (tgtSlice q) (backpropBoundarySlice baseWidth q) bdy
     in mapBoundaryL (tgtAtom' atom) (srcSlice q) (backpropBoundaryAtom baseWidth atom) newbdy


-- withFakeRep :: Int -> (forall a b (f :: a :-> b). Sing1 f -> r) -> r
-- withFakeRep n f = let
--         a = mkA0 (ZeroCellData "a")
--         c = mkA1 (OneCellData "c") a a
--     in case foldr cmpA1 (idA1 a) $ replicate n c of
--         A1Cell rep -> f rep


type BdyDelta f = (Int, Rational)

propagateDelta :: TwoCellAtom f g -> BdyDelta f -> [BdyDelta g]
propagateDelta TwoCellAtom{..} (i, delta) =
    if (inputs == 0 && i == before) || (before < i && i < before + inputs)
       then [(before, delta/2), (before+outputs, delta/2)]
    else if i >= before + inputs
       then [(i - inputs + outputs, delta)]
    else [(i, delta)]

applyDelta :: BdyDelta f -> TwoCellBoundary f -> TwoCellBoundary f
applyDelta (i, delta) (Bdy sf bdy) =
    Bdy sf $ take i bdy ++ [bdy!!i + delta] ++ drop (i+1) bdy

backpropDelta :: Rational -> TwoCellAtom f g -> TwoCellBoundary g -> [BdyDelta g]
backpropDelta baseWidth TwoCellAtom{..} (unBdy -> bdy) = let
        h = sum $ take (outputs+1) $ drop before bdy
        newh = realToFrac (inputs+1) * baseWidth
     in if newh > h
        then [(before, (newh - h)/2), (before + outputs, (newh - h)/2)]
        else []


type LayedOut2Cell = Interleaved TwoCellAtom TwoCellBoundary

layOut2Cell :: forall f g. Rational -> TwoCellCanonForm' f g -> LayedOut2Cell f g
layOut2Cell baseWidth c = propagateDeltasLO2C [] $
    flatMapInterleaved (sliceToLO2C baseWidth) $
    interleaveInComposite (backpropBoundarySlice baseWidth) lastBdy $
    compositeFromInterleaved c
    where
        lastBdy :: TwoCellBoundary g
        lastBdy = defaultBoundary baseWidth $ lastInterleaved c

        applyDeltas :: forall f. [BdyDelta f] -> TwoCellBoundary f -> TwoCellBoundary f
        applyDeltas = flip $ foldr applyDelta

        propagateAndAccumulateDeltas :: forall f g. [BdyDelta f] -> TwoCellAtom f g -> TwoCellBoundary g -> [BdyDelta g]
        propagateAndAccumulateDeltas deltas atom bdy =
            concatMap (propagateDelta atom) deltas ++ backpropDelta baseWidth atom bdy

        propagateDeltasLO2C :: forall f g. [BdyDelta f] -> LayedOut2Cell f g -> LayedOut2Cell f g
        propagateDeltasLO2C deltas (NilIntl bdy) = NilIntl $ applyDeltas deltas bdy
        propagateDeltasLO2C deltas (CmpIntl bdy (atom :: TwoCellAtom f h) q) =
                CmpIntl newbdy atom $ propagateDeltasLO2C @h @g newdeltas q
            where
                newbdy = applyDeltas deltas bdy
                newdeltas = propagateAndAccumulateDeltas deltas atom (headInterleaved q)

drawLO2C :: Point -> RenderOptions -> LayedOut2Cell f g -> Text
drawLO2C p0 opts c =
    let (pend, output) = (\x -> execRWS x () p0) $ sequence_
            (iterInterleaved c $ \(bdyl, atom, bdyr) -> do
                p <- get
                tell $ draw2CellAtom opts p bdyl bdyr atom
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

