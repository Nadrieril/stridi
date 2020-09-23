{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, FlexibleContexts,
    RecordWildCards, AllowAmbiguousTypes, ViewPatterns, TypeFamilies, TypeFamilyDependencies,
    ConstraintKinds, TupleSections, NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}

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
import Data.List.Extra
import Data.Maybe (fromJust)
import Control.Arrow ((***), first, second)
import Control.Monad.State.Strict
import Control.Monad.Writer.Class
import Control.Monad.RWS.Strict
import Control.Monad.Fail
import Control.Exception.Base (assert)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.ByteString.Lazy.Char8   as LB
import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Unsafe.Coerce (unsafeCoerce)
import Debug.Trace
import Text.LaTeX hiding ((&))
import Text.LaTeX.Base.Class (comm1, LaTeXC, fromLaTeX)
import Text.LaTeX.Base.Syntax (LaTeX(..))
import qualified Diagrams.Prelude as Diag
import Diagrams.Prelude hiding (Render, trace, defaultBoundary, Point, render, namePoint, location)
import Diagrams.Backend.PGF.CmdLine
import Diagrams.Backend.PGF.Surface
import Diagrams.TwoD.Vector         (perp)
import Diagrams.TwoD.Size (height)
import Diagrams.Size
import System.Texrunner (runTex)
import System.Texrunner.Online (runOnlineTex, runOnlineTex', texPutStrLn)

import StriDi.TypedSeq
import StriDi.Cells

type D2 = Diagram PGF


traceShowIdLbl lbl x = trace (lbl ++ ": " ++ show x) x


data TwoCellAtom (f :: a :-> b) (g :: a :-> b) where
    IdAtom :: V1Cell f -> TwoCellAtom f f
    MkAtom :: D2Cell -> V1Cell f -> V1Cell g -> TwoCellAtom f g

srcAtom :: TwoCellAtom f g -> V1Cell f
srcAtom (IdAtom f) = f
srcAtom (MkAtom _ f _) = f

tgtAtom :: TwoCellAtom f g -> V1Cell g
tgtAtom (IdAtom f) = f
tgtAtom (MkAtom _ _ g) = g


data TwoCellUAtom where
    IdUAtom :: A1Cell -> TwoCellUAtom
    MkUAtom :: D2Cell -> A1Cell -> A1Cell -> TwoCellUAtom

srcUAtom :: TwoCellUAtom -> A1Cell
srcUAtom (IdUAtom f) = f
srcUAtom (MkUAtom _ f _) = f

tgtUAtom :: TwoCellUAtom -> A1Cell
tgtUAtom (IdUAtom f) = f
tgtUAtom (MkUAtom _ _ g) = g

untypeAtom :: TwoCellAtom f g -> TwoCellUAtom
untypeAtom (IdAtom f) = IdUAtom (A1Cell f)
untypeAtom (MkAtom d f g) = MkUAtom d (A1Cell f) (A1Cell g)


data TwoCellSlice (f :: a :-> b) (g :: a :-> b) where
    EmptySlice :: V0Cell a -> TwoCellSlice (K1Id :: a :-> a) (K1Id :: a :-> a)
    ConsSlice :: TwoCellAtom (f :: a :-> b) (g :: a :-> b)
            -> TwoCellSlice h i -> TwoCellSlice (f `K1Cmp` h) (g `K1Cmp` i)

srcSlice :: TwoCellSlice f g -> V1Cell f
srcSlice (EmptySlice a) = V1Id a
srcSlice (ConsSlice atom q) = srcAtom atom `cmp1` srcSlice q

tgtSlice :: TwoCellSlice f g -> V1Cell g
tgtSlice (EmptySlice a) = V1Id a
tgtSlice (ConsSlice atom q) = tgtAtom atom `cmp1` tgtSlice q

singSlice :: TwoCellAtom f g -> TwoCellSlice f g
singSlice atom =
    case unit1Proof (srcAtom atom) of
      Refl -> case unit1Proof (tgtAtom atom) of
        Refl -> ConsSlice atom (EmptySlice $ tgt1 $ srcAtom atom)

idSlice :: V1Cell f -> TwoCellSlice f f
idSlice f = singSlice (IdAtom f)

tensorSlice :: TwoCellSlice f g -> TwoCellSlice h i -> TwoCellSlice (f `K1Cmp` h) (g `K1Cmp` i)
tensorSlice (EmptySlice _) s = s
tensorSlice (ConsSlice atom q) s2 =
    case assoc1Proof (srcAtom atom) (srcSlice q) (srcSlice s2) of
        Refl -> case assoc1Proof (tgtAtom atom) (tgtSlice q) (tgtSlice s2) of
            Refl -> ConsSlice atom $ tensorSlice q s2


data TwoCellUSlice where
    EmptyUSlice :: A0Cell -> TwoCellUSlice
    ConsUSlice :: TwoCellUAtom -> TwoCellUSlice -> TwoCellUSlice

untypeSlice :: TwoCellSlice f g -> TwoCellUSlice
untypeSlice (EmptySlice a) = EmptyUSlice $ A0Cell a
untypeSlice (ConsSlice atom q) = ConsUSlice (untypeAtom atom) (untypeSlice q)


type TwoCellCanonForm = Interleaved TwoCellSlice V1Cell

tensorCanonForm :: TwoCellCanonForm f g -> TwoCellCanonForm h i -> TwoCellCanonForm (f `K1Cmp` h) (g `K1Cmp` i)
tensorCanonForm (NilIntl f) (NilIntl h) =
    NilIntl (f `cmp1` h)
tensorCanonForm (NilIntl f) (CmpIntl h s q) =
    CmpIntl (f `cmp1` h) (tensorSlice (idSlice f) s) (tensorCanonForm (NilIntl f) q)
tensorCanonForm (CmpIntl f s q) (NilIntl h) =
    CmpIntl (f `cmp1` h) (tensorSlice s (idSlice h)) (tensorCanonForm q (NilIntl h))
tensorCanonForm (CmpIntl f s1 q1) (CmpIntl h s2 q2) =
    CmpIntl (f `cmp1` h) (tensorSlice s1 s2) (tensorCanonForm q1 q2)

twoCellToCanonForm :: f :--> g -> TwoCellCanonForm f g
twoCellToCanonForm (V2Id f) = CmpIntl f (idSlice f) $ NilIntl f
twoCellToCanonForm (V2Atom d f g) = CmpIntl f (singSlice $ MkAtom d f g) $ NilIntl g
twoCellToCanonForm (V2Cmp c1 c2) = twoCellToCanonForm c1 `mergeInterleaved` twoCellToCanonForm c2
twoCellToCanonForm (V2Tensor c1 c2) = twoCellToCanonForm c1 `tensorCanonForm` twoCellToCanonForm c2



data RenderOptions = RenderOptions {
    renderWidth2Cell :: Double,
    renderLength2Cell :: Double
}

defaultRenderOpts = RenderOptions 1 1
largeRenderOpts = RenderOptions 2 1

type MonadLayout2Cell = MonadReader RenderOptions

askBaseWidth :: MonadReader RenderOptions m => m Double
askBaseWidth = renderWidth2Cell <$> ask

askBaseLength :: MonadReader RenderOptions m => m Double
askBaseLength = renderLength2Cell <$> ask



data TwoCellBoundary f = Bdy {
    repBdy :: V1Cell f,
    unBdy :: [Double]
}

instance Show (TwoCellBoundary f) where
    show (Bdy f bdy) =
        "TwoCellBoundary (" ++ show1CellLabel f ++ ") "
        ++ "[" ++ intercalate ", " (show <$> bdy) ++ "]"

defaultBoundary :: MonadLayout2Cell m => V1Cell f -> m (TwoCellBoundary f)
defaultBoundary f = do
    baseWidth <- askBaseWidth
    return $ Bdy f $ if length1 f == 0
        then [0]
        else [0] ++ replicate (length1 f - 1) baseWidth ++ [0]

splitBoundary' :: V1Cell f -> V1Cell g -> TwoCellBoundary (f `K1Cmp` g) -> (TwoCellBoundary f, Double, TwoCellBoundary g)
splitBoundary' f g (Bdy _ l) = let
        n = length1 f
        before = take n l
        mid = l !! n
        after = drop (n + 1) l
    in ( Bdy f (before ++ [0])
       , mid
       , Bdy g ([0] ++ after))

splitBoundary :: V1Cell f -> V1Cell g -> TwoCellBoundary (f `K1Cmp` g) -> (TwoCellBoundary f, Double, TwoCellBoundary g)
splitBoundary f g (Bdy _ l) = let
        n = length1 f
        before = take n l
        mid = l !! n
        after = drop (n + 1) l
    in ( Bdy f (before ++ [mid/2])
       , 0
       , Bdy g ([mid/2] ++ after))


data TwoCellBdyDelta f = BdyDelta {
    repDelta :: V1Cell f,
    unDelta :: [(Int, Double)]
}
type BdyDelta f = (Int, Double)

instance Show (TwoCellBdyDelta f) where
    show (BdyDelta f delta) =
        "TwoCellBdyDelta (" ++ show1CellLabel f ++ ") "
        ++ "[" ++ intercalate ", " (show <$> delta) ++ "]"

nilDelta :: V1Cell f -> TwoCellBdyDelta f
nilDelta f = BdyDelta f []

mergeDeltas :: TwoCellBdyDelta f -> TwoCellBdyDelta f -> TwoCellBdyDelta f
mergeDeltas (BdyDelta f d1) (BdyDelta _ d2) = BdyDelta f $ d1 ++ d2

tensorDeltas :: TwoCellBdyDelta f -> TwoCellBdyDelta g -> TwoCellBdyDelta (f `K1Cmp` g)
tensorDeltas (BdyDelta f deltasf) (BdyDelta g deltasg) =
    BdyDelta (f `cmp1` g) $ deltasf ++ fmap (\(i, d) -> (i + length1 f, d)) deltasg

splitDeltas :: V1Cell f -> V1Cell g -> TwoCellBdyDelta (f `K1Cmp` g) -> (TwoCellBdyDelta f, TwoCellBdyDelta g)
splitDeltas f g (unDelta -> deltas) = let
        nf = length1 f
        (deltasf, deltasg) = partition (\(i, _) -> i <= nf) deltas
    in (BdyDelta f deltasf, BdyDelta g $ fmap (\(i, d) -> (i - nf, d)) deltasg)

mapDeltas :: V1Cell f -> V1Cell g
            -> (TwoCellBdyDelta f -> TwoCellBdyDelta f')
            -> (TwoCellBdyDelta g -> TwoCellBdyDelta g')
            -> TwoCellBdyDelta (f `K1Cmp` g) -> TwoCellBdyDelta (f' `K1Cmp` g')
mapDeltas f1 g1 mapf mapg = uncurry tensorDeltas . (mapf *** mapg) . splitDeltas f1 g1

applyDeltas :: forall f. TwoCellBdyDelta f -> TwoCellBoundary f -> TwoCellBoundary f
applyDeltas (BdyDelta f1 deltas) (Bdy f2 bdy) = Bdy f2 $ foldr aux bdy deltas
    where
        aux (i, delta) bdy = take i bdy ++ [bdy!!i + delta] ++ drop (i+1) bdy

propagateDeltaAtom :: TwoCellAtom f g -> BdyDelta f -> [BdyDelta g]
propagateDeltaAtom (IdAtom _) (i, delta) = [(i, delta)]
propagateDeltaAtom (MkAtom _ f g) (i, delta) = let
        inputs = length1 f
        outputs = length1 g
    in
    -- If the delta is inside the cell, spread it out evenly to keep the cell centered;
    -- otherwise, simply propagate it
    if inputs > 0 && i == 0
        then [(i, delta)]
    else if inputs > 0 && i == inputs
       then [(i - inputs + outputs, delta)]
    else [(0, delta/2), (outputs, delta/2)]

propagateDeltasAtom :: TwoCellAtom f g -> TwoCellBdyDelta f -> TwoCellBdyDelta g
propagateDeltasAtom atom (BdyDelta _ deltas) = BdyDelta (tgtAtom atom) $ concatMap (propagateDeltaAtom atom) deltas

propagateDeltasSlice :: TwoCellSlice f g -> TwoCellBdyDelta f -> TwoCellBdyDelta g
propagateDeltasSlice (EmptySlice _) = id
propagateDeltasSlice (ConsSlice atom q) = mapDeltas (srcAtom atom) (srcSlice q) (propagateDeltasAtom atom) (propagateDeltasSlice q)


mergeBD :: MonadLayout2Cell m =>
    (TwoCellBoundary f, TwoCellBdyDelta h) ->
    Double ->
    (TwoCellBoundary g, TwoCellBdyDelta i) ->
    m (TwoCellBoundary (f `K1Cmp` g), TwoCellBdyDelta (h `K1Cmp` i))
mergeBD ((Bdy f lf), deltash) origmid ((Bdy g lg), deltasi) = do
    baseWidth <- askBaseWidth
    let midb = last lf + head lg
        origmid = baseWidth
        deltaMerge = BdyDelta (repDelta deltasi) $
            if midb >= origmid then [] else [(0, origmid - midb)]
    return ( Bdy (f `cmp1` g) (init lf ++ [midb `max` origmid] ++ tail lg)
           , deltash `tensorDeltas` (deltasi `mergeDeltas` deltaMerge))

backpropBdyAtom :: MonadLayout2Cell m => TwoCellAtom f g -> TwoCellBoundary g -> m (TwoCellBoundary f, TwoCellBdyDelta g)
backpropBdyAtom (IdAtom f) bdy = return (bdy, nilDelta f)
backpropBdyAtom (MkAtom _ f g) (unBdy -> bdy) = do
    newbdy <- defaultBoundary f
    let inputs = length1 f
        outputs = length1 g
        outputWidth = sum bdy
        inputWidth = sum $ unBdy newbdy
        deltaWidth = outputWidth - inputWidth
        (x1, x2) = (head bdy, last bdy)

    return $ if deltaWidth > 0
            -- If there is already enough space to fit the cell, spread the leftover space evenly,
            -- so that the cell remains centered wrt its outputs.
           then let srcDelta = BdyDelta f [(0, deltaWidth/2 + x1 - (x1 + x2) / 2), (inputs, deltaWidth/2 + x2 - (x1 + x2) / 2)]
                in (applyDeltas srcDelta newbdy, nilDelta g)
            -- Otherwise, make space for the cell
           else let tgtDelta = BdyDelta g [(0, abs deltaWidth/2), (outputs, abs deltaWidth/2)]
                in (newbdy, tgtDelta)

backpropBdySlice :: MonadLayout2Cell m => TwoCellSlice f g -> TwoCellBoundary g -> m (TwoCellBoundary f, TwoCellBdyDelta g)
backpropBdySlice (EmptySlice a) bdy = return (bdy, nilDelta $ V1Id a)
backpropBdySlice s@(ConsSlice atom q) bdy = do
    let (bdyAtom, mid, bdyQ) = splitBoundary (tgtAtom atom) (tgtSlice q) bdy
    bdAtom <- backpropBdyAtom atom bdyAtom
    bdQ <- backpropBdySlice q bdyQ
    mergeBD bdAtom mid bdQ



data TwoCellSliceAndDelta f g = SliceAndDelta {
    sliceSD :: TwoCellSlice f g,
    deltaSD :: TwoCellBdyDelta g
}

accumulateDeltasSD :: TwoCellBdyDelta f -> TwoCellSliceAndDelta f g -> TwoCellBdyDelta g
accumulateDeltasSD deltas sd = propagateDeltasSlice (sliceSD sd) deltas `mergeDeltas` deltaSD sd

type PartiallyLayedOut2Cell = Interleaved TwoCellSliceAndDelta TwoCellBoundary

partiallyLayOutTwoCell :: MonadLayout2Cell m => TwoCellCanonForm f g -> m (PartiallyLayedOut2Cell f g)
partiallyLayOutTwoCell (NilIntl g) = NilIntl <$> defaultBoundary g
partiallyLayOutTwoCell (CmpIntl _ s q) = do
    newq <- partiallyLayOutTwoCell q
    (newbdy, deltas) <- backpropBdySlice s (headInterleaved newq)
    return $ CmpIntl newbdy (SliceAndDelta s deltas) newq

type LayedOut2Cell = Interleaved TwoCellSlice TwoCellBoundary

propagateDeltasLO2C :: PartiallyLayedOut2Cell f g -> LayedOut2Cell f g
propagateDeltasLO2C c = let
        firstDeltas = nilDelta $ repBdy $ headInterleaved c
     in snd $ mapAccumInterleaved (\deltas sd -> (accumulateDeltasSD deltas sd, sliceSD sd)) applyDeltas firstDeltas c

layOutTwoCell :: MonadLayout2Cell m => TwoCellCanonForm f g -> m (LayedOut2Cell f g)
layOutTwoCell c = propagateDeltasLO2C <$> partiallyLayOutTwoCell c



data Point = Point Double Double

instance Show Point where
    show (Point x y) = "(" ++ show x ++ "," ++ show y ++ ")"
instance Render Point where
    render = T.pack . show

instance Num Point where
    fromInteger x = Point (fromInteger x) (fromInteger x)
    (Point x1 y1) + (Point x2 y2) = Point (x1+x2) (y1+y2)
    (Point x1 y1) - (Point x2 y2) = Point (x1-x2) (y1-y2)

y :: Point -> Double
y (Point _ y) = y

translateh :: Double -> Point -> Point
translateh dx = (Point dx 0 +)

translatev :: Double -> Point -> Point
translatev dy = (Point 0 dy +)

scalePoint :: Double -> Point -> Point
scalePoint k (Point x y) = Point (k*x) (k*y)

midPoint :: Point -> Point -> Point
midPoint p1 p2 = scalePoint (1/2) $ p1 + p2


pointsFromBdy :: TwoCellBoundary f -> Point -> [(Point, D1Cell)]
pointsFromBdy (Bdy f bdy) p0 =
    [ (p, d)
    | d <- list1Cells f
    | p <- init $ tail $ scanl (flip translatev) p0 bdy ]

data DrawableAtom = DrawableAtom {
    uatom :: TwoCellUAtom,
    location :: Point,
    leftBdy :: [(Point, D1Cell)],
    rightBdy :: [(Point, D1Cell)]
}

mkDrawableAtom :: Double -> Point -> Point -> TwoCellBoundary f -> TwoCellBoundary g -> TwoCellAtom f g -> DrawableAtom
mkDrawableAtom baseLength pl pr bdyl@(Bdy f unbdyl) bdyr@(Bdy g unbdyr) atom =
    let deltaFromBorder = Point (baseLength / 2) 0
        inputs = length1 f
        outputs = length1 g
        midpt = case () of
            _ | inputs == 0 && outputs == 0 ->
                translatev ((head unbdyl) / 2) pl
            _ | inputs == 0 ->
                midPoint
                    (translatev (head unbdyr) pr)
                    (translatev (sum $ init unbdyr) pr)
            _  ->
                midPoint
                    (translatev (head unbdyl) pl)
                    (translatev (sum $ init unbdyl) pl)
        location = midpt + deltaFromBorder
        leftBdy = pointsFromBdy bdyl (pl - midpt - deltaFromBorder)
        rightBdy = pointsFromBdy bdyr (pr - midpt + deltaFromBorder)
     in DrawableAtom { uatom = untypeAtom atom, location, leftBdy, rightBdy }

mkDrawableAtoms :: Double -> Point -> Point -> TwoCellBoundary f -> TwoCellBoundary g -> TwoCellSlice f g -> [DrawableAtom]
mkDrawableAtoms baseLength pl pr bdyf bdyg (EmptySlice _) = []
mkDrawableAtoms baseLength pl pr bdyf bdyg (ConsSlice atom q) = let
        (bdySrcAtom, midSrc, bdySrcQ) = splitBoundary' (srcAtom atom) (srcSlice q) bdyf
        (bdyTgtAtom, midTgt, bdyTgtQ) = splitBoundary' (tgtAtom atom) (tgtSlice q) bdyg
        drawableAtom = mkDrawableAtom baseLength pl pr bdySrcAtom bdyTgtAtom atom
        rest = mkDrawableAtoms
                baseLength
                (translatev (sum $ midSrc : unBdy bdySrcAtom) pl)
                (translatev (sum $ midTgt : unBdy bdyTgtAtom) pr)
                bdySrcQ bdyTgtQ q
    in drawableAtom : rest

data Drawable2Cell = Drawable2Cell {
    d2CAtoms :: [DrawableAtom],
    d2CColumns :: [[DrawableAtom]],
    d2CIntermediates :: [[(Point, D1Cell)]],
    d2CLeftBdy :: [(Point, D1Cell)],
    d2CRightBdy :: [(Point, D1Cell)]
}

mkDrawable2Cell :: Double -> LayedOut2Cell f g -> Drawable2Cell
mkDrawable2Cell baseLength c = let
        (p, columns) =
            second reverse $
            foldlInterleaved c (Point baseLength 0, []) $ \(bdyl, slice, bdyr) (p, columns) ->
                let column = mkDrawableAtoms baseLength p p bdyl bdyr slice
                 in (translateh (2*baseLength) p, column:columns)
        d2CLeftBdy = pointsFromBdy (headInterleaved c) (Point 0 0)
        d2CRightBdy = pointsFromBdy (lastInterleaved c) p
        d2CAtoms = concat columns
        d2CColumns = columns
        d2CIntermediates =
            (concatMap (\atom -> map (first (location atom +)) $ map (first (translateh (-baseLength))) $ leftBdy atom) (head columns))
            : map (concatMap (\atom -> map (first (location atom +)) $ rightBdy atom)) columns
    in Drawable2Cell { d2CAtoms, d2CColumns, d2CIntermediates, d2CLeftBdy, d2CRightBdy }

data HalfWire =
    HWStraight { hwStraightAnchor :: P2 Double }
    | HWCurved { hwCurvedOrigin :: P2 Double, hwCurvedAnchor :: V2 Double }
    deriving (Show)

data LaidOutWire = LaidOutWire {
    lowData :: D1Cell,
    lowStart :: HalfWire,
    lowEnd :: HalfWire
} deriving (Show)

type HalfWires = [HalfWire]
type MonadExtractWires m =
    ( MonadState (HalfWires, HalfWires) m
    , MonadWriter [LaidOutWire] m
    , MonadFail m
    )

extractWires :: Drawable2Cell -> [LaidOutWire]
extractWires drawable = let
        -- We go column by column and keep a running list of wires that are alive so far.
        -- In the left stack we keep incoming halfwires for this column; in the right stack
        -- we keep (in reverse order) outgoing halfwires for this column.
        popl :: MonadExtractWires m => m HalfWire
        popl = do
            -- This pattern should not fail if typechecking is correct
            (x:q, right) <- get
            put (q, right)
            return x
        pushr :: MonadExtractWires m => HalfWire -> m ()
        pushr x = modify $ second (x:)
        telllow :: MonadExtractWires m => LaidOutWire -> m ()
        telllow = tell . (:[])

        startWire :: MonadExtractWires m => HalfWire -> m ()
        startWire = pushr
        forwardWire :: MonadExtractWires m => m ()
        forwardWire = popl >>= pushr
        endWire :: MonadExtractWires m => D1Cell -> HalfWire -> m ()
        endWire lowData lowEnd = do
            lowStart <- popl
            telllow $ LaidOutWire { lowData, lowStart, lowEnd }
        nextColumn :: MonadExtractWires m => m ()
        nextColumn = do
            -- This pattern should not fail if typechecking is correct
            ([], halfwires) <- get
            put (reverse halfwires, [])

        processNode :: MonadExtractWires m => DrawableAtom -> m ()
        processNode (DrawableAtom { uatom = IdUAtom _, leftBdy }) = do
            -- Keep existing halfwires
            forM_ leftBdy $ \_ -> forwardWire
        processNode (DrawableAtom { uatom = MkUAtom celldata _ _, location, leftBdy, rightBdy }) = do
            let mkCurved dp = HWCurved {
                    hwCurvedOrigin = pointToPoint location,
                    hwCurvedAnchor = pointToVec dp
                }
            -- A bunch of incoming halfwires end here
            forM_ leftBdy $ \(dp, wire) -> do
                endWire wire $ mkCurved dp
            -- A bunch of outgoing outwires start here
            forM_ rightBdy $ \(dp, _) -> do
                startWire $ mkCurved dp
        processDrawable :: MonadExtractWires m => Drawable2Cell -> m ()
        processDrawable drawable = do
            -- First column
            forM_ (d2CLeftBdy drawable) $ \(dp, _) -> do
                startWire $ HWStraight (pointToPoint dp)

            -- Columns with nodes
            forM_ (d2CColumns drawable) $ \nodes -> do
                nextColumn
                forM_ nodes processNode

            nextColumn
            -- Last column
            forM_ (d2CRightBdy drawable) $ \(dp, wire) -> do
                endWire wire $ HWStraight (pointToPoint dp)

    in snd $ fromJust $ evalRWST (processDrawable drawable) () ([], [])

-- Draw the given text
mkLatexText :: String -> OnlineTex D2
mkLatexText [] = return mempty
mkLatexText str = do
    -- By default, tikz adds an inner padding of 1/3em to rectangles around text
    -- I measure 1em from the width of an "M"
    -- TODO: measure only once
    m :: D2 <- hboxOnline "M"
    let em = width m
        inner_sep = em/3

    txt <- hboxOnline $ "\\ensuremath{" ++ str ++ "}"
    -- Center and add inner padding
    return $ txt # centerXY # frame inner_sep

-- Draw the given text in a box
mkNodeDiag :: String -> OnlineTex D2
mkNodeDiag [] = return mempty
mkNodeDiag str = do
    txt <- mkLatexText str
    -- Draw rectangle around
    -- Default tikz line thickness is 0.4pt (called thin).
    -- Seems like I can't get line thickness small enough in `diagrams`.
    let rect = boundingRect txt # fc white # lw thin
    return $ txt <> rect

-- Moves a diagram along a trail at the given parameter, rotating it to match
-- the direction of the trail.
placeAlongTrail ::
    ( InSpace V2 (N t) t, Parametric t, Parametric (Tangent t), Codomain t (N t) ~ Diag.Point V2 (N d)
    , InSpace V2 (N d) d, OrderedField (N d), Transformable d, HasOrigin d
    ) => t -> N t -> d -> d
placeAlongTrail trail param = let
        point = trail `atParam` param
        tangent = trail `tangentAtParam` param
    in moveTo point . rotateTo (direction tangent)

pointToVec :: Point -> V2 Double
pointToVec (Point x y) = scale 30 $ r2 (x, y)

pointToPoint :: Point -> P2 Double
pointToPoint p = origin .+^ pointToVec p

strokeWire :: D1Cell -> Bool -> Bool -> [Segment Closed V2 Double] -> D2
strokeWire wire decorate reverse segments = let
        trail = trailFromSegments segments `at` origin
        trail' = if reverse then reverseLocTrail trail else trail
        -- Temporary hack
        isArrowR =
            "decoration={markings, mark=at position 0.5 with {\\arrow[line width=0.2mm]{angle 90}}}" `elem` tikzDecorations1 wire
        isArrowL =
            "decoration={markings, mark=at position 0.5 with {\\arrow[line width=0.2mm]{angle 90 reversed}}}" `elem` tikzDecorations1 wire
        decoration =
            if decorate && (isArrowR || isArrowL)
            then let
                    arrow = scale 4 $ translate (r2 (0.354, 0)) $
                            fromOffsets [r2 (1, 0) # rotate (3/8 @@ turn)]
                         <> fromOffsets [r2 (1, 0) # rotate (-3/8 @@ turn)]
                    arrow' = if isArrowL then rotate (1/2 @@ turn) arrow else arrow
                 in placeAlongTrail trail' 0.5 arrow'
            else mempty
    in decoration <> stroke trail'

type MonadLatexDiagram = RWST () D2 () OnlineTex

liftOnlineTex :: OnlineTex a -> MonadLatexDiagram a
liftOnlineTex = lift

tellDiagram :: D2 -> MonadLatexDiagram ()
tellDiagram = tell

evalMonadLatexDiagram :: MonadLatexDiagram () -> OnlineTex D2
evalMonadLatexDiagram x = do
    ((), (), diag) <- runRWST x () ()
    return diag

drawHalfWire :: MonadWriter D2 m => D1Cell -> Bool -> Bool -> HalfWire -> m (P2 Double)
drawHalfWire wire decorate reverse (HWStraight anchor) = return anchor
drawHalfWire wire decorate reverse (HWCurved origin anchor) = do
    let ctrlpt = anchor & _x .~ 0
        segment =
            if abs (view _y anchor) <= 0.01
            then straight anchor
            else bézier3 (ctrlpt/2) (anchor + (ctrlpt - anchor)/2) anchor
    tell $ moveTo origin $ strokeWire wire decorate reverse [segment]
    return $ origin .+^ anchor

drawLaidOutWire :: LaidOutWire -> MonadLatexDiagram ()
drawLaidOutWire (LaidOutWire { lowData, lowStart, lowEnd }) = do
    -- Draw the start and end of the wire
    startPoint <- drawHalfWire lowData False False lowStart
    endPoint <- drawHalfWire lowData False True lowEnd
    -- Draw the straight identity between the two
    tell $ moveTo startPoint $ strokeWire lowData True False [straight (endPoint .-. startPoint)]

draw2CellAtom :: DrawableAtom -> MonadLatexDiagram ()
draw2CellAtom (DrawableAtom { uatom = IdUAtom _ }) = return ()
draw2CellAtom (DrawableAtom { uatom = MkUAtom celldata _ _, location, leftBdy, rightBdy }) = do
    let label = T.unpack $ render $ label2 celldata
    case label of
        _ | "circle" `elem` tikzOptions2 celldata -> do
            tellDiagram $ moveTo (pointToPoint location) $ circle 1.5 # fc black
        _ -> do
            diag <- liftOnlineTex $ moveTo (pointToPoint location) <$> mkNodeDiag label
            tellDiagram diag

drawLO2CLatex :: RenderOptions -> Drawable2Cell -> MonadLatexDiagram ()
drawLO2CLatex opts drawable = do
    forM_ (d2CAtoms drawable) draw2CellAtom
    forM_ (d2CLeftBdy drawable) $ \(dp, d) -> do
        let lbl = T.unpack (render (label1 d))
        txt <- liftOnlineTex $ mkLatexText lbl
        tellDiagram $ moveTo (pointToPoint dp) $ alignXMax txt
    forM_ (d2CRightBdy drawable) $ \(dp, d) -> do
        let lbl = T.unpack (render (label1 d))
        txt <- liftOnlineTex $ mkLatexText lbl
        tellDiagram $ moveTo (pointToPoint dp) $ alignXMin txt
    forM_ (extractWires drawable) drawLaidOutWire

draw2Cell :: LaTeXC l => RenderOptions -> (f :--> g) -> l
draw2Cell opts =
    fromLaTeX . raw
    . T.decodeUtf8 . LB.toStrict . toLazyByteString
    . renderDia PGF with
    . surfOnlineTex with
    . evalMonadLatexDiagram
    . drawLO2CLatex opts
    . mkDrawable2Cell (renderLength2Cell opts)
    . flip layOutTwoCell opts
    . twoCellToCanonForm

drawA2Cell :: LaTeXC l => RenderOptions -> A2Cell -> l
drawA2Cell opts (A2Cell c) = draw2Cell opts c

