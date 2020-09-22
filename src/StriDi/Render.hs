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
import Control.Arrow ((***), first, second)
import Control.Monad.State.Strict
import Control.Monad.Writer.Class
import Control.Monad.RWS.Strict
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

approx :: Rational -> Double
approx x = realToFrac (round (100 * realToFrac x)) / 100


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
    renderWidth2Cell :: Rational,
    renderLength2Cell :: Rational
}

defaultRenderOpts = RenderOptions 1 1
largeRenderOpts = RenderOptions 2 1

type MonadLayout2Cell = MonadReader RenderOptions

askBaseWidth :: MonadReader RenderOptions m => m Rational
askBaseWidth = renderWidth2Cell <$> ask

askBaseLength :: MonadReader RenderOptions m => m Rational
askBaseLength = renderLength2Cell <$> ask



data TwoCellBoundary f = Bdy {
    repBdy :: V1Cell f,
    unBdy :: [Rational]
}

instance Show (TwoCellBoundary f) where
    show (Bdy f bdy) =
        "TwoCellBoundary (" ++ show1CellLabel f ++ ") "
        ++ "[" ++ intercalate ", " (show . approx <$> bdy) ++ "]"

defaultBoundary :: MonadLayout2Cell m => V1Cell f -> m (TwoCellBoundary f)
defaultBoundary f = do
    baseWidth <- askBaseWidth
    return $ Bdy f $ if length1 f == 0
        then [0]
        else [0] ++ replicate (length1 f - 1) baseWidth ++ [0]

splitBoundary' :: V1Cell f -> V1Cell g -> TwoCellBoundary (f `K1Cmp` g) -> (TwoCellBoundary f, Rational, TwoCellBoundary g)
splitBoundary' f g (Bdy _ l) = let
        n = length1 f
        before = take n l
        mid = l !! n
        after = drop (n + 1) l
    in ( Bdy f (before ++ [0])
       , mid
       , Bdy g ([0] ++ after))

splitBoundary :: V1Cell f -> V1Cell g -> TwoCellBoundary (f `K1Cmp` g) -> (TwoCellBoundary f, Rational, TwoCellBoundary g)
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
    unDelta :: [(Int, Rational)]
}
type BdyDelta f = (Int, Rational)

instance Show (TwoCellBdyDelta f) where
    show (BdyDelta f delta) =
        "TwoCellBdyDelta (" ++ show1CellLabel f ++ ") "
        ++ "[" ++ intercalate ", " (show . (fmap approx) <$> delta) ++ "]"

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
    Rational ->
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



data Point = Point Rational Rational

instance Show Point where
    show (Point x y) = "(" ++ show (approx x) ++ "," ++ show (approx y) ++ ")"
instance Render Point where
    render = T.pack . show

instance Num Point where
    fromInteger x = Point (fromInteger x) (fromInteger x)
    (Point x1 y1) + (Point x2 y2) = Point (x1+x2) (y1+y2)
    (Point x1 y1) - (Point x2 y2) = Point (x1-x2) (y1-y2)

y :: Point -> Rational
y (Point _ y) = y

translateh :: Rational -> Point -> Point
translateh dx = (Point dx 0 +)

translatev :: Rational -> Point -> Point
translatev dy = (Point 0 dy +)

scalePoint :: Rational -> Point -> Point
scalePoint k (Point x y) = Point (k*x) (k*y)

midPoint :: Point -> Point -> Point
midPoint p1 p2 = scalePoint (1/2) $ p1 + p2



type MonadDraw2Cell m = (MonadReader RenderOptions m, MonadWriter (Text, Text) m, MonadState Int m)

ensuremath :: LaTeXC l => l -> l
ensuremath = comm1 "ensuremath"

mkLine decorate d a1 a2 p1 p2 =
    "\\draw[" <> T.intercalate ", " (tikzOptions1 d ++ if decorate then tikzDecorations1 d else []) <> "] "
    <> render p1
    <> " to[out=" <> a1 <> ", in=" <> a2 <> "] "
    <> render p2
    <> ";\n"
mkLabel p anchor d =
    "\\node at " <> render p
    <> " [anchor=" <> anchor <> "] {"
    <> render (ensuremath $ label1 d)
    <> "};\n"
mkNode p d name =
    "\\node at " <> render p
    <> " [" <> T.intercalate ", " (tikzOptions2 d) <> "] "
    <> name
    <> " {" <> render (ensuremath $ label2 d) <> "};\n"

drawInMatrix :: MonadDraw2Cell m => Text -> m ()
drawInMatrix t = tell (t, "")
drawOutMatrix :: MonadDraw2Cell m => Text -> m ()
drawOutMatrix t = tell ("", t)

newName :: MonadDraw2Cell m => m Text
newName = do
    (i :: Int) <- get
    modify (+1)
    return $ "n" <> T.pack (show i)

-- A named tikz node along with onecell data, used for drawing wires
-- This is important to refer to points from other columns.
data NamedNode = NamedNode {
    nodeName :: Text,
    nodeLocation :: Point,
    node1CData :: D1Cell
}

instance Show NamedNode where
    show = T.unpack . render

instance Render NamedNode where
    render n = "(" <> nodeName n <> ")"

namePoint :: MonadDraw2Cell m => D1Cell -> Point -> m NamedNode
namePoint d p = do
    name <- newName
    drawInMatrix $ "\\path " <> render p <> " node[coordinate] (" <> name <> ") {};\n"
    return $ NamedNode name p d

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

mkDrawableAtom :: Rational -> Point -> Point -> TwoCellBoundary f -> TwoCellBoundary g -> TwoCellAtom f g -> DrawableAtom
mkDrawableAtom baseLength pl pr bdyl@(Bdy f unbdyl) bdyr@(Bdy g unbdyr) atom =
    let deltaFromBorder = Point (baseLength / 2) 0
        inputs = length1 f
        outputs = length1 g
        location = case () of
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
        leftBdy = pointsFromBdy bdyl (pl - location - deltaFromBorder)
        rightBdy = pointsFromBdy bdyr (pr - location + deltaFromBorder)
     in DrawableAtom { uatom = untypeAtom atom, location, leftBdy, rightBdy }

mkDrawableAtoms :: Rational -> Point -> Point -> TwoCellBoundary f -> TwoCellBoundary g -> TwoCellSlice f g -> [DrawableAtom]
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
    d2CAtoms :: [[DrawableAtom]],
    d2CLeftBdy :: [(Point, D1Cell)],
    d2CRightBdy :: [(Point, D1Cell)]
}

mkDrawable2Cell :: Rational -> LayedOut2Cell f g -> Drawable2Cell
mkDrawable2Cell baseLength c = let
        (p, d2CAtoms) =
            second reverse $ -- Note to self: this is very fun to comment out with the old tikz renderer. It gets very wobbly.
            foldlInterleaved c (Point baseLength 0, []) $ \(bdyl, slice, bdyr) (p, columns) ->
                let column = mkDrawableAtoms baseLength p p bdyl bdyr slice
                 in (translateh (2*baseLength) p, column:columns)
        d2CLeftBdy = pointsFromBdy (headInterleaved c) (Point 0 0)
        d2CRightBdy = pointsFromBdy (lastInterleaved c) p
    in Drawable2Cell { d2CAtoms, d2CLeftBdy, d2CRightBdy }

draw2CellAtom :: MonadDraw2Cell m => DrawableAtom -> [NamedNode] -> m [NamedNode]
draw2CellAtom (DrawableAtom { uatom = IdUAtom _ }) inputNodes = return inputNodes
draw2CellAtom (DrawableAtom { uatom = MkUAtom celldata _ _, location, leftBdy, rightBdy }) inputNodes = do
    nodeName <- newName
    -- Draw input and output wires, naming the nodes to be able to link them across matrix cell boundaries
    pointsLeft <- forM leftBdy $ \(dp, d) -> do
        let angle = if abs (y dp) <= 0.01 then "180" else if y dp > 0 then "up" else "down"
        let p' = location + dp
        drawInMatrix $ mkLine False d "0" angle p' location
        namePoint d p'
    pointsRight <- forM rightBdy $ \(dp, d) -> do
        let angle = if abs (y dp) <= 0.01 then "0" else if y dp > 0 then "up" else "down"
        let p' = location + dp
        drawInMatrix $ mkLine False d angle "180" location p'
        namePoint d p'

    -- Draw the node
    drawInMatrix $ mkNode location celldata ("(" <> nodeName <> ")")

    -- Link with previously drawn cells
    forM_ (zip inputNodes pointsLeft) $ \(pl, pr) ->
        drawOutMatrix $ mkLine True (node1CData pl) "0" "180" pl pr

    return pointsRight

splitNodeList :: [DrawableAtom] -> [NamedNode] -> [(DrawableAtom, [NamedNode])]
splitNodeList [] _ = []
splitNodeList (atom:q) inputNodes =
    let (inputNodesAtom, inputNodesQ) = splitAt (lengthA1 $ srcUAtom $ uatom atom) inputNodes
     in (atom, inputNodesAtom) : splitNodeList q inputNodesQ

draw2CellSlice :: MonadDraw2Cell m => [DrawableAtom] -> [NamedNode] -> m [NamedNode]
draw2CellSlice atoms inputNodes =
    concat <$> forM (splitNodeList atoms inputNodes) (uncurry draw2CellAtom)

drawLO2C :: RenderOptions -> Drawable2Cell -> Text
drawLO2C opts drawable = (\(inm, outm) -> inm <> outm) $ snd $ (\x -> evalRWS x opts 0) $ do
    baseLength <- askBaseLength
    let p0 = Point 0 0
        deltaFromBorder = Point (baseLength / 2) 0

    drawInMatrix $ "\\matrix[column sep=3mm]{"

    pointsLeft <- forM (d2CLeftBdy drawable) $ \(p, d) -> do
        let p' = p - deltaFromBorder
        drawInMatrix $ mkLabel p' "east" d
        drawInMatrix $ mkLine False d "0" "180" p' p
        namePoint d p
    drawInMatrix $ "&\n"

    pts2Cell <- foldM (\nodes atoms -> do
            draw2CellSlice atoms nodes <* drawInMatrix "&\n"
        ) pointsLeft (d2CAtoms drawable)

    pointsRight <- forM (d2CRightBdy drawable) $ \(p, d) -> do
        let p' = p + deltaFromBorder
        drawInMatrix $ mkLabel p' "west" d
        drawInMatrix $ mkLine False d "0" "180" p p'
        namePoint d p

    drawInMatrix $ "\\\\};"

    forM_ (zip pts2Cell pointsRight) $ \(pl, pr) ->
        drawOutMatrix $ mkLine True (node1CData pl) "0" "180" pl pr



-- Draw the given text in a box
mkNodeDiag :: String -> OnlineTex D2
mkNodeDiag [] = return mempty
mkNodeDiag str = do
    -- By default, tikz adds an inner padding of 1/3em to rectangles around text
    -- I measure 1em from the width of an "M"
    -- TODO: measure only once
    m :: D2 <- hboxOnline "M"
    let em = width m
        inner_sep = em/3

    txt <- hboxOnline $ "\\ensuremath{" ++ str ++ "}"
    -- Center and add inner padding
    txt <- return $ txt # centerXY # frame inner_sep
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
pointToVec (Point x y) = scale 30 $ r2 (approx x, approx y)

strokeWire :: D1Cell -> Bool -> Bool -> [Segment Closed V2 Double] -> D2
strokeWire wire decorate reverse segments = let
        trail = trailFromSegments segments `at` origin
        -- Temporary hack
        isArrowR =
            "decoration={markings, mark=at position 0.5 with {\\arrow[line width=0.2mm]{angle 90}}}" `elem` tikzDecorations1 wire
        isArrowL =
            "decoration={markings, mark=at position 0.5 with {\\arrow[line width=0.2mm]{angle 90 reversed}}}" `elem` tikzDecorations1 wire
        arrow =
            if isArrowR || isArrowL
            then let
                    needReverse = isArrowL && not reverse || isArrowR && reverse
                    arrow = scale 4 $ translate (r2 (0.354, 0)) $
                            fromOffsets [r2 (1, 0) # rotate (3/8 @@ turn)]
                         <> fromOffsets [r2 (1, 0) # rotate (-3/8 @@ turn)]
                    arrow' = if needReverse then rotate (1/2 @@ turn) arrow else arrow
                 in placeAlongTrail trail 0.5 arrow'
            else mempty
    in if decorate
        then arrow <> stroke trail
        else stroke trail

draw2CellAtomDiagrams :: Bool -> DrawableAtom -> OnlineTex D2
draw2CellAtomDiagrams decorate (DrawableAtom { uatom = IdUAtom _, location, leftBdy, rightBdy }) = do
    wires <- forM (zip leftBdy rightBdy) $ \((dpl, wire), (dpr, _)) -> do
        let pl = pointToVec dpl
        let pr = pointToVec dpr
        return $ translate pl $ strokeWire wire decorate False [straight (pr - pl)]
    return $ translate (pointToVec location) $ mconcat wires
draw2CellAtomDiagrams decorate (DrawableAtom { uatom = MkUAtom celldata _ _, location, leftBdy, rightBdy }) = do
    let label = T.unpack $ render $ label2 celldata
    node <- case label of
              _ | "circle" `elem` tikzOptions2 celldata -> return $ circle 1.5 # fc black
              _ -> mkNodeDiag label
    wires <- forM (map (True,) leftBdy ++ map (False,) rightBdy) $ \(reverse, (dp, wire)) -> do
        let d = pointToVec dp
        let ctrlpt = d & _x .~ 0
        let segment =
                if abs (y dp) <= 0.01
                then straight d
                else bézier3 (ctrlpt/2) (d + (ctrlpt - d)/2) d
        return $ strokeWire wire decorate reverse [segment]
    return $ translate (pointToVec location) $ node <> mconcat wires

drawLO2CDiagrams :: RenderOptions -> Drawable2Cell -> Text
drawLO2CDiagrams opts drawable = let
        render = T.decodeUtf8 . LB.toStrict . toLazyByteString . renderDia PGF with
        baseLength = renderLength2Cell opts
        drawIntermediateCol whichBdy atoms = do
            let lbdy = concatMap (\atom -> map (first (location atom +)) $ whichBdy atom) atoms
                rbdy = map (first (translateh baseLength)) lbdy
            draw2CellAtomDiagrams True (DrawableAtom {
                    uatom = IdUAtom undefined,
                    location = 0,
                    leftBdy = lbdy,
                    rightBdy = rbdy
                })
        rendered :: OnlineTex D2
        rendered = do
            let horizStep = pointToVec (Point baseLength 0)
            firstCol <- drawIntermediateCol leftBdy (head (d2CAtoms drawable))
            columns <- forM (zip [0..] $ d2CAtoms drawable) $ \(i, atoms) -> do
                intermediate <- drawIntermediateCol rightBdy atoms
                nodes <- forM atoms $ draw2CellAtomDiagrams False
                return $ mconcat nodes <> intermediate
            return $ translate (-horizStep) firstCol <> mconcat columns
    in render $ surfOnlineTex with rendered

draw2Cell :: LaTeXC l => RenderOptions -> (f :--> g) -> l
draw2Cell opts =
      (\x ->
         (fromLaTeX . TeXEnv "tikzpicture" [] . raw . drawLO2C opts $ x)
      -- <> (fromLaTeX . raw . drawLO2CDiagrams opts $ x)
      )
    . mkDrawable2Cell (renderLength2Cell opts)
    . flip layOutTwoCell opts
    . twoCellToCanonForm

drawA2Cell :: LaTeXC l => RenderOptions -> A2Cell -> l
drawA2Cell opts (A2Cell c) = draw2Cell opts c

