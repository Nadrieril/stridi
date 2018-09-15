{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, FlexibleContexts,
    RecordWildCards, AllowAmbiguousTypes, ViewPatterns, TypeFamilies, TypeFamilyDependencies,
    ConstraintKinds #-}
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
import Control.Arrow ((***))
import Control.Monad.State.Strict
import Control.Monad.Writer.Class
import Control.Monad.RWS.Strict
import Control.Exception.Base (assert)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)
import Debug.Trace
import Text.LaTeX
import Text.LaTeX.Base.Class (comm1, LaTeXC, fromLaTeX)
import Text.LaTeX.Base.Syntax (LaTeX(..))

import StriDi.TypedSeq
import StriDi.Cells


traceShowIdLbl lbl x = trace (lbl ++ ": " ++ show x) x

approx :: Rational -> Float
approx x = realToFrac (round (100 * realToFrac x)) / 100


data TwoCellAtom (f :: a :-> b) (g :: a :-> b) where
    IdAtom :: Sing1 f -> TwoCellAtom f f
    MkAtom :: TwoCellData -> Sing1 f -> Sing1 g -> TwoCellAtom f g

srcAtom :: TwoCellAtom f g -> Sing1 f
srcAtom (IdAtom f) = f
srcAtom (MkAtom _ f _) = f

tgtAtom :: TwoCellAtom f g -> Sing1 g
tgtAtom (IdAtom f) = f
tgtAtom (MkAtom _ _ g) = g



data TwoCellSlice (f :: a :-> b) (g :: a :-> b) where
    EmptySlice :: Sing0 a -> TwoCellSlice (TId1 :: a :-> a) (TId1 :: a :-> a)
    ConsSlice :: TwoCellAtom (f :: a :-> b) (g :: a :-> b)
            -> TwoCellSlice h i -> TwoCellSlice (f `Cmp1` h) (g `Cmp1` i)

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



type TwoCellCanonForm = Interleaved TwoCellSlice Sing1

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
twoCellToCanonForm (Id2 f) = CmpIntl f (idSlice f) $ NilIntl f
twoCellToCanonForm (Mk2 d f g) = CmpIntl f (singSlice $ MkAtom d f g) $ NilIntl g
twoCellToCanonForm (Cmp2 c1 c2) = twoCellToCanonForm c1 `mergeInterleaved` twoCellToCanonForm c2
twoCellToCanonForm (Tensor2 c1 c2) = twoCellToCanonForm c1 `tensorCanonForm` twoCellToCanonForm c2



data TwoCellBoundary f = Bdy {
    repBdy :: Sing1 f,
    unBdy :: [Rational]
}

instance Show (TwoCellBoundary f) where
    show (Bdy f bdy) =
        "TwoCellBoundary (" ++ show1CellLabel f ++ ") "
        ++ "[" ++ intercalate ", " (show . approx <$> bdy) ++ "]"

defaultBoundary :: Rational -> Sing1 f -> TwoCellBoundary f
defaultBoundary baseWidth f = Bdy f $
        if length1 f == 0
            then [0]
            else [0] ++ replicate (length1 f - 1) baseWidth ++ [0]

splitBoundary :: Sing1 f -> Sing1 g -> TwoCellBoundary (f `Cmp1` g) -> (TwoCellBoundary f, TwoCellBoundary g)
splitBoundary f g (Bdy _ l) = let
        n = length1 f
        before = take n l
        mid = l !! n
        after = drop (n + 1) l
    in ( Bdy f (before ++ [mid/2])
       , Bdy g ([mid/2] ++ after))

mergeBoundary :: Rational -> TwoCellBoundary f -> TwoCellBoundary g -> TwoCellBoundary (f `Cmp1` g)
mergeBoundary baseWidth (Bdy f lf) (Bdy g lg) = Bdy (f `cmp1` g) (init lf ++ [last lf + head lg] ++ tail lg)



data TwoCellBdyDelta f = BdyDelta {
    repDelta :: Sing1 f,
    unDelta :: [(Int, Rational)]
}
type BdyDelta f = (Int, Rational)

instance Show (TwoCellBdyDelta f) where
    show (BdyDelta f delta) =
        "TwoCellBdyDelta (" ++ show1CellLabel f ++ ") "
        ++ "[" ++ intercalate ", " (show . (fmap approx) <$> delta) ++ "]"

nilDelta :: Sing1 f -> TwoCellBdyDelta f
nilDelta f = BdyDelta f []

mergeDeltas :: TwoCellBdyDelta f -> TwoCellBdyDelta f -> TwoCellBdyDelta f
mergeDeltas (BdyDelta f d1) (BdyDelta _ d2) = BdyDelta f $ d1 ++ d2

tensorDeltas :: TwoCellBdyDelta f -> TwoCellBdyDelta g -> TwoCellBdyDelta (f `Cmp1` g)
tensorDeltas (BdyDelta f deltasf) (BdyDelta g deltasg) =
    BdyDelta (f `cmp1` g) $ deltasf ++ fmap (\(i, d) -> (i + length1 f, d)) deltasg

splitDeltas :: Sing1 f -> Sing1 g -> TwoCellBdyDelta (f `Cmp1` g) -> (TwoCellBdyDelta f, TwoCellBdyDelta g)
splitDeltas f g (unDelta -> deltas) = let
        nf = length1 f
        (deltasf, deltasg) = partition (\(i, _) -> i <= nf) deltas
    in (BdyDelta f deltasf, BdyDelta g $ fmap (\(i, d) -> (i - nf, d)) deltasg)

mapDeltas :: Sing1 f -> Sing1 g
            -> (TwoCellBdyDelta f -> TwoCellBdyDelta f')
            -> (TwoCellBdyDelta g -> TwoCellBdyDelta g')
            -> TwoCellBdyDelta (f `Cmp1` g) -> TwoCellBdyDelta (f' `Cmp1` g')
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


mergeBD :: Rational -> (TwoCellBoundary f, TwoCellBdyDelta h) -> (TwoCellBoundary g, TwoCellBdyDelta i) -> (TwoCellBoundary (f `Cmp1` g), TwoCellBdyDelta (h `Cmp1` i))
mergeBD baseWidth ((Bdy f lf), deltash) ((Bdy g lg), deltasi) =
    let midb = last lf + head lg
        deltaMerge = BdyDelta (repDelta deltasi) $
            if midb >= baseWidth then [] else [(0, baseWidth - midb)]
     in ( Bdy (f `cmp1` g) (init lf ++ [baseWidth `max` midb] ++ tail lg)
        , deltash `tensorDeltas` (deltasi `mergeDeltas` deltaMerge))

backpropBdyAtom :: Rational -> TwoCellAtom f g -> TwoCellBoundary g -> (TwoCellBoundary f, TwoCellBdyDelta g)
backpropBdyAtom baseWidth (IdAtom f) bdy = (bdy, nilDelta f)
backpropBdyAtom baseWidth (MkAtom _ f g) (unBdy -> bdy) = let
        inputs = length1 f
        outputs = length1 g
        newbdy = defaultBoundary baseWidth f
        outputWidth = sum bdy
        inputWidth = sum $ unBdy newbdy
        deltaWidth = outputWidth - inputWidth
        (x1, x2) = (head bdy, last bdy)

     in if deltaWidth > 0
            -- If there is already enough space to fit the cell, spread the leftover space evenly,
            -- so that the cell remains centered wrt its outputs.
           then let srcDelta = BdyDelta f [(0, deltaWidth/2 + x1 - (x1 + x2) / 2), (inputs, deltaWidth/2 + x2 - (x1 + x2) / 2)]
                in (applyDeltas srcDelta newbdy, nilDelta g)
            -- Otherwise, make space for the cell
           else let tgtDelta = BdyDelta g [(0, abs deltaWidth/2), (outputs, abs deltaWidth/2)]
                in (newbdy, tgtDelta)

backpropBdySlice :: Rational -> TwoCellSlice f g -> TwoCellBoundary g -> (TwoCellBoundary f, TwoCellBdyDelta g)
backpropBdySlice baseWidth (EmptySlice a) bdy = (bdy, nilDelta $ Id1 a)
backpropBdySlice baseWidth s@(ConsSlice atom q) bdy =
    let (bdyAtom, bdyQ) = splitBoundary (tgtAtom atom) (tgtSlice q) bdy
     in mergeBD baseWidth
            (backpropBdyAtom baseWidth atom bdyAtom)
            (backpropBdySlice baseWidth q bdyQ)



data TwoCellSliceAndDelta f g = SliceAndDelta {
    sliceSD :: TwoCellSlice f g,
    deltaSD :: TwoCellBdyDelta g
}

accumulateDeltasSD :: TwoCellBdyDelta f -> TwoCellSliceAndDelta f g -> TwoCellBdyDelta g
accumulateDeltasSD deltas sd = propagateDeltasSlice (sliceSD sd) deltas `mergeDeltas` deltaSD sd

type PartiallyLayedOut2Cell = Interleaved TwoCellSliceAndDelta TwoCellBoundary

partiallyLayOutTwoCell :: Rational -> TwoCellCanonForm f g -> PartiallyLayedOut2Cell f g
partiallyLayOutTwoCell baseWidth (NilIntl g) = NilIntl $ defaultBoundary baseWidth g
partiallyLayOutTwoCell baseWidth (CmpIntl _ s q) =
    let newq = partiallyLayOutTwoCell baseWidth q
        (newbdy, deltas) = backpropBdySlice baseWidth s (headInterleaved newq)
     in CmpIntl newbdy (SliceAndDelta s deltas) newq

type LayedOut2Cell = Interleaved TwoCellSlice TwoCellBoundary

propagateDeltasLO2C :: PartiallyLayedOut2Cell f g -> LayedOut2Cell f g
propagateDeltasLO2C c = let
        firstDeltas = nilDelta $ repBdy $ headInterleaved c
     in snd $ mapAccumInterleaved (\deltas sd -> (accumulateDeltasSD deltas sd, sliceSD sd)) applyDeltas firstDeltas c

layOutTwoCell :: forall f g. Rational -> TwoCellCanonForm f g -> LayedOut2Cell f g
layOutTwoCell baseWidth = propagateDeltasLO2C . partiallyLayOutTwoCell baseWidth



data RenderOptions = RenderOptions {
    renderWidth2Cell :: Rational,
    renderLength2Cell :: Rational
}

defaultRenderOpts = RenderOptions 1 1
largeRenderOpts = RenderOptions 2 1

data Point = Point Rational Rational
instance Show Point where
    show (Point x y) = "(" ++ show (approx x) ++ "," ++ show (approx y) ++ ")"
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

instance Num Point where
    (Point x1 y1) + (Point x2 y2) = Point (x1+x2) (y1+y2)
    (Point x1 y1) - (Point x2 y2) = Point (x1-x2) (y1-y2)

scalePoint :: Rational -> Point -> Point
scalePoint k (Point x y) = Point (k*x) (k*y)

midPoint :: Point -> Point -> Point
midPoint p1 p2 = scalePoint (1/2) $ p1 + p2


ensuremath :: LaTeXC l => l -> l
ensuremath = comm1 "ensuremath"

mkLine decorate d a1 a2 p1 p2 =
    "\\draw[" <> T.intercalate ", " (tikzOptions1 d ++ if decorate then tikzDecorations1 d else []) <> "] "
    <> render p1
    <> " to[out=" <> a1 <> ", in=" <> a2 <> "] "
    <> render p2
    <> ";\n"
mkLabel p anchor label =
    "\\node at " <> render p
    <> " [anchor=" <> anchor <> "] {"
    <> render (ensuremath $ label1 label)
    <> "};\n"
mkNode p d name =
    "\\node at " <> render p
    <> " [" <> T.intercalate ", " (tikzOptions2 d) <> "] "
    <> name
    <> " {" <> render (ensuremath $ label2 d) <> "};\n"

type MonadDraw2Cell m = (MonadWriter (Text, Text) m, MonadState Int m)

drawInMatrix :: MonadDraw2Cell m => Text -> m ()
drawInMatrix t = tell (t, "")
drawOutMatrix :: MonadDraw2Cell m => Text -> m ()
drawOutMatrix t = tell ("", t)

newName :: MonadDraw2Cell m => m Text
newName = do
    (i :: Int) <- get
    modify (+1)
    return $ "n" <> T.pack (show i)

data NamedNode = NamedNode {
    nodeName :: Text,
    node1CData :: OneCellData
}

instance Show NamedNode where
    show = T.unpack . render

instance Render NamedNode where
    render n = "(" <> nodeName n <> ")"

namePoint :: (MonadDraw2Cell m, Render s) => OneCellData -> s -> m NamedNode
namePoint d p = do
    name <- newName
    drawInMatrix $ "\\path " <> render p <> " node[coordinate] (" <> name <> ") {};\n"
    return $ NamedNode name d

pointsFromBdy :: TwoCellBoundary f -> Point -> [(Point, OneCellData)]
pointsFromBdy (Bdy f bdy) p0 =
    [ (p, d)
    | d <- list1Cells f
    | p <- init $ tail $ scanl (flip translatev) p0 bdy ]

draw2CellAtom :: MonadDraw2Cell m => RenderOptions -> Point -> Point -> TwoCellBoundary f -> TwoCellBoundary g -> TwoCellAtom f g -> [NamedNode] -> m [NamedNode]
draw2CellAtom opts pl pr _ _ (IdAtom _) inputNodes = return inputNodes
draw2CellAtom opts pl pr bdyl@(Bdy _ unbdyl) bdyr@(Bdy _ unbdyr) (MkAtom label f g) inputNodes = do
    let deltaFromBorder = Point (renderLength2Cell opts / 2) 0
        inputs = length1 f
        outputs = length1 g
        pnode = case () of
            _ | inputs == 0 && outputs == 0 ->
                    translatev ((sum unbdyl) / 2) pl
            _ | inputs == 0 ->
                    translatev (head unbdyr + (sum $ init $ tail unbdyr) / 2) pr
            _  ->
                    translatev (head unbdyl + (sum $ init $ tail unbdyl) / 2) pl

    name <- newName
    -- Draw the node once to enable referring to its anchors
    drawInMatrix $ mkNode pnode label ("(" <> name <> ")")

    -- Draw input and output wires, naming the nodes to be able to link them across matrix cell boudaries
    pointsLeft <- forM (pointsFromBdy bdyl (pl - pnode - deltaFromBorder)) $ \(dp, d) -> do
        pname <- namePoint d $ "(" <> name <> ".west) ++" <> render dp
        let angle = if abs (y dp) <= 0.1 then "180" else if y dp > 0 then "up" else "down"
        drawInMatrix $ mkLine False d "0" angle pname pnode
        return pname
    pointsRight <- forM (pointsFromBdy bdyr (pr - pnode + deltaFromBorder)) $ \(dp, d) -> do
        pname <- namePoint d $ "(" <> name <> ".east) ++" <> render dp
        let angle = if abs (y dp) <= 0.1 then "0" else if y dp > 0 then "up" else "down"
        drawInMatrix $ mkLine False d angle "180" pnode pname
        return pname

    -- Draw the node again to hide overlapping lines
    drawInMatrix $ mkNode pnode label ""

    -- Link with previously drawn cells
    forM_ (zip inputNodes pointsLeft) $ \(pl, pr) ->
        drawOutMatrix $ mkLine True (node1CData pl) "0" "180" pl pr

    return pointsRight

draw2CellSlice :: MonadDraw2Cell m => RenderOptions -> Point -> Point -> TwoCellBoundary f -> TwoCellBoundary g -> TwoCellSlice f g -> [NamedNode] -> m [NamedNode]
draw2CellSlice opts pl pr bdyf bdyg (EmptySlice _) _ = do
    -- let deltaFromBorder = Point (renderLength2Cell opts / 2) 0
    -- let pl' = translatev (head (unBdy bdyf)) pl - deltaFromBorder
    -- let pr' = translatev (head (unBdy bdyg)) pr + deltaFromBorder
    -- drawInMatrix $ mkLine False (OneCellData "" ["blue"] []) "0" "180" pl' pr'
    return []
draw2CellSlice opts pl pr bdyf bdyg (ConsSlice atom q) inputNodes = let
        (bdySrcAtom, bdySrcQ) = splitBoundary (srcAtom atom) (srcSlice q) bdyf
        (bdyTgtAtom, bdyTgtQ) = splitBoundary (tgtAtom atom) (tgtSlice q) bdyg
        (inputNodesAtom, inputNodesQ) = splitAt (length1 $ srcAtom atom) inputNodes
    in do
        outputNodesAtom <- draw2CellAtom opts pl pr bdySrcAtom bdyTgtAtom atom inputNodesAtom
        outputNodesSlice <- draw2CellSlice opts (translatev (sum $ unBdy bdySrcAtom) pl) (translatev (sum $ unBdy bdyTgtAtom) pr) (bdySrcQ) (bdyTgtQ) q inputNodesQ
        return $ outputNodesAtom ++ outputNodesSlice

drawLO2C :: RenderOptions -> LayedOut2Cell f g -> Text
drawLO2C opts c = (\(inm, outm) -> inm <> outm) $ snd $ (\x -> evalRWS x () 0) $ do
    let p0 = Point 0 0
    let deltaFromBorder = Point (renderLength2Cell opts / 2) 0

    drawInMatrix $ "\\matrix[column sep=3mm]{"

    pointsLeft <- forM (pointsFromBdy (headInterleaved c) p0) $ \(p, d) -> do
        let p' = p - deltaFromBorder
        drawInMatrix $ mkLabel p' "east" d
        drawInMatrix $ mkLine False d "0" "180" p' p
        namePoint d p
    drawInMatrix $ "&\n"

    pts2Cell <- foldM (\nodes f -> f nodes) pointsLeft
        (iterInterleaved c $ \(bdyl, slice, bdyr) -> \nodes ->
            draw2CellSlice opts p0 p0 bdyl bdyr slice nodes
            <* drawInMatrix "&\n"
        )

    pointsRight <- forM (pointsFromBdy (lastInterleaved c) p0) $ \(p, d) -> do
        let p' = p + deltaFromBorder
        drawInMatrix $ mkLabel p' "west" d
        drawInMatrix $ mkLine False d "0" "180" p p'
        namePoint d p

    drawInMatrix $ "\\\\};"

    forM_ (zip pts2Cell pointsRight) $ \(pl, pr) ->
        drawOutMatrix $ mkLine True (node1CData pl) "0" "180" pl pr

draw2Cell :: LaTeXC l => RenderOptions -> (f :--> g) -> l
draw2Cell opts = fromLaTeX . TeXEnv "tikzpicture" [] . raw
    . drawLO2C opts
    . layOutTwoCell (renderWidth2Cell opts)
    . twoCellToCanonForm

drawA2Cell :: LaTeXC l => RenderOptions -> A2Cell -> l
drawA2Cell opts (A2Cell c) = draw2Cell opts c

