{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, FlexibleContexts,
    RecordWildCards, AllowAmbiguousTypes, ViewPatterns #-}
module StriDi.Render
    ( Id1, Cmp1, (:-->)(..)
    , id2, labelled2
    , flip2Cell
    , draw2Cell
    ) where

import qualified Data.Text as T
import Data.Proxy
import Control.Monad.State.Strict
import Control.Monad.Writer.Class
import Control.Monad.RWS.Strict
import Control.Exception.Base (assert)
import Text.LaTeX

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



mkLine a1 a2 p1 p2 = "\\draw " <> render p1 <> " to[out=" <> a1 <> ", in=" <> a2 <> "] " <> render p2 <> ";\n"
mkLabel p anchor label = "\\node at " <> render p <> " [anchor=" <> anchor <> "] {" <> label <> "};\n"
mkNode p label = "\\node at " <> render p <> " [circle, draw, fill=white] {" <> label <> "};\n"

draw2Cell :: (f :--> g) -> Text
draw2Cell = drawLO2C (Point 0 0) . layOut2Cell . twoCellToCanonForm




data TwoCellAtom f g = TwoCellAtom {
    before :: Int,
    after :: Int,
    inputs :: Int,
    outputs :: Int,
    inRep :: Sing f,
    outRep :: Sing g,
    label :: Text
}

totalInputs :: TwoCellAtom f g -> Int
totalInputs TwoCellAtom{..} = before + inputs + after

totalOutputs :: TwoCellAtom f g -> Int
totalOutputs TwoCellAtom{..} = before + outputs + after

flip2CellAtom :: TwoCellAtom f g -> TwoCellAtom g f
flip2CellAtom ca@TwoCellAtom{..} = ca { inputs = outputs, outputs = inputs }

tensor2CellAtomL :: forall x f g. Sing x -> TwoCellAtom f g -> TwoCellAtom (x `Cmp1` f) (x `Cmp1` g)
tensor2CellAtomL sx ca = ca {
        before = before ca + length sx,
        inRep = sx ++ inRep ca,
        outRep = sx ++ outRep ca
    }

tensor2CellAtomR :: forall x f g. Sing x -> TwoCellAtom f g -> TwoCellAtom (f `Cmp1` x) (g `Cmp1` x)
tensor2CellAtomR sx ca = ca {
        after = after ca + length sx,
        inRep = inRep ca ++ sx,
        outRep = outRep ca ++ sx
    }


type TwoCellCanonForm = Composite TwoCellAtom

tensorCanonFormL :: forall x f g. Sing x -> TwoCellCanonForm f g -> TwoCellCanonForm (x `Cmp1` f) (x `Cmp1` g)
tensorCanonFormL sx NilCte = NilCte
tensorCanonFormL sx (CmpCte (atom :: TwoCellAtom f h) q) = CmpCte (tensor2CellAtomL @x sx atom) $ tensorCanonFormL @x sx q

tensorCanonFormR :: forall x f g. Sing x -> TwoCellCanonForm f g -> TwoCellCanonForm (f `Cmp1` x) (g `Cmp1` x)
tensorCanonFormR sx NilCte = NilCte
tensorCanonFormR sx (CmpCte (atom :: TwoCellAtom f h) q) = CmpCte (tensor2CellAtomR @x sx atom) $ tensorCanonFormR @x sx q

twoCellToCanonForm :: f :--> g -> TwoCellCanonForm f g
twoCellToCanonForm (Id2 sf) = twoCellToCanonForm (Labelled2 "id" sf sf)
twoCellToCanonForm (Labelled2 n sf sg) = singComposite $ TwoCellAtom {
        before = 0,
        after = 0,
        inputs = length sf,
        outputs = length sg,
        inRep = sf,
        outRep = sg,
        label = n
    }
twoCellToCanonForm (Cmp2 c1 c2) = (twoCellToCanonForm c1) `mergeComposite` (twoCellToCanonForm c2)
twoCellToCanonForm (Tensor2 (Id2 sf :: f :--> g) (c2 :: f' :--> g')) =
    tensorCanonFormL @f sf $ twoCellToCanonForm c2
twoCellToCanonForm (Tensor2 (c1 :: f :--> g) (Id2 sf :: f' :--> g')) =
    tensorCanonFormR @f' sf $ twoCellToCanonForm c1
twoCellToCanonForm (Tensor2 (c1 :: f1 :--> g1) (c2 :: f2 :--> g2)) =
    twoCellToCanonForm $
        (c1 `Tensor2` Id2 @f2 (extractLeftRep c2))
        `Cmp2` (Id2 @g1 (extractLeftRep (flip2Cell c1)) `Tensor2` c2)

twoCellLength :: Rational
twoCellLength = 1

draw2CellAtom :: Point -> TwoCellBoundary f -> TwoCellBoundary g -> TwoCellAtom f g -> Text
draw2CellAtom pl (unBdy -> bdyl) (unBdy -> bdyr) TwoCellAtom{..} =
    let pr = translateh twoCellLength pl
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
        let p = translate (twoCellLength / 2) (width / 2) p1
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
    repBdy :: Sing f,
    unBdy :: [Rational]
}

baseWidth :: Rational
baseWidth = 1

defaultBoundary :: TwoCellAtom f g -> TwoCellBoundary g
defaultBoundary ca = Bdy (outRep ca) $ replicate (totalOutputs ca+1) baseWidth

backpropBoundary :: TwoCellAtom f g -> TwoCellBoundary g -> TwoCellBoundary f
backpropBoundary ca@TwoCellAtom{..} bdy = let
        (bdybefore, mid, bdyafter) = projectBdyR ca bdy
        h = case mid of
              Left h -> h
              Right (x1, mid, x2) -> x1 + sum mid + x2
        newh = realToFrac (inputs + 1) * baseWidth
        newmid = if inputs == 0 then [h] else let
                newmid = replicate (inputs - 1) baseWidth
                (x1, x2) = case mid of
                    _ | newh > h -> (baseWidth, baseWidth)
                    Left h -> (baseWidth + (h - newh)/2, baseWidth + (h - newh)/2)
                    Right (x1, mid, x2) -> let
                        outWidth = sum mid
                        inWidth = sum newmid
                      in (x1 + (outWidth - inWidth) / 2, x2 + (outWidth - inWidth) / 2)
            in [x1] ++ newmid ++ [x2]
    in Bdy inRep $ bdybefore ++ newmid ++ bdyafter

projectBdyL :: TwoCellAtom f g -> TwoCellBoundary f ->
        ([Rational], Either Rational (Rational, [Rational], Rational), [Rational])
projectBdyL = projectBdyR . flip2CellAtom

projectBdyR :: TwoCellAtom f g -> TwoCellBoundary g ->
        ([Rational], Either Rational (Rational, [Rational], Rational), [Rational])
projectBdyR TwoCellAtom{..} (unBdy -> bdy) =
    let (bdybefore, (mid, bdyafter)) =
            fmap (splitAt (outputs+1)) $ splitAt before bdy
     in (bdybefore,
        if outputs == 0
           then Left (head mid)
           else Right (head mid, tail $ init mid, last mid),
        bdyafter)


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

backpropDelta :: TwoCellAtom f g -> TwoCellBoundary g -> [BdyDelta g]
backpropDelta TwoCellAtom{..} (unBdy -> bdy) = let
        h = sum $ take (outputs+1) $ drop before bdy
        newh = realToFrac (inputs+1) * baseWidth
     in if newh > h
        then [(before, (newh - h)/2), (before + outputs, (newh - h)/2)]
        else []


type LayedOut2Cell = Interleaved TwoCellAtom TwoCellBoundary

layOut2Cell :: forall f g. TwoCellCanonForm f g -> LayedOut2Cell f g
layOut2Cell c = propagateDeltasLO2C [] $ interleaveInComposite backpropBoundary lastBdy c
    where
        lastBdy :: TwoCellBoundary g
        lastBdy = lastComposite c defaultBoundary undefined

        applyDeltas :: forall f. [BdyDelta f] -> TwoCellBoundary f -> TwoCellBoundary f
        applyDeltas = flip $ foldr applyDelta

        propagateAndAccumulateDeltas :: forall f g. [BdyDelta f] -> TwoCellAtom f g -> TwoCellBoundary g -> [BdyDelta g]
        propagateAndAccumulateDeltas deltas atom bdy =
            concatMap (propagateDelta atom) deltas ++ backpropDelta atom bdy

        propagateDeltasLO2C :: forall f g. [BdyDelta f] -> LayedOut2Cell f g -> LayedOut2Cell f g
        propagateDeltasLO2C deltas (NilIntl bdy) = NilIntl $ applyDeltas deltas bdy
        propagateDeltasLO2C deltas (CmpIntl bdy (atom :: TwoCellAtom f h) q) =
                CmpIntl newbdy atom $ propagateDeltasLO2C @h @g newdeltas q
            where
                newbdy = applyDeltas deltas bdy
                newdeltas = propagateAndAccumulateDeltas deltas atom (headInterleaved q)

drawLO2C :: Point -> LayedOut2Cell f g -> Text
drawLO2C p0 c =
    let (pend, output) = (\x -> execRWS x () p0) $ sequence_
            (iterInterleaved c $ \(bdyl, atom, bdyr) -> do
                p <- get
                tell $ draw2CellAtom p bdyl bdyr atom
                put (translateh twoCellLength p)
            )
    in output
       <> drawBdyLabels (headInterleaved c) p0 "east"
       <> drawBdyLabels (lastInterleaved c) pend "west"
    where
        drawBdyLabels (Bdy rep bdy) p0 dir =
            T.unlines [ mkLabel p dir n
                | n <- rep
                | p <- tail $ scanl (flip translatev) p0 bdy ]
