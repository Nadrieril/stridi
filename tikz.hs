{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, LambdaCase, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, FlexibleContexts,
    RecordWildCards, AllowAmbiguousTypes #-}
import GHC.TypeLits
import Data.List (intersperse)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Promotion.Prelude.List
import Data.Proxy
import Control.Monad.State.Class
import Control.Monad.Writer.Class
import Control.Monad.RWS.Strict
import Control.Exception.Base (assert)
import Debug.Trace

import Text.LaTeX hiding (In)
import Text.LaTeX.Packages.TikZ
import Text.LaTeX.Base.Syntax hiding (In)
import Text.LaTeX.Base.Class

main :: IO ()
main = execLaTeXT theBody >>= TIO.putStrLn . render

theBody :: LaTeXT IO ()
theBody = do
    "A string diagram"
    center $ fromLaTeX $ TeXEnv "tikzpicture" [OptArg "scale=0.5"] $ mconcat $ intersperse "\n" $ fmap raw
        [ "\\fill[catc] (0,1) -- ++(0,1) -- ++(4,0) -- (4,1) -- cycle;"
        , "\\fill[catd] (0,1) -- ++(0,-1) -- ++(4,0) -- (4,1) -- cycle;"
        , "\\draw (0,1) -- (4,1);"
        , "\\draw (0,1) node[anchor=east] {$\\icol{x\\\\u}$};"
        , "\\draw (4,1) node[anchor=west] {$\\icol{y\\\\v}$};"
        ]
    "Another string diagram"
    center $ fromLaTeX $ TeXEnv "tikzpicture" [] $
        raw $ draw2Cell $ let
                alpha = Labelled2 "$\\alpha$" :: (F `Cmp1` F) :--> F
                beta = Labelled2 "$\\beta$" :: F :--> (G `Cmp1` H `Cmp1` H)
                gamma = Labelled2 "$\\gamma$" :: (G `Cmp1` H) :--> F
                delta = Labelled2 "$\\delta$" :: H :--> Id1
                eta = Labelled2 "$\\eta$" :: F :--> Id1
                mu = Labelled2 "$\\mu$" :: (G `Cmp1` G) :--> Id1
                nu = Labelled2 "$\\nu$" :: Id1 :--> (G `Cmp1` G)
                omega = Labelled2 "$\\omega$" :: Id1 :--> (F `Cmp1` F)
                epsilon = Labelled2 "$\\epsilon$" :: G :--> G
                x = omega
                    `Cmp2` alpha
                    `Cmp2` beta
                    `Cmp2` (gamma `Tensor2` delta)
                    `Cmp2` eta
                        :: Id1 :--> Id1
            in
            (nu `Cmp2`((epsilon `Cmp2` epsilon)
                `Tensor2` x `Tensor2` Id2 @G) `Cmp2` mu)
    center $ fromLaTeX $ TeXEnv "tikzpicture" [] $
        raw $ draw2Cell $ let
                beta = Labelled2 "$\\beta$" :: F :--> (F `Cmp1` G)
                gamma = Labelled2 "$\\gamma$" :: G :--> H
                eta = Labelled2 "$\\eta$" :: F :--> Id1
            in beta `Cmp2` (eta `Tensor2` gamma)
    center $ fromLaTeX $ TeXEnv "tikzpicture" [] $
        raw $ draw2Cell $ let
                beta = Labelled2 "$\\beta$" :: F :--> (F `Cmp1` G `Cmp1` H)
                gamma = Labelled2 "$\\gamma$" :: G :--> F
                delta = Labelled2 "$\\delta$" :: H :--> Id1
                eta = Labelled2 "$\\eta$" :: F :--> Id1
                omega = Labelled2 "$\\omega$" :: Id1 :--> F
                x = beta
                    `Cmp2` (eta `Tensor2` gamma `Tensor2` delta)
                    `Cmp2` eta
            in x
    center $ fromLaTeX $ TeXEnv "tikzpicture" [] $
        raw $ draw2Cell $ let
                beta = Labelled2 "$\\beta$" :: F :--> (G `Cmp1` H `Cmp1` H)
                gamma = Labelled2 "$\\gamma$" :: (G `Cmp1` H) :--> F
                delta = Labelled2 "$\\delta$" :: H :--> Id1
                eta = Labelled2 "$\\eta$" :: F :--> Id1
                mu = Labelled2 "$\\mu$" :: (G `Cmp1` G) :--> Id1
                nu = Labelled2 "$\\nu$" :: Id1 :--> (G `Cmp1` G)
                omega = Labelled2 "$\\omega$" :: Id1 :--> F
                x = omega
                    `Cmp2` beta
                    `Cmp2` (gamma `Tensor2` delta)
                    `Cmp2` eta
                        :: Id1 :--> Id1
            in
            (nu `Cmp2` (Id2 @G `Tensor2` x `Tensor2` Id2 @G) `Cmp2` mu)
    "Another string diagram"
    center $ fromLaTeX $ TeXEnv "tikzpicture" [] $
        raw $ draw2Cell $ let
                alpha = Labelled2 "$\\beta$" :: Id1 :--> (F `Cmp1` G)
                beta = Labelled2 "$\\alpha$" :: (F `Cmp1` G) :--> Id1
                circle = Id2 @H `Tensor2` (alpha `Cmp2` beta) `Tensor2` Id2 @H
            in
            circle `Cmp2` (Id2 @H `Tensor2` Id2 @H) `Cmp2` flip2Cell circle
    "End of "
    hatex

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


type A1Cell = [Symbol]
type Id1 = '[]
type Cmp1 a b = a :++ b
type F = '["$F$"]
type G = '["$G$"]
type H = '["$H$"]


data (f :: A1Cell) :--> (g :: A1Cell) where
    Labelled2 :: (Reify1 f, Reify1 g) => Text -> f :--> g
    Id2 :: Reify1 f => f :--> f
    Cmp2 :: (Reify1 f, Reify1 g, Reify1 h) => (f :--> g) -> (g :--> h) -> (f :--> h)
    Tensor2 :: (Reify1 f, Reify1 g, Reify1 f', Reify1 g',
                Reify1 (Cmp1 f f'), Reify1 (Cmp1 g g'), Reify1 (Cmp1 f g'), Reify1 (Cmp1 g f')) =>
        (f :--> g) -> (f' :--> g') -> (Cmp1 f f' :--> Cmp1 g g')

length2Cell :: (f :--> g) -> Rational
length2Cell (Cmp2 alpha beta) = length2Cell alpha + length2Cell beta
length2Cell (Tensor2 alpha beta) = length2Cell alpha `max` length2Cell beta
length2Cell _ = 2

width2Cell :: forall f g. (Reify1 f, Reify1 g) => (f :--> g) -> Rational
width2Cell (Cmp2 alpha beta) = width2Cell alpha `max` width2Cell beta
width2Cell (Tensor2 alpha beta) = width2Cell alpha + width2Cell beta
width2Cell _ = realToFrac $ length (treeToList (reify1 @f)) `max` length (treeToList (reify1 @g))

flip2Cell :: f :--> g -> g :--> f
flip2Cell Id2 = Id2
flip2Cell (Labelled2 n) = Labelled2 (n <> "'")
flip2Cell (Cmp2 c1 c2) = Cmp2 (flip2Cell c2) (flip2Cell c1)
flip2Cell (Tensor2 c1 c2) = Tensor2 (flip2Cell c1) (flip2Cell c2)

canonicalize2Cell :: f :--> g -> f :--> g
canonicalize2Cell Id2 = Id2
canonicalize2Cell (Labelled2 n) = Labelled2 n
canonicalize2Cell (Cmp2 c1 c2) = Cmp2 (canonicalize2Cell c1) (canonicalize2Cell c2)
canonicalize2Cell (Tensor2 (c1 :: f' :--> g') (c2 :: f'' :--> g'')) =
    (canonicalize2Cell c1 `Tensor2` Id2 @f'') `Cmp2` (Id2 @g' `Tensor2` canonicalize2Cell c2)


data Tree1 (f :: [Symbol]) a where
    TreeNil :: Tree1 Id1 a
    TreeCons :: (Reify1 f, KnownSymbol s) => Proxy s -> a -> Tree1 f a -> Tree1 (s ': f) a

instance Functor (Tree1 f) where
    fmap f TreeNil = TreeNil
    fmap f (TreeCons n x q) = TreeCons n (f x) $ fmap f q

treeToList :: Tree1 f a -> [(String, a)]
treeToList TreeNil = []
treeToList (TreeCons n x q) = (symbolVal n, x) : treeToList q

class Reify1 (f :: [Symbol]) where
    reify1 :: Tree1 f ()
instance Reify1 '[] where
    reify1 = TreeNil
instance (KnownSymbol s, Reify1 f) => Reify1 (s ': f) where
    reify1 = TreeCons Proxy () (reify1 @f)

splitTree1 :: forall f g a. Reify1 f => Tree1 (f `Cmp1` g) a -> (Tree1 f a, Tree1 g a)
splitTree1 t = case (reify1 @f, t) of
    (TreeNil, t) -> (TreeNil, t)
    (TreeCons _ () _, TreeCons n x q) ->
        let (q', q'') = splitTree1 q
        in (TreeCons n x q', q'')

mergeTree1 :: forall f g a. (Reify1 (f `Cmp1` g)) => Tree1 f a -> Tree1 g a -> Tree1 (f `Cmp1` g) a
mergeTree1 TreeNil t2 = t2
mergeTree1 (TreeCons n x q) t2 = case reify1 @(f `Cmp1` g) of
    TreeCons _ () _ -> TreeCons n x $ mergeTree1 q t2

type PointsFor f = Tree1 f Point

generatePoints :: Reify1 f => Point -> (Point -> Point) -> PointsFor f
generatePoints init next = snd $ aux init
    where
        aux :: forall f. Reify1 f => Point -> (Point, PointsFor f)
        aux e = case reify1 @f of
            TreeNil -> (e, TreeNil)
            TreeCons n () (q :: Tree1 g ()) ->
                let (new, q') = aux @g e
                in (next new, TreeCons n new q')

type BoundingBox = (Point, Point)

translatebb :: Rational -> Rational -> BoundingBox -> BoundingBox
translatebb dx dy (lo, hi) = (translate dx dy lo, translate dx dy hi)


centerBdy :: forall f. Reify1 f => (Point, Point) -> PointsFor f -> PointsFor f
centerBdy (Point _ loy, Point _ hiy) bdy =
    let pts = treeToList bdy
        ys = fmap (\(_, Point _ y) -> y) pts
        (miny, maxy) = (minimum ys, maximum ys)
     in fmap (translatev (((hiy + loy) - (maxy + miny)) / 2)) bdy

genBoundaries :: forall f g. (Reify1 f, Reify1 g) => (f :--> g) -> (Point, Point) -> (PointsFor f, PointsFor g)
genBoundaries c p = (centerBdy p $ leftBdy c p, centerBdy p $ rightBdy c p)
    where
        defaultBdy :: forall f. Reify1 f => (Point, Point) -> PointsFor f
        defaultBdy p@(lo, _) = centerBdy p $ generatePoints lo (translatev 1)

        leftBdy :: forall f g. Reify1 f => (f :--> g) -> (Point, Point) -> PointsFor f
        leftBdy (Cmp2 c1 c2) p0 = leftBdy c1 p0
        leftBdy (Tensor2 c1 c2) p@(lo, hi) = let
                mid = translatev (width2Cell c2) lo
                l1 = leftBdy c1 (mid, hi)
                l2 = leftBdy c2 (lo, mid)
            in mergeTree1 l1 l2
        leftBdy _ p = defaultBdy p

        rightBdy :: forall f g. Reify1 g => (f :--> g) -> (Point, Point) -> PointsFor g
        rightBdy (Cmp2 c1 c2) p0 = rightBdy c2 p0
        rightBdy (Tensor2 c1 c2) p@(lo, hi) = let
                mid = translatev (width2Cell c2) lo
                r1 = rightBdy c1 (mid, hi)
                r2 = rightBdy c2 (lo, mid)
            in mergeTree1 r1 r2
        rightBdy _ p = defaultBdy p


mkLine a1 a2 p1 p2 = "\\draw " <> render p1 <> " to[out=" <> a1 <> ", in=" <> a2 <> "] " <> render p2 <> ";"
mkLabel p anchor label = "\\node at " <> render p <> " [anchor=" <> anchor <> "] {" <> label <> "};"
mkNode p label = "\\node at " <> render p <> " [circle, draw, fill=white] {" <> label <> "};"
drawbb (lo, hi) len =
    "\\draw " <>
        render lo <> " -- " <>
        render (translateh len lo) <> " -- " <>
        render (translateh len hi) <> " -- " <>
        render hi <> " -- " <>
        "cycle;"

draw2Cell :: (Reify1 f, Reify1 g) => (f :--> g) -> Text
draw2Cell c = drawCanon2Cell (Point 0 0) (twoCellToCanonForm c)


type TwoCellCanonForm = [TwoCellAtom]

data TwoCellAtom = TwoCellAtom {
    before :: Int,
    after :: Int,
    inputs :: Int,
    outputs :: Int,
    label :: Text
}
    deriving Eq

totalInputs :: TwoCellAtom -> Int
totalInputs TwoCellAtom{..} = before + inputs + after

totalOutputs :: TwoCellAtom -> Int
totalOutputs TwoCellAtom{..} = before + outputs + after

tensorCanonForm :: Int -> Int -> TwoCellCanonForm -> TwoCellCanonForm
tensorCanonForm nbefore nafter = fmap (\ca -> ca {
    before = before ca + nbefore,
    after = after ca + nafter
})

flip2CellAtom :: TwoCellAtom -> TwoCellAtom
flip2CellAtom ca@TwoCellAtom{..} = ca { inputs = outputs, outputs = inputs }

typeWidth :: forall f. Reify1 f => Int
typeWidth = length $ treeToList $ reify1 @f

twoCellToCanonForm :: forall f g. (Reify1 f, Reify1 g) => f :--> g -> TwoCellCanonForm
twoCellToCanonForm Id2 = twoCellToCanonForm (Labelled2 "id" :: f :--> f)
twoCellToCanonForm (Labelled2 n) = [TwoCellAtom {
    before = 0,
    after = 0,
    inputs = typeWidth @f,
    outputs = typeWidth @g,
    label = n
}]
twoCellToCanonForm (Cmp2 c1 c2) = (twoCellToCanonForm c1) ++ (twoCellToCanonForm c2)
twoCellToCanonForm (Tensor2 (c1 :: f' :--> g') (c2 :: f'' :--> g'')) =
    (tensorCanonForm 0 (typeWidth @f'') $ twoCellToCanonForm c1)
    ++ (tensorCanonForm (typeWidth @g') 0 $ twoCellToCanonForm c2)

type TwoCellBoundary = [Rational]

defaultBoundary :: Int -> TwoCellBoundary
defaultBoundary n = replicate (n+1) baseWidth

dumbBoundaries :: TwoCellCanonForm -> [TwoCellBoundary]
dumbBoundaries [] = []
dumbBoundaries (ca:q) =
    let q' = dumbBoundaries q
        q'' = if null q' then [defaultBoundary (totalOutputs ca)] else q'
     in defaultBoundary (totalInputs ca) : q''

type BdyDelta = (Int, Rational)

constructBoundaries :: TwoCellCanonForm -> [TwoCellBoundary]
constructBoundaries c = snd $ foldr pushAtom ([], [defaultBoundary (totalOutputs (last c))]) c
    where
        projectBdyL :: TwoCellAtom -> TwoCellBoundary ->
                ([Rational], Either Rational (Rational, [Rational], Rational), [Rational])
        projectBdyL TwoCellAtom{..} bdy =
            let (bdybefore, (mid, bdyafter)) =
                    fmap (splitAt (inputs+1)) $ splitAt before bdy
             in (bdybefore,
            if inputs == 0
               then Left (head mid)
               else Right (head mid, tail $ init mid, last mid),
            bdyafter)
        projectBdyR :: TwoCellAtom -> TwoCellBoundary ->
                ([Rational], Either Rational (Rational, [Rational], Rational), [Rational])
        projectBdyR TwoCellAtom{..} bdy =
            let (bdybefore, (mid, bdyafter)) =
                    fmap (splitAt (outputs+1)) $ splitAt before bdy
             in (bdybefore,
            if outputs == 0
               then Left (head mid)
               else Right (head mid, tail $ init mid, last mid),
            bdyafter)


        propagateDelta :: TwoCellAtom -> BdyDelta -> [BdyDelta]
        propagateDelta TwoCellAtom{..} (i, delta) =
            if (inputs == 0 && i == before) || (before < i && i < before + inputs)
               then [(before, delta/2), (before+outputs, delta/2)]
            else if i >= before + inputs
               then [(i - inputs + outputs, delta)]
            else [(i, delta)]

        applyDelta :: BdyDelta -> TwoCellBoundary -> TwoCellBoundary
        applyDelta (i, delta) bdy =
            take i bdy ++ [bdy!!i + delta] ++ drop (i+1) bdy

        deepPropagateDeltas :: [BdyDelta] -> TwoCellCanonForm -> [TwoCellBoundary] -> [TwoCellBoundary]
        deepPropagateDeltas _ _ [] = []
        deepPropagateDeltas deltas atoms (bdy:bdys) =
                newbdy : newbdys
            where
                newbdy = foldr applyDelta bdy deltas
                newbdys = case atoms of
                    [] -> bdys
                    (atom:atoms) ->
                        let newdeltas = concatMap (propagateDelta atom) deltas
                         in deepPropagateDeltas newdeltas atoms bdys

        backpropBoundary :: TwoCellAtom -> TwoCellBoundary -> (TwoCellBoundary, [BdyDelta])
        backpropBoundary ca@TwoCellAtom{..} bdy =
            let (bdybefore, mid, bdyafter) = projectBdyR ca bdy
                h = case mid of
                      Left h -> h
                      Right (x1, mid, x2) -> x1 + sum mid + x2
                newh = realToFrac (inputs + 1) * baseWidth
                deltas = if newh > h
                    then [(before, (newh - h)/2), (before + outputs, (newh - h)/2)]
                    else []
                newmid =
                    if inputs == 0 then [h]
                    else let
                        newmid = replicate (inputs - 1) baseWidth
                        (x1, x2) = case mid of
                            _ | newh > h -> (baseWidth, baseWidth)
                            Left h -> (baseWidth, baseWidth + h - newh)
                            Right (x1, mid, x2) -> let
                                outWidth = sum mid
                                inWidth = sum newmid
                              in (x1 + (outWidth - inWidth) / 2, x2 + (outWidth - inWidth) / 2)
                        in [x1] ++ newmid ++ [x2]
            in (bdybefore ++ newmid ++ bdyafter, deltas)

        pushAtom :: TwoCellAtom -> (TwoCellCanonForm, [TwoCellBoundary]) -> (TwoCellCanonForm, [TwoCellBoundary])
        pushAtom ca (atoms, bdys) = assert (length atoms + 1 == length bdys) $
            let (bdy, deltas) = backpropBoundary ca (head bdys)
                bdys' = deepPropagateDeltas deltas atoms bdys
             in (ca : atoms, bdy : bdys')


twoCellLength :: Rational
twoCellLength = 1

baseWidth :: Rational
baseWidth = 1

evalRWS' :: r -> s -> RWS r w s a -> w
evalRWS' r s rws = snd $ evalRWS rws r s

draw2CellAtom :: Point -> TwoCellBoundary -> TwoCellBoundary -> TwoCellAtom -> Text
draw2CellAtom pl bdyl bdyr TwoCellAtom{..} =
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
        (p1, _, bdyl, _) <- get
        let widthInputs = sum $ take (inputs+1) bdyl
        let p = translate (twoCellLength / 2) (realToFrac widthInputs / 2) p1
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
        p1 <- popleft
        p2 <- popright
        tell $ "\\draw[dashed] " <> render p1 <> " -- " <> render p2 <> ";"

drawCanon2Cell :: Point -> TwoCellCanonForm -> Text
drawCanon2Cell p c = let
    bdys = constructBoundaries c
    in evalRWS' () (p, bdys) $ forM_ c $ \ca -> do
        (p, bdys) <- get
        tell $ draw2CellAtom p (head bdys) (head $ tail bdys) ca
        -- tell $ draw2CellAtom p (defaultBoundary (totalInputs ca)) (defaultBoundary (totalOutputs ca)) ca
        put (translateh twoCellLength p, tail bdys)

