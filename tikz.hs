{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, LambdaCase, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, FlexibleContexts #-}
import GHC.TypeLits
import Data.List (intersperse)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Promotion.Prelude.List

import Text.LaTeX
import Text.LaTeX.Packages.TikZ
import Text.LaTeX.Base.Syntax
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
                x = alpha
                    `Cmp2` beta
                    `Cmp2` (gamma `Tensor2` delta)
                    `Cmp2` eta
                        :: (F `Cmp1` F) :--> Id1
            in
            (Id2 @G `Tensor2` x `Tensor2` Id2 @G `Cmp2` mu)
    "Another string diagram"
    center $ fromLaTeX $ TeXEnv "tikzpicture" [] $
        raw $ draw2Cell $ let
                alpha = Labelled2 "$\\beta$" :: Id1 :--> (F `Cmp1` G)
                beta = Labelled2 "$\\alpha$" :: (F `Cmp1` G) :--> Id1
            in
            Id2 @H `Tensor2` (alpha `Cmp2` beta) `Tensor2` Id2 @H
    "End of "
    hatex

data Proxy (a :: k) = Proxy

data Point = Point Float Float
instance Show Point where
    show (Point x y) = "(" ++ show x ++ "," ++ show y ++ ")"
instance Render Point where
    render = T.pack . show

translate :: Float -> Float -> Point -> Point
translate dx dy (Point x y) = Point (x+dx) (y+dy)

translateh :: Float -> Point -> Point
translateh dx = translate dx 0

translatev :: Float -> Point -> Point
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
    Tensor2 :: (Reify1 f, Reify1 g, Reify1 f', Reify1 g') => (f :--> g) -> (f' :--> g') -> (Cmp1 f f' :--> Cmp1 g g')

length2Cell :: (f :--> g) -> Float
length2Cell (Cmp2 alpha beta) = length2Cell alpha + length2Cell beta
length2Cell (Tensor2 alpha beta) = length2Cell alpha `max` length2Cell beta
length2Cell _ = 2

width2Cell :: forall f g. (Reify1 f, Reify1 g) => (f :--> g) -> Float
width2Cell (Cmp2 alpha beta) = width2Cell alpha `max` width2Cell beta
width2Cell (Tensor2 alpha beta) = width2Cell alpha + width2Cell beta
width2Cell _ = realToFrac $ length (treeToList (reify1 @f)) `max` length (treeToList (reify1 @g))

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

translatebb :: Float -> Float -> BoundingBox -> BoundingBox
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
        defaultBdy p@(lo, _) = centerBdy p $ generatePoints (translate 0 0.5 lo) (translatev 1)

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


draw2Cell :: (Reify1 f, Reify1 g) => (f :--> g) -> Text
draw2Cell c =
    drawInner2Cell c (lo, translatev (width2Cell c) lo) ptsf ptsg
        <> T.unlines [ mkLabel p "east" (T.pack n) | (n, p) <- treeToList ptsf ]
        <> T.unlines [ mkLabel p "west" (T.pack n) | (n, p) <- treeToList ptsg ]
    where
        lo = Point 0 0
        hi = translatev (width2Cell c) lo
        (ptsf, ptsg') = genBoundaries c (lo, hi)
        ptsg = fmap (translateh (length2Cell c)) $ ptsg'

        mkLine p1 p2 = "\\draw " <> render p1 <> " to[out=0, in=180] " <> render p2 <> ";"
        mkLabel p anchor label = "\\node at " <> render p <> " [anchor=" <> anchor <> "] {" <> label <> "};"
        mkNode p label = "\\node at " <> render p <> " [circle, draw, fill=white] {" <> label <> "};"
        drawbb (lo, hi) len =
            "\\draw " <>
                render lo <> " -- " <>
                render (translateh len lo) <> " -- " <>
                render (translateh len hi) <> " -- " <>
                render hi <> " -- " <>
                "cycle;"

        drawInner2Cell :: (Reify1 f, Reify1 g) => (f :--> g) -> (Point,Point) -> PointsFor f -> PointsFor g -> Text
        drawInner2Cell Id2 _ ptsf ptsg = T.unlines
            [ mkLine p1 p2 | (_, p1) <- treeToList ptsf | (_, p2) <- treeToList ptsg ]
        drawInner2Cell c@(Labelled2 n) bb@(lo@(Point _ loy), (Point _ hiy)) ptsf ptsg =
            let p = translate 1 ((hiy - loy) / 2) lo
            in
            T.unlines [ mkLine p1 p | (_, p1) <- treeToList ptsf ]
            <> T.unlines [ mkLine p p2 | (_, p2) <- treeToList ptsg ]
            <> drawbb bb (length2Cell c)
            <> mkNode p n
        drawInner2Cell (Cmp2 (c1 :: f :--> h) c2) bb ptsf ptsg =
            let bb1 = translatebb (length2Cell c1 - 0.1) 0 bb
                bb2 = translatebb 0.2 0 bb1
                ptsleft = snd $ genBoundaries c1 bb1
                ptsright = fst $ genBoundaries c2 bb2
            in
            drawInner2Cell c1 bb ptsf ptsleft
            <> drawInner2Cell (Id2 @h) bb1 ptsleft ptsright
            <> drawInner2Cell c2 bb2 ptsright ptsg
            <> T.unlines [ "\\node at " <> render p <> " {" <> T.pack n <> "};" | (n, p) <- treeToList ptsleft ]
        drawInner2Cell (Tensor2 c1 c2) (lo, hi) ptsf ptsg =
            let mid = translatev (width2Cell c2) lo
                (ptsf1, ptsf2) = splitTree1 ptsf
                (ptsg1, ptsg2) = splitTree1 ptsg
            in
            drawInner2Cell c2 (lo, mid) ptsf2 ptsg2
            <> drawInner2Cell c1 (mid, hi) ptsf1 ptsg1



-- \begin{tikzpicture}[scale=0.5]
-- \path
--     coordinate[dot, label=right:$\eta$] (eta)
--     ++(1,1) coordinate[label=right:$a$] (a)
--     ++(1,1) coordinate[dot, label=left:$\epsilon$] (epsilon)
--     ++(-1,1) coordinate[label=right:$b$] (b)
--     ++(-2,0) coordinate[label=left:$\icol{x\\I}$] (br)
--     (eta) ++(1,-1) coordinate[label=right:$c$] (c)
--     ++(2,0) coordinate[label=right:$tl$] (tl);
-- \draw (tl) -- (c) to[out=180, in=-90] (eta) to[out=90, in=180] (a) to[out=0, in=-90] (epsilon) to[out=90, in=0] (b) -- (br);
-- \begin{pgfonlayer}{background}
-- \fill[catc] (tl) -- (c) -- ++(0,-1) -- ++(2,0) -- cycle;
-- \fill[catd] (tl) -- (c) -- ++(0,1) -- ++(2,0) -- cycle;

-- \fill[catc] (c) -- (a) -- ++(0,1) -- ++(-2,0) -- ++(0,-4) -- ++(2,0) -- cycle;
-- \fill[catd] (c) to[out=180, in=-90] (eta) to[out=90, in=180] (a) -- cycle;

-- \fill[catd] (a) -- (b) -- ++(0,1) -- ++(2,0) -- ++(0,-4) -- ++(-2,0) -- cycle;
-- \fill[catc] (a) to[out=0, in=-90] (epsilon) to[out=90, in=0] (b) -- cycle;
-- \end{pgfonlayer}
-- \end{tikzpicture}
