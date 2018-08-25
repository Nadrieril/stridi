{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, LambdaCase, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType #-}
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
            (Id2 @F) `Tensor2` ((Id2 @G `Tensor2` x `Tensor2` Id2 @G) `Cmp2` mu)
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

data Tree1 a (f :: [Symbol]) where
    TreeNil :: Tree1 a Id1
    TreeCons :: (Reify1 f, KnownSymbol s) => Proxy s -> a -> Tree1 a f -> Tree1 a (s ': f)

treeToList :: Tree1 a f -> [(String, a)]
treeToList TreeNil = []
treeToList (TreeCons n x q) = (symbolVal n, x) : treeToList q

class Reify1 (f :: [Symbol]) where
    reify1 :: Tree1 () f
instance Reify1 '[] where
    reify1 = TreeNil
instance (KnownSymbol s, Reify1 f) => Reify1 (s ': f) where
    reify1 = TreeCons Proxy () (reify1 @f)

splitTree1 :: forall f g a. Reify1 f => Tree1 a (f `Cmp1` g) -> (Tree1 a f, Tree1 a g)
splitTree1 t = case (reify1 @f, t) of
    (TreeNil, t) -> (TreeNil, t)
    (TreeCons _ () _, TreeCons n x q) ->
        let (q', q'') = splitTree1 q
        in (TreeCons n x q', q'')

type PointsFor f = Tree1 Point f

generatePoints :: Reify1 f => Point -> (Point -> Point) -> PointsFor f
generatePoints init next = snd $ aux init
    where
        aux :: forall f. Reify1 f => Point -> (Point, PointsFor f)
        aux e = case reify1 @f of
            TreeNil -> (e, TreeNil)
            TreeCons n () (q :: Tree1 () g) ->
                let (new, q') = aux @g e
                in (next new, TreeCons n new q')

draw2Cell :: (Reify1 f, Reify1 g) => (f :--> g) -> Text
draw2Cell c =
    drawInner2Cell c p0 ptsf ptsg
        <> T.unlines [ mkLabel p "east" (T.pack n) | (n, p) <- treeToList ptsf ]
        <> T.unlines [ mkLabel p "west" (T.pack n) | (n, p) <- treeToList ptsg ]
    where
        p0 = Point 0 0
        ptsf = generatePoints (translate 0 0.5 p0) (translatev 1)
        ptsg = generatePoints (translate (length2Cell c) 0.5 p0) (translatev 1)

        mkLine p1 p2 = "\\draw " <> render p1 <> " to[out=0, in=180] " <> render p2 <> ";"
        mkLabel p anchor label = "\\node at " <> render p <> " [anchor=" <> anchor <> "] {" <> label <> "};"
        mkNode p label = "\\node at " <> render p <> " [circle, draw, fill=white] {" <> label <> "};"

        drawInner2Cell :: (Reify1 f, Reify1 g) => (f :--> g) -> Point -> PointsFor f -> PointsFor g -> Text
        drawInner2Cell Id2 _ ptsf ptsg = T.unlines
            [ mkLine p1 p2 | (_, p1) <- treeToList ptsf | (_, p2) <- treeToList ptsg ]
        drawInner2Cell c@(Labelled2 n) p0 ptsf ptsg =
            let p = translate 1 (width2Cell c / 2) p0
            in
            T.unlines [ mkLine p1 p | (_, p1) <- treeToList ptsf ]
            <> T.unlines [ mkLine p p2 | (_, p2) <- treeToList ptsg ]
            <> mkNode p n
        drawInner2Cell (Cmp2 c1 c2) p0 ptsf ptsg =
            let p1 = translateh (length2Cell c1) p0
                ptsh = generatePoints (translate (length2Cell c1) 0.5 p0) (translatev 1)
            in
            drawInner2Cell c1 p0 ptsf ptsh
            <> drawInner2Cell c2 p1 ptsh ptsg
            <> T.unlines [ "\\node at " <> render p <> " {" <> T.pack n <> "};" | (n, p) <- treeToList ptsh ]
        drawInner2Cell (Tensor2 c1 c2) p0 ptsf ptsg =
            let p1 = translatev (width2Cell c2) p0
                (ptsf1, ptsf2) = splitTree1 ptsf
                (ptsg1, ptsg2) = splitTree1 ptsg
            in
            drawInner2Cell c2 p0 ptsf2 ptsg2
            <> drawInner2Cell c1 p1 ptsf1 ptsg1



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
