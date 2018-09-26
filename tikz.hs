{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, LambdaCase, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds #-}
import GHC.TypeLits
import Data.List (intersperse)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

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
        raw $ draw2Cell $
            (Id2 @G) `Tensor2`
            ((Labelled2 "$\\alpha$" :: (F `Cmp1` F) :--> F)
            `Cmp2` (Labelled2 "$\\beta$" :: F :--> (G `Cmp1` H `Cmp1` H))
            `Cmp2` ((Labelled2 "$\\gamma$" :: (G `Cmp1` H) :--> F) `Tensor2` (Labelled2 "$\\delta$" :: H :--> Id1))
            `Tensor2` (Id2 @G))
            `Cmp2` (Labelled2 "$\\lambda$" :: (G `Cmp1` (F `Cmp1` Id1 `Cmp1` G)) :--> (G `Cmp1` F `Cmp1` G))
            `Cmp2` (Id2 `Tensor2` (Labelled2 "$\\eta$" :: F :--> Id1) `Tensor2` Id2)
            `Cmp2` (Labelled2 "$\\mu$" :: (G `Cmp1` Id1 `Cmp1` G) :--> Id1)
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

-- data A0Cell = M | C | D

-- data (a::A0Cell) :-> (b::A0Cell) where
--     Labelled1 :: Text -> (a :-> b)
--     Id1 :: a :-> a
--     Cmp1 :: (b :-> c) -> (a :-> b) -> (a :-> c)

data A1Cell = Labelled1 Symbol | Id1 | Cmp1 A1Cell A1Cell
type F = Labelled1 "$F$"
type G = Labelled1 "$G$"
type H = Labelled1 "$H$"

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

data Tree1 a (f :: A1Cell) where
    TreeL :: KnownSymbol s => Proxy s -> a -> Tree1 a (Labelled1 s)
    TreeId :: Tree1 a Id1
    TreeCmp :: (Reify1 f, Reify1 g) => Tree1 a f -> Tree1 a g -> Tree1 a (Cmp1 f g)

treeToList :: Tree1 a f -> [(String, a)]
treeToList TreeId = []
treeToList (TreeL n x) = [(symbolVal n, x)]
treeToList (TreeCmp t1 t2) = treeToList t1 ++ treeToList t2

class Reify1 (f :: A1Cell) where
    reify1 :: Tree1 () f
instance KnownSymbol s => Reify1 (Labelled1 s) where
    reify1 = TreeL Proxy ()
instance Reify1 Id1 where
    reify1 = TreeId
instance forall f g. (Reify1 f, Reify1 g) => Reify1 (Cmp1 f g) where
    reify1 = TreeCmp (reify1 @f) (reify1 @g)

type PointsFor f = Tree1 Point f

generatePoints :: Reify1 f => Point -> (Point -> Point) -> PointsFor f
generatePoints init next = snd $ aux init
    where
        aux :: forall f. Reify1 f => Point -> (Point, PointsFor f)
        aux e = case reify1 @f of
            TreeL n () -> (next e, TreeL n e)
            TreeId -> (e, TreeId)
            TreeCmp (t1 :: Tree1 () g) (t2 :: Tree1 () h) ->
                let (new, t1') = aux @g e
                    (new', t2') = aux @h new
                in (new', TreeCmp t1' t2')

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
        drawInner2Cell (Tensor2 c1 c2) p0 (TreeCmp ptsf1 ptsf2) (TreeCmp ptsg1 ptsg2) =
            let p1 = translatev (width2Cell c1) p0
            in
            drawInner2Cell c1 p0 ptsf1 ptsg1
            <> drawInner2Cell c2 p1 ptsf2 ptsg2



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
