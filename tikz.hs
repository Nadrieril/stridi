{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, LambdaCase, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, FlexibleContexts,
    RecordWildCards, AllowAmbiguousTypes #-}
import GHC.TypeLits
import Data.List (intersperse)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Promotion.Prelude.List
import Data.Proxy
import Control.Monad.State.Strict
import Control.Monad.Writer.Class
import Control.Monad.RWS.Strict
import Control.Exception.Base (assert)
import Debug.Trace

import Text.LaTeX hiding (In)
import Text.LaTeX.Packages.TikZ
import Text.LaTeX.Base.Syntax hiding (In)
import Text.LaTeX.Base.Class

evalRWS' :: r -> s -> RWS r w s a -> w
evalRWS' r s rws = snd $ evalRWS rws r s

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
    Tensor2 :: (Reify1 f, Reify1 g, Reify1 f', Reify1 g') =>
        (f :--> g) -> (f' :--> g') -> (Cmp1 f f' :--> Cmp1 g g')

flip2Cell :: f :--> g -> g :--> f
flip2Cell Id2 = Id2
flip2Cell (Labelled2 n) = Labelled2 (n <> "'")
flip2Cell (Cmp2 c1 c2) = Cmp2 (flip2Cell c2) (flip2Cell c1)
flip2Cell (Tensor2 c1 c2) = Tensor2 (flip2Cell c1) (flip2Cell c2)


class Reify1 (f :: [Symbol]) where
    reify1 :: [String]
instance Reify1 '[] where
    reify1 = []
instance (KnownSymbol s, Reify1 f) => Reify1 (s ': f) where
    reify1 = symbolVal (Proxy @s) : reify1 @f

width1Cell :: forall f. Reify1 f => Int
width1Cell = length $ reify1 @f

type OneCellRep = [Text]

oneCellRep :: forall f. Reify1 f => OneCellRep
oneCellRep = fmap T.pack $ reify1 @f


mkLine a1 a2 p1 p2 = "\\draw " <> render p1 <> " to[out=" <> a1 <> ", in=" <> a2 <> "] " <> render p2 <> ";\n"
mkLabel p anchor label = "\\node at " <> render p <> " [anchor=" <> anchor <> "] {" <> label <> "};\n"
mkNode p label = "\\node at " <> render p <> " [circle, draw, fill=white] {" <> label <> "};\n"

draw2Cell :: (Reify1 f, Reify1 g) => (f :--> g) -> Text
draw2Cell = drawLO2C (Point 0 0) . layOut2Cell . twoCellToCanonForm


data TwoCellAtom = TwoCellAtom {
    before :: Int,
    after :: Int,
    inputs :: Int,
    outputs :: Int,
    inRep :: OneCellRep,
    outRep :: OneCellRep,
    label :: Text
}

totalInputs :: TwoCellAtom -> Int
totalInputs TwoCellAtom{..} = before + inputs + after

totalOutputs :: TwoCellAtom -> Int
totalOutputs TwoCellAtom{..} = before + outputs + after

flip2CellAtom :: TwoCellAtom -> TwoCellAtom
flip2CellAtom ca@TwoCellAtom{..} = ca { inputs = outputs, outputs = inputs }


type TwoCellCanonForm = [TwoCellAtom]

tensorCanonForm :: Int -> Int -> TwoCellCanonForm -> TwoCellCanonForm
tensorCanonForm nbefore nafter = fmap (\ca -> ca {
    before = before ca + nbefore,
    after = after ca + nafter
})

twoCellToCanonForm :: forall f g. (Reify1 f, Reify1 g) => f :--> g -> TwoCellCanonForm
twoCellToCanonForm Id2 = twoCellToCanonForm (Labelled2 "id" :: f :--> f)
twoCellToCanonForm (Labelled2 n) = [TwoCellAtom {
        before = 0,
        after = 0,
        inputs = width1Cell @f,
        outputs = width1Cell @g,
        inRep = oneCellRep @f,
        outRep = oneCellRep @g,
        label = n
    }]
twoCellToCanonForm (Cmp2 c1 c2) = (twoCellToCanonForm c1) ++ (twoCellToCanonForm c2)
twoCellToCanonForm (Tensor2 (c1 :: f' :--> g') (c2 :: f'' :--> g'')) =
    (tensorCanonForm 0 (width1Cell @f'') $ twoCellToCanonForm c1)
    ++ (tensorCanonForm (width1Cell @g') 0 $ twoCellToCanonForm c2)

twoCellLength :: Rational
twoCellLength = 1

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


type TwoCellBoundary = [Rational]

baseWidth :: Rational
baseWidth = 1

defaultBoundary :: Int -> TwoCellBoundary
defaultBoundary n = replicate (n+1) baseWidth

backpropBoundary :: TwoCellAtom -> TwoCellBoundary -> TwoCellBoundary
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
    in bdybefore ++ newmid ++ bdyafter

projectBdyL :: TwoCellAtom -> TwoCellBoundary ->
        ([Rational], Either Rational (Rational, [Rational], Rational), [Rational])
projectBdyL = projectBdyR . flip2CellAtom

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


type BdyDelta = (Int, Rational)

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

backpropDelta :: TwoCellAtom -> TwoCellBoundary -> [BdyDelta]
backpropDelta TwoCellAtom{..} bdy = let
        h = sum $ take (outputs+1) $ drop before bdy
        newh = realToFrac (inputs+1) * baseWidth
     in if newh > h
        then [(before, (newh - h)/2), (before + outputs, (newh - h)/2)]
        else []


data LayedOut2Cell =
    NilLO2C TwoCellBoundary
      | ConsLO2C TwoCellBoundary TwoCellAtom LayedOut2Cell

makeEmptyLO2C :: Int -> LayedOut2Cell
makeEmptyLO2C n = NilLO2C $ defaultBoundary n

headLO2C :: LayedOut2Cell -> TwoCellBoundary
headLO2C (NilLO2C bdy) = bdy
headLO2C (ConsLO2C bdy _ _) = bdy

tailLO2C :: LayedOut2Cell -> TwoCellBoundary
tailLO2C (NilLO2C bdy) = bdy
tailLO2C (ConsLO2C _ _ q) = tailLO2C q

iterLO2C :: LayedOut2Cell -> [(TwoCellBoundary, TwoCellAtom, TwoCellBoundary)]
iterLO2C (NilLO2C bdy) = []
iterLO2C (ConsLO2C bdy atom (NilLO2C bdy')) = [(bdy, atom, bdy')]
iterLO2C (ConsLO2C bdy atom q@(ConsLO2C bdy' _ _)) = (bdy, atom, bdy') : iterLO2C q

layOut2Cell :: TwoCellCanonForm -> LayedOut2Cell
layOut2Cell c = propagateDeltasLO2C [] $ foldr pushAtomLO2C initLOC c
    where
        initLOC = makeEmptyLO2C (totalOutputs (last c))

        propagateDeltasLO2C :: [BdyDelta] -> LayedOut2Cell -> LayedOut2Cell
        propagateDeltasLO2C deltas (NilLO2C bdy) = NilLO2C $ foldr applyDelta bdy deltas
        propagateDeltasLO2C deltas (ConsLO2C bdy atom q) = ConsLO2C newbdy atom $ propagateDeltasLO2C newdeltas q
            where
                newbdy = foldr applyDelta bdy deltas
                newdeltas = concatMap (propagateDelta atom) deltas ++ backpropDelta atom (headLO2C q)

        pushAtomLO2C :: TwoCellAtom -> LayedOut2Cell -> LayedOut2Cell
        pushAtomLO2C atom c =
            let bdy = backpropBoundary atom (headLO2C c)
             in ConsLO2C bdy atom c

drawLO2C :: Point -> LayedOut2Cell -> Text
drawLO2C p c = evalRWS' () p $ forM_ (iterLO2C c) $
        \(bdyl, atom, bdyr) -> do
            p <- get
            tell $ draw2CellAtom p bdyl bdyr atom
            put (translateh twoCellLength p)
       -- <> T.unlines [ mkLabel p "east" (T.pack n) | (n, p) <- headLO2C c ]
       -- <> T.unlines [ mkLabel p "west" (T.pack n) | (n, p) <- tailLO2C c ]

