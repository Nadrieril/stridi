{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, LambdaCase, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, FlexibleContexts,
    RecordWildCards, AllowAmbiguousTypes, ViewPatterns #-}
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


data Composite f a b where
    NilCte :: Composite f a a
    CmpCte :: f a b -> Composite f b c -> Composite f a c

headComposite :: Composite f a b -> (forall c. f a c -> r) -> r -> r
headComposite NilCte _ x = x
headComposite (CmpCte fab _) f _ = f fab

foldComposite :: (forall a b c. f a b -> r b c -> r a c) -> r b b -> Composite f a b -> r a b
foldComposite _ x NilCte = x
foldComposite f x (CmpCte fab q) = f fab (foldComposite f x q)

mergeComposite :: Composite f a b -> Composite f b c -> Composite f a c
mergeComposite NilCte fbc = fbc
mergeComposite (CmpCte fab q) fbc = CmpCte fab $ mergeComposite q fbc

singComposite :: f a b -> Composite f a b
singComposite fab = CmpCte fab NilCte


data Interleaved f g a b where
    NilIntl :: g a -> Interleaved f g a a
    CmpIntl :: g a -> f a b -> Interleaved f g b c -> Interleaved f g a c

headInterleaved :: Interleaved f g a b -> g a
headInterleaved (NilIntl ga) = ga
headInterleaved (CmpIntl ga _ _) = ga

tailInterleaved :: Interleaved f g a b -> g b
tailInterleaved (NilIntl ga) = ga
tailInterleaved (CmpIntl _ _ q) = tailInterleaved q

iterInterleaved :: Interleaved f g a b -> (forall a b. (g a, f a b, g b) -> r) -> [r]
iterInterleaved (NilIntl ga) f = []
iterInterleaved (CmpIntl ga fab (NilIntl gb)) f = [f (ga, fab, gb)]
iterInterleaved (CmpIntl ga fab q@(CmpIntl gb _ _)) f = f (ga, fab, gb) : iterInterleaved q f

-- scanInterleaved :: (forall a b. (g a, f a b, g' b) -> (g' a, f' a b)) -> (forall a. g a -> g' a)
--                 -> Interleaved f g a b -> Interleaved f' g' a b
-- scanInterleaved map end (NilIntl ga) = NilIntl $ end ga
-- scanInterleaved map end (CmpIntl ga fab q) =
--     let q' = scanInterleaved map end q
--         (ga', fab') = map (ga, fab, headInterleaved q')
--      in CmpIntl ga' fab' q'

interleaveInComposite :: (forall a b c. f a b -> g b -> g a) -> g b -> Composite f a b -> Interleaved f g a b
interleaveInComposite f x = foldComposite (\fab intbc -> CmpIntl (f fab (headInterleaved intbc)) fab intbc) (NilIntl x)



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
                alpha = labelled2 "$\\alpha$" :: (F `Cmp1` F) :--> F
                beta = labelled2 "$\\beta$" :: F :--> (G `Cmp1` H `Cmp1` H)
                gamma = labelled2 "$\\gamma$" :: (G `Cmp1` H) :--> F
                delta = labelled2 "$\\delta$" :: H :--> Id1
                eta = labelled2 "$\\eta$" :: F :--> Id1
                mu = labelled2 "$\\mu$" :: (G `Cmp1` G) :--> Id1
                nu = labelled2 "$\\nu$" :: Id1 :--> (G `Cmp1` G)
                omega = labelled2 "$\\omega$" :: Id1 :--> (F `Cmp1` F)
                epsilon = labelled2 "$\\epsilon$" :: G :--> G
                x = omega
                    `Cmp2` alpha
                    `Cmp2` beta
                    `Cmp2` (gamma `Tensor2` delta)
                    `Cmp2` eta
                        :: Id1 :--> Id1
            in
            (nu `Cmp2`((epsilon `Cmp2` epsilon)
                `Tensor2` x `Tensor2` id2 @G) `Cmp2` mu)
    center $ fromLaTeX $ TeXEnv "tikzpicture" [] $
        raw $ draw2Cell $ let
                beta = labelled2 "$\\beta$" :: F :--> (F `Cmp1` G)
                gamma = labelled2 "$\\gamma$" :: G :--> H
                eta = labelled2 "$\\eta$" :: F :--> Id1
            in beta `Cmp2` (eta `Tensor2` gamma)
    center $ fromLaTeX $ TeXEnv "tikzpicture" [] $
        raw $ draw2Cell $ let
                beta = labelled2 "$\\beta$" :: F :--> (F `Cmp1` G `Cmp1` H)
                gamma = labelled2 "$\\gamma$" :: G :--> F
                delta = labelled2 "$\\delta$" :: H :--> Id1
                eta = labelled2 "$\\eta$" :: F :--> Id1
                omega = labelled2 "$\\omega$" :: Id1 :--> F
                x = beta
                    `Cmp2` (eta `Tensor2` gamma `Tensor2` delta)
                    `Cmp2` eta
            in x
    center $ fromLaTeX $ TeXEnv "tikzpicture" [] $
        raw $ draw2Cell $ let
                beta = labelled2 "$\\beta$" :: F :--> (G `Cmp1` H `Cmp1` H)
                gamma = labelled2 "$\\gamma$" :: (G `Cmp1` H) :--> F
                delta = labelled2 "$\\delta$" :: H :--> Id1
                eta = labelled2 "$\\eta$" :: F :--> Id1
                mu = labelled2 "$\\mu$" :: (G `Cmp1` G) :--> Id1
                nu = labelled2 "$\\nu$" :: Id1 :--> (G `Cmp1` G)
                omega = labelled2 "$\\omega$" :: Id1 :--> F
                x = omega
                    `Cmp2` beta
                    `Cmp2` (gamma `Tensor2` delta)
                    `Cmp2` eta
                        :: Id1 :--> Id1
            in
            (nu `Cmp2` (id2 @G `Tensor2` x `Tensor2` id2 @G) `Cmp2` mu)
    "Another string diagram"
    center $ fromLaTeX $ TeXEnv "tikzpicture" [] $
        raw $ draw2Cell $ let
                alpha = labelled2 "$\\beta$" :: Id1 :--> (F `Cmp1` G)
                beta = labelled2 "$\\alpha$" :: (F `Cmp1` G) :--> Id1
                circle = id2 @H `Tensor2` (alpha `Cmp2` beta) `Tensor2` id2 @H
            in
            circle `Cmp2` (id2 @H `Tensor2` id2 @H) `Cmp2` flip2Cell circle
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


type Sing (f :: [Symbol]) = [Text]

data (f :: A1Cell) :--> (g :: A1Cell) where
    Labelled2 :: Text -> Sing f -> Sing g -> f :--> g
    Id2 :: Sing f -> f :--> f
    Cmp2 :: (f :--> g) -> (g :--> h) -> (f :--> h)
    Tensor2 :: (f :--> g) -> (f' :--> g') -> (Cmp1 f f' :--> Cmp1 g g')

flip2Cell :: f :--> g -> g :--> f
flip2Cell (Id2 sf) = Id2 sf
flip2Cell (Labelled2 n sf sg) = Labelled2 (n <> "'") sg sf
flip2Cell (Cmp2 c1 c2) = Cmp2 (flip2Cell c2) (flip2Cell c1)
flip2Cell (Tensor2 c1 c2) = Tensor2 (flip2Cell c1) (flip2Cell c2)

extractLeftRep :: f :--> g -> Sing f
extractLeftRep (Id2 sf) = sf
extractLeftRep (Labelled2 _ sf _) = sf
extractLeftRep (Cmp2 c1 _) = extractLeftRep c1
extractLeftRep (Tensor2 c1 c2) = let
        r1 = extractLeftRep c1
        r2 = extractLeftRep c2
    in r1 ++ r2

class Reify1 (f :: [Symbol]) where
    reify1 :: Sing f
instance Reify1 '[] where
    reify1 = []
instance (KnownSymbol s, Reify1 f) => Reify1 (s ': f) where
    reify1 = T.pack (symbolVal (Proxy @s)) : reify1 @f

labelled2 :: forall f g. (Reify1 f, Reify1 g) => Text -> f :--> g
labelled2 l = Labelled2 l (reify1 @f) (reify1 @g)

id2 :: forall f. Reify1 f => f :--> f
id2 = Id2 (reify1 @f)



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

-- coerce2CellAtom :: forall f' g' f g. TwoCellAtom f g -> TwoCellAtom f' g'
-- coerce2CellAtom x = x { inputs = inputs x }

tensor2CellAtomL :: forall x f g. Sing x -> TwoCellAtom f g -> TwoCellAtom (x `Cmp1` f) (x `Cmp1` g)
tensor2CellAtomL sx ca = ca {
        before = before ca + length sx
    }

tensor2CellAtomR :: forall x f g. Sing x -> TwoCellAtom f g -> TwoCellAtom (f `Cmp1` x) (g `Cmp1` x)
tensor2CellAtomR sx ca = ca {
        after = after ca + length sx
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


data TwoCellBoundary f = Bdy { unBdy :: [Rational] }

baseWidth :: Rational
baseWidth = 1

defaultBoundary :: Int -> TwoCellBoundary f
defaultBoundary n = Bdy $ replicate (n+1) baseWidth

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
    in Bdy $ bdybefore ++ newmid ++ bdyafter

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
applyDelta (i, delta) (unBdy -> bdy) =
    Bdy $ take i bdy ++ [bdy!!i + delta] ++ drop (i+1) bdy

backpropDelta :: TwoCellAtom f g -> TwoCellBoundary g -> [BdyDelta g]
backpropDelta TwoCellAtom{..} (unBdy -> bdy) = let
        h = sum $ take (outputs+1) $ drop before bdy
        newh = realToFrac (inputs+1) * baseWidth
     in if newh > h
        then [(before, (newh - h)/2), (before + outputs, (newh - h)/2)]
        else []


type LayedOut2Cell = Interleaved TwoCellAtom TwoCellBoundary

layOut2Cell :: TwoCellCanonForm f g -> LayedOut2Cell f g
layOut2Cell c = propagateDeltasLO2C [] $ interleaveInComposite backpropBoundary lastBdy c
    where
        lastBdy :: forall f. TwoCellBoundary f
        lastBdy = defaultBoundary (headComposite c totalOutputs 0)

        applyDeltas :: [BdyDelta f] -> TwoCellBoundary f -> TwoCellBoundary f
        applyDeltas = flip $ foldr applyDelta

        propagateAndAccumulateDeltas :: [BdyDelta f] -> TwoCellAtom f g -> TwoCellBoundary g -> [BdyDelta g]
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
drawLO2C p c = evalRWS' () p $ sequence_ (iterInterleaved c $ \(bdyl, atom, bdyr) -> do
            p <- get
            tell $ draw2CellAtom p bdyl bdyr atom
            put (translateh twoCellLength p)
        )
       -- <> T.unlines [ mkLabel p "east" (T.pack n) | (n, p) <- headInterleaved c ]
       -- <> T.unlines [ mkLabel p "west" (T.pack n) | (n, p) <- tailInterleaved c ]

