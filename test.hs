{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}

import Prelude hiding ((*), (**))
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LT
import qualified Data.ByteString.Lazy.Char8   as LB
import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Text.LaTeX hiding (cup, cap, dot, (&), perp)
import Text.LaTeX.Base.Syntax
import Text.LaTeX.Base.Class
import Text.LaTeX.Packages.AMSMath hiding (cup, cap, dot, perp)
import qualified Text.LaTeX as L
import qualified Text.LaTeX.Packages.AMSMath as L
import StriDi.Cells
import StriDi.Render
import StriDi.DSL
import StriDi.DSL.Monoidal
import Diagrams.Backend.PGF.CmdLine
import Diagrams.Backend.PGF.Surface
import Diagrams.Prelude hiding (render)
import Diagrams.TwoD.Vector         (perp)
import Diagrams.TwoD.Size (height)
import Diagrams.Size
import System.Texrunner (runTex)
import System.Texrunner.Online (runOnlineTex, runOnlineTex', texPutStrLn)

type D2 = Diagram PGF

diagram :: OnlineTex D2
diagram = do
    txt <- mkNode "default"
    return txt

-- Draw the given text in a box
mkNode :: String -> OnlineTex D2
mkNode str = do
    txt <- hboxOnline str
    -- By default, tikz adds an inner padding of 1/3em to rectangles around text
    -- For now I assume the height is 1em. This isn't very good.
    let h = height txt
        inner_sep = h/3
    txt <- return $ txt # frame inner_sep
    -- Default tikz line thickness is 0.4pt (called thin).
    -- Seems to correspond with default diagrams line thickness too
    return $ (txt <> boundingRect txt)


-- Draw an arrow with a horizontal label above or below.
labeledArrow :: Bool -> String -> V2 Double -> OnlineTex D2
labeledArrow above label r = diaArrow <$> hboxOnline label
  where
    diaArrow txt = atDirection ((direction . rev . perp) r)
                               (arr # translate (negated $ r^/2))
                               (txt # centerXY # scale 0.1 # frame 0.3)
                               # translate (r^/2)
      where
        rev = if above then id else negated
        arr = arrowV' ops r
        ops = with & arrowHead .~ spike
                   & arrowTail .~ spike'
                   & lengths   .~ normalized 0.015


-- Manually render a pdf for the `diagrams` diagram alongside the rendering of the
-- `stridi` diagram.
-- Normally would only use:
-- main = renderOnlinePGF' "test.pdf" with diagram
main :: IO ()
main = do
    let outFile = "test.pdf"
    ltx <- execLaTeXT body
    ltx <- return $ render ltx
    -- (_, texLog, mPDF) <- runTex "pdflatex" [] [] $ LT.encodeUtf8 $ LT.fromStrict ltx
    let opts = with & surface.preamble .~ (unlines [
                "\\documentclass{article}",
                "\\usepackage{pgfcore}",
                "\\pagenumbering{gobble}",
                "\\usepackage{tikz}",
                "\\usepackage{amsmath}",
                "\\usetikzlibrary{decorations.markings, arrows, matrix}"
            ])
        surf = opts ^. surface
        toByteString = LB.toStrict . toLazyByteString

    (_, texLog, mPDF) <-
        runOnlineTex'
            (surf^.command)
            (surf^.arguments)
            "" $ do

            let echo x = do
                    texPutStrLn $ toByteString x
                    liftIO $ T.putStrLn $ T.decodeUtf8 $ toByteString x

            echo $ stringUtf8 $ surf ^. preamble
            echo $ stringUtf8 $ surf ^. beginDoc

            d <- diagram
            let rendered = renderDia PGF opts d
                -- (opts', _, _) = adjustDia PGF opts d
                -- bounds = specToSize 100 (opts'^.sizeSpec)
                -- bounds' = fmap (fromInteger . floor) bounds

            -- maybe (return ())
            --   (texPutStrLn . toByteString . stringUtf8 . ($ fmap ceiling bounds'))
            --   (surf^.pageSize)
            echo rendered
            texPutStrLn $ T.encodeUtf8 ltx
            -- liftIO $ T.putStrLn ltx
            echo $ stringUtf8 $ surf ^. endDoc

    case mPDF of
      Nothing  -> putStrLn "Error, no PDF found:"
               >> print texLog
      Just pdf -> LB.writeFile outFile pdf


draw2c :: LaTeXC l => A2Cell -> l
draw2c = drawA2Cell $ RenderOptions 0.6 0.3

arrowR, arrowL :: [Text]
arrowR = ["postaction={decorate}","decoration={markings, mark=at position 0.5 with {\\arrow[line width=0.2mm]{angle 90}}}"]
arrowL = ["postaction={decorate}","decoration={markings, mark=at position 0.5 with {\\arrow[line width=0.2mm]{angle 90 reversed}}}"]
blackdot :: [Text]
blackdot = ["circle", "draw=black", "fill=black", "minimum size=1mm", "inner sep=0mm"]

p = new1C "P"
q = new1C "Q"
r = new1C "R"
s = new1C "S"
st = new1C "S" ** new1C "T"
ab = new1C "A" ** new1C "B"

mkRepr1C l = (new1COptions l [] arrowR, new1COptions l [] arrowL)
mkRepr2C l (ar,al) (br,bl) = (new2C l ar br , new2C l bl al)

a = new1C "A"
b = new1C "B"
c = new1C "C"
d = new1C "D"

aa@(ar, al) = mkRepr1C "A"
bb@(br, bl) = mkRepr1C "B"
ss@(sr, sl) = mkRepr1C "S"
tt@(tr, tl) = mkRepr1C "T"

cup (ar, al) = new2COptions "" [] id1 (al ** ar)
cap (ar, al) = new2COptions "" [] (ar ** al) id1
l = new2C "l" (sr**sl) (ar**al)
fork = new2COptions "" blackdot a (a**a)
cofork = new2COptions "" blackdot (a**a) a
bead = new2COptions "" blackdot a a

body :: LaTeXT IO ()
body = do
    -- raw "\\documentclass{article}"
    -- raw "\\usepackage{tikz}"
    -- raw "\\usepackage{amsmath}"
    -- raw "\\usetikzlibrary{decorations.markings, arrows, matrix}"
    -- raw "\\begin{document}"

    -- lens laws
    draw2c l
    -- draw2c $ l * (id2 ar ** cup aa ** id2 al)
    -- draw2c $ (id2 sr ** cup ss ** id2 sl) * (l ** l)
    -- -- snakes
    -- draw2c $ (id2 ar ** cup aa) * (cap aa ** id2 ar)
    -- draw2c $ (cup aa ** id2 al) * (id2 al ** cap aa)
    -- raw "\\\\"
    -- -- back-to-back
    -- draw2c $ cap aa * cup bb
    -- draw2c $ cap aa ** cup bb
    -- draw2c $ cup bb ** cap aa
    -- raw "\\\\"
    -- draw2c $ fork ** cofork
    -- draw2c $ (id2 a ** cofork) * (fork ** id2 a)
    -- draw2c $ (fork ** id2 a ** id2 a) * (id2 a ** id2 a ** cofork)
    -- draw2c $ (fork ** id2 a) * (id2 a ** cofork)
    -- draw2c $ fork * cofork
    -- raw "\\\\"
    -- draw2c $ cofork ** fork
    -- draw2c $ (cofork ** id2 a) * (id2 a ** fork)
    -- draw2c $ (id2 a ** id2 a ** fork) * (cofork ** id2 a ** id2 a)
    -- draw2c $ (id2 a ** fork) * (cofork ** id2 a)
    -- raw "\\\\"
    -- draw2c $ cofork ** cofork
    -- draw2c $ cofork ** id2 a ** cofork
    -- draw2c $ id2 a ** cofork
    -- draw2c $ cofork ** id2 a
    -- raw "\\\\"
    -- draw2c $ bead * bead
    -- draw2c $ bead ** bead
    -- draw2c $ (bead ** bead) * (bead ** bead)
    -- draw2c $ bead ** bead ** bead
    -- raw "\\\\"
    -- draw2c $ ((fork ** fork) * (id2 a ** cap (a, a) ** id2 a)) * ((fork ** fork) * (id2 a ** cap (a, a) ** id2 a))
    -- draw2c $ (id2 a ** cap (a, a) ** id2 a) * cap (a, a)
    -- draw2c $ cofork * bead
    -- draw2c $ cofork

    -- raw "\\end{document}"

