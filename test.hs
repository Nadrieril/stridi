{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}

import Prelude hiding ((*), (**))
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LT
import qualified Data.ByteString.Lazy.Char8   as LB
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
import Diagrams.Prelude hiding (render)
import Diagrams.TwoD.Vector         (perp)
import Diagrams.Size
import System.Texrunner (runTex)

main :: IO ()
main = do
    let outFile = "test.pdf"
    ltx <- execLaTeXT body
    ltx <- return $ render ltx
    (_, texLog, mPDF) <- runTex "pdflatex" [] [] $ LT.encodeUtf8 $ LT.fromStrict ltx
    case mPDF of
      Nothing  -> putStrLn "Error, no PDF found:"
               >> print texLog
      Just pdf -> LB.writeFile outFile pdf
-- main = renderOnlinePGF' "test.pdf" with example

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
    raw "\\documentclass{article}"
    raw "\\usepackage{tikz}"
    raw "\\usepackage{amsmath}"
    raw "\\usetikzlibrary{decorations.markings, arrows, matrix}"
    raw "\\begin{document}"

    -- lens laws
    draw2c $ l * (id2 ar ** cup aa ** id2 al)
    draw2c $ (id2 sr ** cup ss ** id2 sl) * (l ** l)
    -- snakes
    draw2c $ (id2 ar ** cup aa) * (cap aa ** id2 ar)
    draw2c $ (cup aa ** id2 al) * (id2 al ** cap aa)
    raw "\\\\"
    -- back-to-back
    draw2c $ cap aa * cup bb
    draw2c $ cap aa ** cup bb
    draw2c $ cup bb ** cap aa
    raw "\\\\"
    draw2c $ fork ** cofork
    draw2c $ (id2 a ** cofork) * (fork ** id2 a)
    draw2c $ (fork ** id2 a ** id2 a) * (id2 a ** id2 a ** cofork)
    draw2c $ (fork ** id2 a) * (id2 a ** cofork)
    draw2c $ fork * cofork
    raw "\\\\"
    draw2c $ cofork ** fork
    draw2c $ (cofork ** id2 a) * (id2 a ** fork)
    draw2c $ (id2 a ** id2 a ** fork) * (cofork ** id2 a ** id2 a)
    draw2c $ (id2 a ** fork) * (cofork ** id2 a)
    raw "\\\\"
    draw2c $ cofork ** cofork
    draw2c $ cofork ** id2 a ** cofork
    draw2c $ id2 a ** cofork
    draw2c $ cofork ** id2 a
    raw "\\\\"
    draw2c $ bead * bead
    draw2c $ bead ** bead
    draw2c $ (bead ** bead) * (bead ** bead)
    draw2c $ bead ** bead ** bead
    raw "\\\\"
    draw2c $ ((fork ** fork) * (id2 a ** cap (a, a) ** id2 a)) * ((fork ** fork) * (id2 a ** cap (a, a) ** id2 a))
    draw2c $ (id2 a ** cap (a, a) ** id2 a) * cap (a, a)
    draw2c $ cofork * bead
    draw2c $ cofork

    raw "\\end{document}"


type D2 = Diagram PGF


example :: OnlineTex D2
example = frame 5 . scale 10 <$> do
    txt <- hboxOnline "$lkj \\otimes \\TeX$"
    return txt

-- Use the envelope from the hbox to label the width, height and depth.
hboxLines :: String -> OnlineTex D2
hboxLines str = do
  txt <- hboxOnline str

  let h = envelopeV unitY txt
      d = envelopeV unit_Y txt
      w = envelopeV unitX txt

  -- hArrow <- labeledArrow False "height" h
  -- dArrow <- labeledArrow True "depth" d
  -- wArrow <- labeledArrow False "width" w

  return txt
  -- return $ (txt <> boundingRect txt <> fromOffsets [w])
  --          ||| strutX 1 ||| (hArrow === dArrow)
  --          === strutY 1
  --          === wArrow

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
