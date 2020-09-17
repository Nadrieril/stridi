{-# LANGUAGE OverloadedStrings #-}

import Prelude hiding ((*), (**))
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Text.LaTeX hiding (cup, cap, dot)
import Text.LaTeX.Base.Syntax
import Text.LaTeX.Base.Class
import Text.LaTeX.Packages.AMSMath hiding (cup, cap, dot)
import qualified Text.LaTeX as L
import qualified Text.LaTeX.Packages.AMSMath as L
import StriDi.Cells
import StriDi.Render
import StriDi.DSL
import StriDi.DSL.Monoidal

main :: IO ()
main = execLaTeXT body >>= T.putStrLn . render

draw2c :: LaTeXC l => A2Cell -> l
draw2c = drawA2Cell $ RenderOptions 0.6 0.3

arrowR, arrowL :: [Text]
arrowR = ["postaction={decorate}","decoration={markings, mark=at position 0.5 with {\\arrow[line width=0.2mm]{angle 90}}}"]
arrowL = ["postaction={decorate}","decoration={markings, mark=at position 0.5 with {\\arrow[line width=0.2mm]{angle 90 reversed}}}"]
dot :: [Text]
dot = ["circle", "draw=black", "fill=black", "minimum size=1mm", "inner sep=0mm"]

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
fork = new2COptions "" dot a (a**a)
cofork = new2COptions "" dot (a**a) a
bead = new2COptions "" dot a a

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
