{-# LANGUAGE OverloadedStrings, DataKinds, KindSignatures, TypeOperators, GADTs, LambdaCase, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, FlexibleContexts,
    RecordWildCards, AllowAmbiguousTypes, ViewPatterns #-}

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Text.LaTeX
import Text.LaTeX.Base.Syntax
import Text.LaTeX.Base.Class

import Stridi.Render

main :: IO ()
main = execLaTeXT theBody >>= TIO.putStrLn . render

type F = '["$F$"]
type G = '["$G$"]
type H = '["$H$"]

theBody :: LaTeXT IO ()
theBody = do
    "A string diagram"
    center $ fromLaTeX $ TeXEnv "tikzpicture" [OptArg "scale=0.5"] $ raw $ T.unlines
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
                mu = labelled2 "$\\mu$" :: (G `Cmp1` G) :--> H
                nu = labelled2 "$\\nu$" :: H :--> (G `Cmp1` G)
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
                beta = labelled2 "$\\beta$" :: (F `Cmp1` F) :--> (F `Cmp1` G)
                gamma = labelled2 "$\\gamma$" :: G :--> (G `Cmp1` G `Cmp1` G `Cmp1` H)
                eta = labelled2 "$\\eta$" :: F :--> (F `Cmp1` F `Cmp1` F)
                pi = labelled2 "$\\pi$" :: F :--> (F `Cmp1` F)
                rho = labelled2 "$\\rho$" :: (F `Cmp1` F) :--> Id1
            in beta `Cmp2` ((eta `Cmp2` (id2 @F `Tensor2` (pi `Cmp2` rho) `Tensor2` id2 @F)) `Tensor2` gamma)
    center $ fromLaTeX $ TeXEnv "tikzpicture" [] $
        raw $ draw2Cell $ let
                beta = labelled2 "$\\beta$" :: (F `Cmp1` G `Cmp1` H) :--> (F `Cmp1` G `Cmp1` H)
                gamma = labelled2 "$\\gamma$" :: G :--> F
                delta = labelled2 "$\\delta$" :: H :--> H
                eta = labelled2 "$\\eta$" :: F :--> G
            in beta `Cmp2` (eta `Tensor2` (gamma `Cmp2` eta) `Tensor2` delta)
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
