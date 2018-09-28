#!/usr/bin/env stack
-- stack --resolver lts-12.7 script --package shake
import Development.Shake
import Development.Shake.FilePath

opts = shakeOptions {
      shakeThreads = 0
    , shakeColor = True
}

main = shakeArgs opts $ do
    let buildDir = ".shake/cache"
    want ["test.pdf"]

    "*.pdf" %> \outputFile -> do
        let texFile = buildDir </> outputFile -<.> "tex"
        need [texFile]
        cmd_ "latexrun -O" [buildDir] "--latex-cmd=xelatex" [texFile]

    buildDir </> "*.tex" %> \outputFile -> do
        let inputFile = takeFileName outputFile -<.> "hs"
        -- TODO: dep on stridi hs files
        need [inputFile]
        Stdout stdout <- cmd "stack runghc --package HaTeX --package singletons --package extra" [inputFile]
        writeFileChanged outputFile stdout

    phony "clean" $ do
        putNormal $ "Cleaning files in " ++ buildDir
        cmd_ "latexrun -O" buildDir "--clean-all"
        removeFilesAfter buildDir ["//*"]
