#!/usr/bin/env stack
-- stack --resolver lts-14.7 script --package shake
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
        alwaysRerun
        let inputFile = buildDir </> outputFile
        copyFileChanged inputFile outputFile

    buildDir </> "*.pdf" %> \outputFile -> do
        alwaysRerun
        let texFile = outputFile -<.> "tex"
        need [texFile]
        cmd_ "pdflatex -interaction nonstopmode -output-directory" [buildDir] [texFile]

    buildDir </> "*.tex" %> \outputFile -> do
        alwaysRerun
        let inputFile = takeFileName outputFile -<.> "hs"
        -- TODO: dep on stridi hs files
        need [inputFile]
        Stdout stdout <- cmd "stack test"
        writeFileChanged outputFile stdout

    phony "clean" $ do
        alwaysRerun
        putNormal $ "Cleaning files in " ++ buildDir
        removeFilesAfter buildDir ["//*"]
