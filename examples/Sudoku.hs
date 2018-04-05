module Sudoku where

import Control.Monad
import Data.List (transpose)

import ClpHs.FD
import qualified ClpHs.Domain as Domain

type Sudoku = [Int]

test :: Sudoku
test = [
    0, 0, 0, 0, 8, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 6, 5, 0, 7,
    4, 0, 2, 7, 0, 0, 0, 0, 0,
    0, 8, 0, 3, 0, 0, 1, 0, 0,
    0, 0, 3, 0, 0, 0, 8, 0, 0,
    0, 0, 5, 0, 0, 9, 0, 7, 0,
    0, 5, 0, 0, 0, 8, 0, 0, 6,
    3, 0, 1, 2, 0, 4, 0, 0, 0,
    0, 0, 6, 0, 1, 0, 0, 0, 0 ]

displayPuzzle :: Sudoku -> String
displayPuzzle = unlines . map show . chunk 9

printSudoku :: Sudoku -> IO ()
printSudoku = putStr . unlines . map displayPuzzle . sudoku

sudoku :: Sudoku -> [Sudoku]
sudoku puzzle = runFD $ do
    vs <- news 81 $ (Domain.range 1 9)
    zipWithM_ (\v n -> when (n > 0) (v #== int n)) vs puzzle
    mapM_ allDifferent (rows vs)
    mapM_ allDifferent (columns vs)
    mapM_ allDifferent (boxes vs)
    label vs

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk n xs = ys : chunk n zs where
    (ys, zs) = splitAt n xs

rows :: [a] -> [[a]]
rows = chunk 9

columns :: [a] -> [[a]]
columns = transpose . rows

boxes :: [a] -> [[a]]
boxes = concatMap (map concat . transpose) . chunk 3 . chunk 3 . chunk 3