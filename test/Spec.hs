import CLPHS.FD
import CLPHS.FD.Domain

main :: IO ()
main = print test

test :: [[Int]]
test = runFD $ do
    x <- new $ range inf sup
    y <- new $ range inf sup
    x #== y + 1
    y #== 1
    label [x,y]


