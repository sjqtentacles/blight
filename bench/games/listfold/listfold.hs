-- listfold: build the list [1..N], map (*2), then fold-sum it. Mirrors listfold_int.bl; the result is
-- sum_{i=1..N} 2*i = N*(N+1) = 100010000 for N = 10000 (shared golden). A linear (list-shaped)
-- traversal/allocation pattern (GHC may fuse the intermediate list, which is idiomatic).

main :: IO ()
main = print (sum (map (* 2) [1 .. 10000 :: Int]))
