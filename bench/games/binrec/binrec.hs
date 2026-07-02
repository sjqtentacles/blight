-- binrec: count the nodes of a perfect binary tree of height d without building it, by naive binary
-- recursion t(d) = 1 + t(d-1) + t(d-1) = 2^(d+1) - 1. Mirrors binrec_int.bl; with d = 21 the result
-- is 4194303 (shared golden). A pure recursion-overhead / arithmetic compute benchmark (~2^22 calls).

nodes :: Int -> Int
nodes 0 = 1
nodes d = 1 + nodes (d - 1) + nodes (d - 1)

main :: IO ()
main = print (nodes 21)
