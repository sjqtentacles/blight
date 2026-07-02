-- treesum: build a full binary tree of depth 20 (each internal node labeled 1) and sum every node
-- label. Mirrors treesum_int.bl; leaves contribute 0 so the sum is the internal-node count
-- 2^20 - 1 = 1048575 (shared golden). Allocates ~2^21 nodes to stress the allocator/GC.

data Tree = Leaf | Node Tree Int Tree

build :: Int -> Tree
build 0 = Leaf
build d = Node (build (d - 1)) 1 (build (d - 1))

treeSum :: Tree -> Int
treeSum Leaf = 0
treeSum (Node l x r) = treeSum l + x + treeSum r

main :: IO ()
main = print (treeSum (build 20))
