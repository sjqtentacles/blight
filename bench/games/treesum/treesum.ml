(* treesum: build a full binary tree of depth 20 (each internal node labeled 1) and sum every node
   label. Mirrors treesum_int.bl; leaves contribute 0 so the sum is the internal-node count
   2^20 - 1 = 1048575 (shared golden). Allocates ~2^21 nodes to stress the allocator/GC. *)

type tree = Leaf | Node of tree * int * tree

let rec build depth =
  if depth = 0 then Leaf
  else Node (build (depth - 1), 1, build (depth - 1))

let rec tree_sum = function
  | Leaf -> 0
  | Node (l, x, r) -> tree_sum l + x + tree_sum r

let () =
  let t = build 20 in
  Printf.printf "%d\n" (tree_sum t)
