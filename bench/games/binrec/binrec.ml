(* binrec: count the nodes of a perfect binary tree of height d without building it, by naive binary
   recursion t(d) = 1 + t(d-1) + t(d-1) = 2^(d+1) - 1. Mirrors binrec_int.bl; with d = 21 the result
   is 4194303 (shared golden). A pure recursion-overhead / arithmetic compute benchmark (~2^22 calls). *)

let rec nodes d = if d = 0 then 1 else 1 + nodes (d - 1) + nodes (d - 1)

let () = Printf.printf "%d\n" (nodes 21)
