(* listfold: build the list [1..N], double each element (map), then fold it to a sum. Mirrors
   listfold_int.bl; the result is sum_{i=1..N} 2*i = N*(N+1) = 100010000 for N = 10000 (shared golden).
   Allocates two N-element lists to exercise a linear (list-shaped) allocation pattern. *)

let () =
  let xs = List.init 10000 (fun i -> i + 1) in
  let ys = List.map (fun x -> x * 2) xs in
  let s = List.fold_left ( + ) 0 ys in
  Printf.printf "%d\n" s
