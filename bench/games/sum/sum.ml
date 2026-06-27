let () =
  let acc = ref 0 in
  for i = 1 to 1000 do
    acc := !acc + i
  done;
  Printf.printf "%d\n" !acc
