let () =
  let acc = ref 1 in
  for i = 1 to 20 do
    acc := !acc * i
  done;
  Printf.printf "%d\n" !acc
