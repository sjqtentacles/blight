let () =
  let a = ref 0 and b = ref 1 in
  for _ = 1 to 30 do
    let next = !a + !b in
    a := !b;
    b := next
  done;
  Printf.printf "%d\n" !a
