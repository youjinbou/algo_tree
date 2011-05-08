
let _ = Random.init (int_of_float (Unix.time ()))


let dump_data = false

let min = 0
let max = 80000

let count = 999

let dotty_folder = "dots"

(* randomize the order of an array content *)
let randomize_order a size =
  for i = 0 to (size-1) do
    let x = Random.int (size-1)
    and y = Random.int (size-1)
    in
    let z = a.(x) 
    in
      a.(x) <- a.(y); a.(y) <- z
  done
