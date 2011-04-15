(* sample application conducting tests on the trees *)

let max      = 1000000

type tree_kind_t = MBtree | MRbtree_f | MRbtree_i

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

let t_kind = MBtree


module BTC = 
struct
  type key_t = int
  type value_t = int
  let compare k1 k2 = if k1 < k2 then -1 else if k1 > k2 then 1 else 0
  let max = 4
  let string_of_key = string_of_int
end

module BTCf =
struct
  type key_t = int
  type 'a t = (key_t * 'a)
  let make k v : 'a t  = (k,v)
  let get_key x = fst x
  let compare k1 k2 = if k1 < k2 then -1 else if k1 > k2 then 1 else 0
  let string_of_key = string_of_int
end

(* Btree ----------------------------------------------------------- *)

module IBt = Btree.Mutable.Make(BTC)

(* B+tree ---------------------------------------------------------- *)

(* module IBpt = Bptree.Make(BTC) *)
 
(* Red Black tree -------------------------------------------------- *)

module IBf = Rbtree.Make(BTCf)

module BTCi =
struct
  type key_t        = int
  type t            = (key_t * int)
  let get_key x     = fst x
  let compare k1 k2 = if k1 < k2 then -1 else if k1 > k2 then 1 else 0
  let string_of_key = string_of_int
end
 
module IBi = Rbtree_imp.Make(BTCi)

(* ----------------------------------------------------------------- *)

let _ = 
  let checkarray = Array.make (max) 0
  in
    for i = 0 to (max-1) do
      checkarray.(i) <- i
    done;

    randomize_order checkarray max;

  match t_kind with
      MBtree -> (
	let t = IBt.create ()
	in 
	for i = 1 to max do
	  let x = checkarray.(i-1) in
	  IBt.add t x x
	done;
	for i = 1 to max do
	  let x = checkarray.(i-1) in
          ignore (IBt.remove t x)
	done
      )
    | MRbtree_f -> (
      let t : int IBf.t = IBf.create ()
      in
      let rec addv t i = 
	if i = max then IBf.dump t "main_fun" "dots/"
	else 
	  let x = checkarray.(i-1) in
	  addv (IBf.add t (BTCf.make x x)) (i+1)
      in addv t 1
    )
    | MRbtree_i -> (
      let t = IBi.create ()
      in
      for i = 1 to max do 
	let x = checkarray.(i-1) in
	IBi.add t (x,x)
      done;
      IBi.dump t "main_imp" "dots/"
    )
      
