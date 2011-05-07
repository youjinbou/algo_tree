open OUnit
open Setup

(* RED BLACK TREE FUNCTIONAL --------------------------- *)

module RBTCf =
struct
  type key_t = int
  type 'a t = (key_t * 'a)
  let get_key x = fst x
  let make k v : 'a t  = (k,v)
  let compare k1 k2 = k1 - k2
  let string_of_key = string_of_int
end
 
module IRBf = Rbtree.Make(RBTCf)

let fun_test () = 
  let dump = if dump_data then (fun t f d ->IRBf.dump t f d) else (fun t f d -> ())
  in
  let lstart = min
  and lend   = max
  in 
  let size   = lend-lstart
  in
  let checkarray = Array.make (size) 0
  and counter = ref (lstart) in
  let f (k,v) =
    (* check that k and v are equal *)
    assert_equal ~msg:("iter: key and value don't match -> "^(string_of_int k)^" <> "^(string_of_int v)) k v;
    (* check values are in order *)
    assert_equal ~msg:("iter: wrong order of values -> "^(string_of_int !counter)^" <> "^(string_of_int v)) !counter v;
    incr counter

  in 
  let rec addv t i = 
    if i = (size) then t else 
      let x = checkarray.(i) in
      let t' = try
	IRBf.add t (RBTCf.make x x)
      with e -> assert_failure ("failed to add "^(string_of_int x))
      in
	dump t' ("add_"^(string_of_int i)^"_"^(string_of_int x)) dotty_folder;
 	addv t' (i+1)

  and checkv t i =
    if i = (size) then () else 
      let x = checkarray.(i) 
      in (
	  try
	    ignore (IRBf.find t x)
	  with e -> assert_failure ("failed to find "^(string_of_int x))
	);
	checkv t (i+1)

  and removev t i =
    if i = (size) then t else 
      let x = checkarray.(i) in
      let t',_ = try
	IRBf.remove t x
      with Not_found -> assert_failure ("failed to remove "^(string_of_int x))
      in
	dump t' ("remove_"^(string_of_int i)^"_"^(string_of_int x)) dotty_folder;
	assert_raises ~msg:("found removed item #"^(string_of_int i)^":"^(string_of_int x))(Not_found) (fun () -> ignore (IRBf.find t' x));
 	removev t' (i+1)

  in
    (* init check array *)
    for i = 0 to (size-1) do
      checkarray.(i) <- (i + lstart)
    done;
    randomize_order checkarray size;
    
    let t = addv (IRBf.create ()) 0 
    in
      IRBf.iter f t;
      (* check number of iterated entries *)
      assert_equal ~msg:("counter check: "^(string_of_int !counter)^" <> "^(string_of_int (lend))) !counter (lend);


      (try 
	 ignore (IRBf.check t)
       with IRBf.Inconsistency (a,b,c) -> assert_failure ("consistency check : error at node "^(string_of_int a)^" with left="^(string_of_int b)^" and right="^(string_of_int c)));

      
      randomize_order checkarray size;
      checkv t 0;

      randomize_order checkarray size;
      ignore (removev t 0)


(* RED BLACK TREE IMPERATIVE ---------------------- *)

module RBTCi =
struct
  type key_t        = int
  type t            = (key_t * int)
  let get_key x     = fst x
  let compare k1 k2 = if k1 < k2 then -1 else if k1 > k2 then 1 else 0
  let string_of_key = string_of_int
end
 
module IRBi = Rbtree_imp.Make(RBTCi)

let imp_test () = 
  let dump = if dump_data then (fun t f d -> IRBi.dump t f d) else (fun t f d -> ())

  in
  let lstart = min
  and lend   = max
  in 
  let size   = lend-lstart
  in
  let checkarray = Array.make (size) 0
  and counter = ref (lstart) in
  let f (k,v) =
    (* check that k and v are equal *)
    assert_equal ~msg:("iter: key and value don't match -> "^(string_of_int k)^" <> "^(string_of_int v)) k v;
    (* check values are in order *)
    assert_equal ~msg:("iter: wrong order of values -> "^(string_of_int !counter)^" <> "^(string_of_int v)) !counter v;
    incr counter

  in 
  let rec addv t i = 
    if i = (size) then () else 
      let x = checkarray.(i) in (
	  try
	    IRBi.add t (x, x)
	  with e -> assert_failure ("failed to add "^(string_of_int x))
	);
	dump t ("add_"^(string_of_int i)^"_"^(string_of_int x)) dotty_folder;
 	addv t (i+1)

  and checkv t i =
    if i = (size) then () else 
      let x = checkarray.(i) 
      in (
	  try
	    ignore (IRBi.find t x)
	  with e -> assert_failure ("failed to find "^(string_of_int x))
	);
	checkv t (i+1);

  and removev t i =
    if i = (size) then () else 
      let x = checkarray.(i) in (
	  try
	    ignore (IRBi.remove t x);
	    dump t ("remove_"^(string_of_int i)^"_"^(string_of_int x)) dotty_folder
	  with 
	      Not_found -> assert_failure ("failed to remove "^(string_of_int x))
	    | IRBi.Inconsistency (a,b,c) -> assert_failure ("consistency check : error at node "^(string_of_int a)^" with left="^(string_of_int b)^" and right="^(string_of_int c))
	);
	assert_raises ~msg:("found removed item #"^(string_of_int i)^":"^(string_of_int x))(Not_found) (fun () -> ignore (IRBi.find t x));
 	removev t (i+1)

  in
    (* init check array *)
    for i = 0 to (size-1) do
      checkarray.(i) <- (i + lstart)
    done;
    randomize_order checkarray size;
    
    let t = IRBi.create ()
    in
      ignore (addv t 0);
      IRBi.iter f t;
      (* check number of iterated entries *)
      assert_equal ~msg:("invalid counter:"^(string_of_int !counter)^" <> "^(string_of_int (lend))) !counter (lend);
      
      randomize_order checkarray size;
      checkv t 0;
      (try 
	 ignore (IRBi.check t)
      with IRBi.Inconsistency (a,b,c) -> assert_failure ("consistency check : error at node "^(string_of_int a)^" with left="^(string_of_int b)^" and right="^(string_of_int c)));
	
      randomize_order checkarray size;
      ignore (removev t 0)

