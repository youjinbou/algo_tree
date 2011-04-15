open OUnit
open Random


(* unit tests for the sorted tree implementations 
   for each kind of tree we do the following:


   - the tree is instancied as a (int, int) map
   - A range of ints from 'min' to 'max' are then
   mapped to themselves in the tree, in a random
   order. 
   - The same range is then seeked in a different random
   order.
   - The same range is then remove from the tree, again
   with a different order.


   Each implementation requires its own set of tests

   'dump_data' indicates if we dump a graphviz 
   dot compatible representation of the tree
   at certain steps of the tests.
   
   
*)


let _ = Random.init (int_of_float (Unix.time ()))

let dump_data = false

let min = 10
let max = 8000

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


(* BTREE ----------------------------------- *)

module BTCeven =
struct
  type key_t   = int
  type value_t = int
  let compare (k1: int) (k2: int) = k1 - k2
  let max = 14
  let string_of_key = string_of_int
end
 
module BTCodd  =
struct
  type key_t   = int
  type value_t = int
  let compare (k1: int) (k2: int) = k1 - k2
  let max = 27
  let string_of_key = string_of_int
end


module IB = Btree.Mutable.Make(BTCeven)

let btree_test () = 

  let dump = if dump_data then (fun t f d -> IB.dump t f d) else (fun t f d -> ())
  in
  let lstart = min
  and lend   = max 
  in 
  let size   = lend-lstart
  in
    (* array listing all the elements we will put in the tree *)
  let checkarray = Array.make (size) 0
  and counter = ref (lstart) in
  let f k v =
    (* check that k and v are equal *)
    assert_equal ~msg:("iter: key and value don't match -> "^(string_of_int k)^" <> "^(string_of_int v)) k v;
    (* check values are in order *)
    assert_equal ~msg:("iter: wrong order of values -> "^(string_of_int !counter)^" <> "^(string_of_int v)) !counter v;
    incr counter

  (* check that all elements in the array starting at index s are in the tree *)
  and checkcontent tree s =
    for i = s to (size-1) do 
      let (x: IB.key_t) =  checkarray.(i) in 
	try 
	  let y = IB.find tree x in
	    assert_equal ~msg:("find item :"^(string_of_int i)) y x
	with Not_found -> assert_failure ("failed to find: "^(string_of_int x))
    done
      
  and tree = IB.create () 
  in
    (* init check array *)
    for i = 0 to (size-1) do
      checkarray.(i) <- (i + lstart)
    done;
    randomize_order checkarray size;


    for i = 0 to (size-1) do 
      let x =  checkarray.(i) in
	try 
	  IB.add tree x x;
	  dump tree ("add_"^(string_of_int i)^"_"^(string_of_int x)) dotty_folder
	with e -> assert_failure ("failed to add "^(string_of_int x))
     done ;

    IB.dump tree "complete_tree" dotty_folder;
    
    IB.iter tree f;
    (* check number of iterated entries *)

    assert_equal ~msg:((string_of_int !counter)^" <> "^(string_of_int (lend))) !counter (lend);

    randomize_order checkarray size;

    checkcontent tree 0; 

    randomize_order checkarray size;

    for i = 0 to (size-1) do 
	let x =  checkarray.(i)
	in (
	    try
	      IB.remove tree x;
	      dump tree ("remove_"^(string_of_int i)^"_"^(string_of_int x)) dotty_folder
	    with e -> ( 
	      assert_failure ("failed to remove "^(string_of_int x))   
	    )
	  );
	  (*
	  checkcontent tree (i+1); 
	  *)
	  assert_raises ~msg:("item #"^(string_of_int i)^":"^(string_of_int x))(Not_found) (fun () -> IB.find tree x)
    done 

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

let rbtree_fun_test () = 
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


let rbtree_imp_test () = 
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



(* TEST SUITE -------------------------------------- *)


let tree_test_list =
  TestLabel ("[test int list]", TestList [
	       TestLabel ("Btree", TestCase(fun _ -> btree_test ())); 
	       TestLabel ("Rbtree (functional)", TestCase(fun _ -> rbtree_fun_test ())); 
	       TestLabel ("Rbtree (imperative)", TestCase(fun _ -> rbtree_imp_test ())) 
	     ]
	    )

let test_suite = TestLabel("[ Test Suite ]",
			   TestList 
			     [
			       tree_test_list
			     ]
			  );;


let _ =
  run_test_tt test_suite

