open OUnit
open Setup

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

let test () = 

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
