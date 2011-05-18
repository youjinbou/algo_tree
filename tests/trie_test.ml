open OUnit
open Setup


module Test(Tree : Trie.T with type key_t = int and type bin_t = int) =
struct

  type key_t = Tree.key_t

  let lstart     = Setup.min
  and lend       = Setup.max
  let size       = lend-lstart

  module UsedM = Map.Make(struct type t = int let compare = compare end)
  module UsedS = Set.Make(struct type t = int let compare = compare end)

  let string_of_bin size x = 
    let rec string_ x i s =
      if i < 0 
      then s 
      else 
	let v = 
	  if x mod 2 = 0 then "0" else "1"
	in
	string_ (x lsr 1) (pred i) (v^s)
    in
    string_ x size ""

  let string_of_key k = string_of_bin Sys.word_size k

  let used = ref (UsedM.empty, UsedS.empty)

  let free = 
    let s = Queue.create () in
    let a = Array.init size (fun x -> x) in
    randomize_order a size;
    for i = 0 to (pred size) do
      Queue.add a.(i) s
    done;
    s

  let no_used_element () = UsedS.is_empty (snd !used)
  let no_free_element () = Queue.is_empty free

  let min_used_element () = UsedS.min_elt (snd !used)

  let rec random_used_element () = 
    let v = (Random.int size) + lstart in
    try 
      UsedM.find v (fst !used)
    with Not_found -> random_used_element ()

  let next_free_element () = 
    Queue.take free

  let use_element k =
    used := UsedM.add k k (fst !used),UsedS.add k (snd !used)

  let release_element k = 
    used := UsedM.remove k (fst !used), UsedS.remove k (snd !used);
    Queue.add k free

  let dump       = 
    let dump t step op key = 
      let fname = Printf.sprintf "op_%04d_%s_%d" step op key in
      Tree.dump string_of_key string_of_int t fname dotty_folder in
    if Setup.dump_data 
    then dump
    else (fun t s o k -> ())
    
   (* check that k and v are equal *)
  let check_key_value (k,v) =
    assert_equal ~msg:("iter: key and value don't match -> "^(string_of_int k)^" <> "^(string_of_int v)) k v

  (* insert a value in the tree and assert that it worked *)
  let check_add i t x =
    let t' = 
      try
	Tree.add t x x
      with e -> assert_failure ("failed to add "^(string_of_int x))
    in
    dump t' i "add" x; t'

  (* search a value in the tree and assert that it worked *)
  let check_find i (t : int Tree.t) x =
    try
      ignore (Tree.find t x);
      dump t i "find" x
    with e -> assert_failure ("failed to find "^(string_of_int x))
	
  (* remove the minimum value from the tree and assert that it worked *)
  let check_remove_min i t =
    let v = Tree.min t in
    let v, t' = 
      try
	snd v, Tree.remove_min t
(*	assert_equal ~msg:("remove : min not equal to :"^(string_of_int x)) v x; *)
      with Not_found -> assert_failure ("failed to remove min "^(string_of_key (fst v))^" at step "^(string_of_int i))
    in
    dump t' i "remove_min" v;
    assert_raises ~msg:("found removed item #"^(string_of_int i)^":"^(string_of_int v))(Not_found) (fun () -> ignore (Tree.find t' v)); t', v

  (* remove a value from the tree and assert that it worked *)
  let check_remove i k t =
    let remove t k =
      Tree.remove t k
    in
    let t' = 
      try
	let t', v = remove t k in
	check_key_value (k,v); t'
      with Not_found -> assert_failure ("failed to remove value at step "^(string_of_int i))
    in
    dump t' i "remove" k;
    assert_raises ~msg:("step #"^(string_of_int i)^" : found removed item #"^(string_of_int k))(Not_found) (fun () -> ignore (Tree.find t' k)); t', k

  let test () =
    (* do randomly Setup.count time:
       - add elements in the tree
       - remove elements
       - check if element is present
    *)

    let t : int Tree.t ref = ref (Tree.make ()) in
    for c = 0 to Setup.count do
      let i = if no_used_element () 
	then -1 else 
	  if no_free_element () then 1
	  else Random.int 8 in
      (match i with
	| 0   -> ( (* search operation *)
	    let v =  min_used_element () in
	    check_find c !t v;
	)
	| 1   -> ( (* remove min operation *)
	  let t', v = check_remove_min c !t
	  in
	  t := t';
	  release_element v
	) 
	| 2   -> ( (* remove op *)
	  let v = random_used_element () in 
	  let t', v = check_remove c v !t in
	  t := t';
	  release_element v
	) 
	| _   -> ( (* add operation *)
	  let v = next_free_element () in
	  t := check_add c !t v;
	  use_element v
	)
      );
      try (
	Tree.check (string_of_int) !t
      )
      with Tree.Inconsistency s -> (
	Printf.fprintf stderr "consistency error at step #%d\n" c;
	assert_failure ("consistency check at step #"^(string_of_int c)^" : "^s)
      )
    done 

end

module TrieConf = 
struct

  type key_t = int
  type bin_t = int
      
  let convert k    = k
  let length       = Sys.word_size
  let shift_width  = 2
  let shift k      = k mod 2, k lsr 1
  let compare      = compare

end

let test =
  let module TB = Trie.Make(TrieConf) in
  let module T = Test(TB) in T.test
