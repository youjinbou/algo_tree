open OUnit
open Random
open Setup

(* FIBONACCI HEAP ---------------------------------- *)

module FibOT =
struct 
  type key_t = int
  let compare = Pervasives.compare
end


module type TREEf =
sig

  type key_t
  type 'a t

  val make   : unit -> 'a t
  val size   : 'a t -> int
  val add    : 'a t -> key_t -> 'a -> 'a t
  val min    : 'a t -> (key_t * 'a)
  val find   : 'a t -> key_t -> 'a
  val iter   : ((key_t * 'a) -> unit) -> 'a t -> unit
  val remove : 'a t -> key_t -> ('a t * 'a) 
  val dump   : (key_t * 'a -> string) -> 'a t -> string -> string -> unit
    
  val check  : 'a t -> unit
    
  exception Inconsistency of string
      
end

module Test(Tree : TREEf with type key_t = int) =
struct

  let lstart     = Setup.min
  and lend       = Setup.max
  let size       = lend-lstart

  module Cache = Set.Make(struct type t = int let compare = compare end)

  let used = ref Cache.empty

  let free = 
    let s = Queue.create () in
    let a = Array.init size (fun x -> x) in
    randomize_order a size;
    for i = 0 to (pred size) do
      Queue.add a.(i) s
    done;
    s

  let cache_empty () = Cache.is_empty !used
  let queue_empty () = Queue.is_empty free

  let dump       = 
    if Setup.dump_data 
    then (fun t f d -> Tree.dump (fun v -> string_of_int (fst v)) t f d)
    else (fun t f d -> ())

  let find_busy_slot b = 
    let v = Cache.min_elt !used in 
    if b 
    then (
      used := Cache.remove v !used;
      Queue.add v free
    );
    v

  let find_free_slot () = 
    let v = Queue.take free
    in used := Cache.add v !used; v

  let drop_busy_slot k =
    let v = Cache.min_elt !used in
    assert_equal ~msg:("removed element not in cache :"^(string_of_int k)^" <> "^(string_of_int v)) k v;
    used := Cache.remove v !used;
    Queue.add v free
    
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
    let dname = Printf.sprintf "op_%04d_%s_%d" i "add" x in
    dump t' dname dotty_folder; t'


  (* search a value in the tree and assert that it worked *)
  let check_find i (t : int Tree.t) x =
    try
      ignore (Tree.find t x);
      let dname = Printf.sprintf "op_%04d_%s_%d" i "find" x in
      dump t dname dotty_folder
    with e -> assert_failure ("failed to find "^(string_of_int x))
	
  (* remove a value from the tree and assert that it worked *)
  let check_remove_min i t =
    let t', v = 
      try
	let (t: int Tree.t), (v : int) = Tree.remove t i in
(*	assert_equal ~msg:("remove : min not equal to :"^(string_of_int x)) v x; *)
	t, v
      with Not_found -> assert_failure ("failed to remove min at step "^(string_of_int i))
    in
    let dname = Printf.sprintf "op_%04d_%s_%d" i "remove" v in
    dump t' dname dotty_folder;
    assert_raises ~msg:("found removed item #"^(string_of_int i)^":"^(string_of_int v))(Not_found) (fun () -> ignore (Tree.find t' v)); t', v

  let test () =
    (* do randomly Setup.count time:
       - add elements in the tree
       - remove elements
       - check if element is present
    *)
    let t : int Tree.t ref = ref (Tree.make ()) in
    for c = 0 to Setup.count do
(*      Printf.printf "test : step = %d\n" c; *)
      let i = if cache_empty () 
	then 2 else 
	  if queue_empty () then 1
	  else Random.int 6 in
      (match i with
	| 0   -> ( (* search operation *)
	    let v = find_busy_slot false in
	    check_find c !t v;
	)
	| 1   -> ( (* remove min operation *)
	  let t', v = check_remove_min c !t
	  in
	  t := t';
	  ignore (drop_busy_slot v)
	)
	| _   -> ( (* add operation *)
	  let v = find_free_slot () in
	  t := check_add c !t v
	)
      );
      try 
	ignore (Tree.check !t)
      with Tree.Inconsistency s -> assert_failure ("consistency check : "^s)
    done
end

module Fib =
struct 
  exception Inconsistency of string 
  include Fib.Make(FibOT) 
  let check t = () 
  let remove t k = 
    let v = snd (min t) in
(*    Printf.fprintf stderr "min value : %d\n" (Obj.magic v); *)
    delete_min t, v
end
  
let test = let module T = Test(Fib) in T.test
