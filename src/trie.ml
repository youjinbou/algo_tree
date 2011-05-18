(* 
   In comparison to other types of trees, the trie (or digital tree) is pretty straightforward 
   to implement: it works by splitting the key in several chunks, and use these to successively
   index the value down. In the original version, the chunks are prefixes of the key, so that, 
   for instance, for a chunk size of only one bit, the trie will hold 2 subtree at each level,
   since a bit can hold 2 values. 
   In this implementation, the trie is configured with a key type, a "binary representation" type
   for the key type (say for instance you have objects, and you want to index them using their
   string representation), an operator to convert the 1st to the 2nd type, an operator to divide
   the bin type in chuncks, an operator to compare bin values, and values holding the respective 
   sizes of the bin type and the chuncks.
   
*)


module type BinaryRep =
sig 

  type key_t
  type bin_t

  (* the length of the key *)
  val length : int
  (* the number of bits extracted by the shift *)
  val shift_width : int  

  val convert : key_t -> bin_t
  val shift   : bin_t -> int * bin_t
  val compare : bin_t -> bin_t -> int

end

(* --------------------------------------------------------------------------------- *)

module type T =
sig

  type key_t
  type bin_t
  type 'a t

  val make   : unit -> 'a t
  val size   : 'a t -> int
  val add    : 'a t -> key_t -> 'a -> 'a t
  val find   : 'a t -> key_t -> 'a
  val iter   : ((key_t * 'a) -> unit) -> 'a t -> unit
  val min    : 'a t -> key_t * 'a
  val remove_min : 'a t -> 'a t
  val remove : 'a t -> key_t -> 'a t * 'a
  val dump   : (bin_t -> string) -> ('a -> string) -> 'a t -> string -> string -> unit
    
  val check  : (key_t -> string) -> 'a t -> unit
    
  exception Inconsistency of string
      
end

(* --------------------------------------------------------------------------------- *)

(* fixed size key trie implementation *)

module Make (BR : BinaryRep) =
struct

  type key_t = BR.key_t

  type bin_t = BR.bin_t

  let width = BR.shift_width

  let convert = BR.convert

  exception Inconsistency of string
  exception Duplicate_Key

  type 'a node = 
    | Node of (int * ('a node array))
    | Leaf of bin_t * (key_t * 'a)
    | EmptyLeaf

  type 'a t = 'a node * int

  let empty = EmptyLeaf

  let rec node_min_key a i =
    if i >= width then raise Not_found;
    match a.(i) with
	EmptyLeaf -> node_min_key a (succ i)
      | _         -> i

  (* --------------------------------------------------------------------------------- *)

  let make () = empty, 0

  let size (t, s) = s

  (* the size of they bin type is actually not necessary, the algorithm relying only on 
     the fact that the size is the same for every values of bin_t *)
  let add (t,s) k v =
    let rec add t k v =
      let rec build_tree_2 k1 v1 k2 v2 =
	let a       = Array.make width EmptyLeaf
	and m1, k1' = BR.shift k1
	and m2, k2' = BR.shift k2 in
	if m1 = m2
	then (
	  a.(m1) <- build_tree_2 k1' v1 k2' v2;
	  Node (1, a)
	)
	else (
	  a.(m1) <- Leaf (k1', v1);
	  a.(m2) <- Leaf (k2', v2);
	  Node (2, a)
	)
      in
      match t with
	| EmptyLeaf   -> Leaf (k, v)
	| Leaf (i,lv) -> (
	  if compare i k = 0 then raise Duplicate_Key;
	  build_tree_2 i lv k v
	)
	| Node (n, a)    -> (
	  let a'    = Array.copy a
	  and m, k' = BR.shift k in
	  let n' = 
	    match a'.(m) with
		EmptyLeaf -> succ n
	      | _         -> n
	  in
	  a'.(m) <- add a.(m) k' v;
	  Node (n', a')
	)
    in
    add t (convert k) (k,v), succ s

  let replace (t, s) k v =
    let rec replace t k v =
      let rec build_tree_2 k1 v1 k2 v2 =
	let a       = Array.make width EmptyLeaf 
	and m1, k1' = BR.shift k1
	and m2, k2' = BR.shift k2 in
	if m1 = m2 
	then (
	  a.(m1) <- build_tree_2 k1' v1 k2' v2;
	  Node (1, a)
	)
	else (
	  a.(m1) <- Leaf (k1', v1);
	  a.(m2) <- Leaf (k2', v2);
	  Node (2, a)
	)
      in
      match t with
	| EmptyLeaf   -> Leaf (k, v)
	| Leaf (i,lv) -> (
	  if i = k 
	  then 
	    Leaf(i, v)
	  else
	    build_tree_2 i v k v
	)
	| Node (n, a)    -> (
	  let a' = Array.copy a
	  and m, k' = BR.shift k in
	  let n' = 
	    match a'.(m) with
		EmptyLeaf -> succ n
	      | _         -> n
	  in
	  a'.(m) <- replace a.(m) k' v;
	  Node (n', a')
	)
    in
    (replace t (convert k) (k,v), succ s)

  let rec find_bin t k =
    match t with
      | EmptyLeaf    -> raise Not_found
      | Leaf (lk,lv) -> if k = lk then lv else raise Not_found
      | Node (n, a)  -> (
	let m, k' = BR.shift k in
	find_bin a.(m) k'
      )

  let find (t, s) k =
    snd (find_bin t (convert k))

  let min (t, s) =
    if s = 0 then raise Not_found;
    let rec min t =
      match t with
	| EmptyLeaf   -> raise Not_found
	| Leaf (k, v) -> v
	| Node (n, a) -> min a.(node_min_key a 0)
    in
    min t

  let remove_min (t, s) =
    let rec remove_min t =
      match t with
	| EmptyLeaf     -> raise Not_found
	| Leaf (lk, lv) -> EmptyLeaf, lv
	| Node (nn, na) -> (
	  let i = node_min_key na 0 in
	  let n, v = remove_min na.(i) in
	  match n with 
	      EmptyLeaf when nn = 1 -> (
		let v = min (t, nn) in 
		EmptyLeaf, v
	      )
	    | EmptyLeaf             -> (
	      let a' = Array.copy na in
	      a'.(i) <- n;
	      Node (pred nn, a'), v
	    )
	    | _                     -> (
	      let a' = Array.copy na in
	      a'.(i) <- n;
	      Node (nn, a'), v
	    )
	)
    in
    let t, v  = remove_min t in (t, pred s)
      
  let remove (t,s) k =
    let rec remove t k =
      match t with
	| EmptyLeaf    -> raise Not_found
	| Leaf(lk, lv) -> if k = lk then EmptyLeaf, lv else raise Not_found
	| Node(nn, na) -> (
	  let m, k' = BR.shift k in
	  let n, v = remove na.(m) k' in
	  match n with
	      EmptyLeaf when nn = 1 -> (
		let v = find_bin t k in
		EmptyLeaf, v
	      )
	    | EmptyLeaf             -> (
	      let a' = Array.copy na in
	      a'.(m) <- n;
	      Node (pred nn, a'), v
	    )
	    | _                     -> (
	      let a' = Array.copy na in
	      a'.(m) <- n;
	      Node (nn, a'), v
	    )
	)
    in
    let t, v = remove t (convert k) in (t, pred s), (snd v)

  let iter f (t, s) = 
    let rec iter f t =
      match t with
	| EmptyLeaf  -> ()
	| Leaf(k, v) -> f v
	| Node (n,a) -> Array.iter (iter f) a
    in iter f t

  let check fkey (t,s) = 
    let rec check_node t =
      match t with
	  EmptyLeaf    -> ()
	| Leaf (k, v)  -> ()
	| Node (nn, a) -> (
	  let count = Array.fold_left (fun acc -> function EmptyLeaf -> acc | _ -> succ acc) 0 a in
	  if count != nn 
	  then
	    raise (Inconsistency (Printf.sprintf "check : nodes count invalid, %d found, %d announced" count nn))
	)
    in
    check_node t
    
  let dump fkey fvalue (t,s) filename dirname = 
    let file = open_out (dirname^"/"^filename^".dot") in
    let dump_link parent child =
      output_string file (parent^" -> "^child^";\n")
    and make_label (k,v) = (fkey (convert k)^" "^(fvalue v))
    and make_id parent n = parent^"_"^(fkey n)
    in
    let node_attr id label =
      (id^" [ label =\""^label^"\" ];\n")
    in
    let dump_leaf parent k v =
      let label = make_label v
      and id    = make_id parent k in 
      dump_link parent id;
      output_string file (node_attr id label)
    in
    let rec node_dump parent t = 
      match t with
	| EmptyLeaf   -> ()
	| Leaf (k, v) -> dump_leaf parent k v
	| Node (n, a) ->
	  let dump_index i x =
	    let id = parent^"_"^(string_of_int i) in
	    dump_link parent id;
	    output_string file (node_attr id id);
	    node_dump id x
	  in
	  Array.iteri dump_index a
    in
    output_string file ("digraph "^filename^" {\n");
    output_string file ("name ="^filename^";\n");
    output_string file "node [shape=ellipse];\n";
    output_string file (node_attr "r" "root");
    node_dump "r" t;
    output_string file "}";
    close_out file
      

end

(* --------------------------------------------------------------------------------- *)

