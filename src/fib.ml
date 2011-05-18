
(*
  Fibonacci heap implementation.
  This structure is very good for priority queues. 
  make, add, find-min, union, decrease-key should be done in amortized O(1) and find, 
  remove-min, remove in amortized O(log n).
  However,  this implementation doesn't use the circular double linked list ( as done 
  in  the  original implementation) to allow uses without side-effects, and therefore 
  the union op isn't O(1) amortized anymore, and the remove-min and remove ops suffer
  as well :(

  Algorithm notes:
  The heap works by storing several trees in a list, with the following constraints:
  - Each node must only have children of key above its own. 
  - The  list  head must always point to the minimum entry in the list (which is also 
    the minimum value of the heap, as a consequence of the 1st constraint).
  - A node is colored : it must be either gray or black.

  Definition:
  The degree of a node is the number of sub-trees it is currently holding.
  
  When  adding a new entry in the heap, we just put it as the root of a new tree, and 
  check if it may become the new minimum.
  When  removing  the  minimum  value of the heap, we clip all its children and plant 
  them in the root list as new trees. We also consolidate the heap, by grafting trees 
  to trees having the same degree, thus ending with trees of unique degree.

*)

module type OrderedType =
sig 
  type key_t
  val minus_infinity : key_t   (* the absolute minimum value possible for type key_t *)
  val compare        : key_t -> key_t -> int
end

module type T =
sig

  type key_t
  type 'a t

  val make   : unit -> 'a t
  val size   : 'a t -> int
  val add    : 'a t -> key_t -> 'a -> 'a t
  val find   : 'a t -> key_t -> 'a
  val iter   : ((key_t * 'a) -> unit) -> 'a t -> unit
  val min    : 'a t -> key_t * 'a
  val decrease_key : 'a t -> key_t -> key_t -> 'a t
  val remove_min : 'a t -> 'a t
  val remove : 'a t -> key_t -> 'a t * 'a
  val dump   : (key_t -> string) -> ('a -> string) -> 'a t -> string -> string -> unit
    
  val check  : (key_t -> string) -> 'a t -> unit
    
  exception Inconsistency of string
      
end

module Make(O : OrderedType) : T with type key_t = O.key_t = 
struct

  type key_t = O.key_t

  type color = Black | Gray

  type 'a node =  Node of (color * (key_t * 'a)  * 'a tree)
  and  'a tree = ('a node) list * int * int  (* the list of roots, the number of nodes, the degree *)

  let tree_make () = ([], 0, 0)

  let node_make c k v = Node (c, (k, v), tree_make ())
  let node_color (Node (c, _, _)) = c
  let node_content (Node (_, v, _)) = v
  let node_key n = fst (node_content n) 
  let node_value n = snd (node_content n)
  let node_tree (Node (_, _, l))  = l

  let tree_roots (l, s, d)  = l
  let tree_size (l, s, _)   = s
  let tree_degree (l, _, d) = d

  let node_degree (Node (_,_,l)) = tree_degree l
  let node_size (Node (_, _, l)) = tree_size l

  (* compute the degree of a list of nodes *)
  let compute_degree (l, _, _) = List.length l

  let node_compare (n1 : 'a node) (n2 : 'a node) : int =
    let v1 = node_key n1 
    and v2 = node_key n2 
    in O.compare v1 v2 

  let tree_compare t1 t2 = 
    match t1, t2 with
      |    [],     _ -> -1
      |     _,    [] ->  1
      | x1::_, x2::_ -> 
	node_compare x1 x2

  (* add <key,value> into the tree t --
     O(1) 
  *)
  let tree_add t key value = 
    let nt = node_make Gray key value in
    match t with
	([], _, _)           -> ([nt], 1, 1)
      | (m::xs as l, s, d)   -> 
	if (node_compare nt m) <= 0 
	then ((nt::l), succ s, succ d) 
	else ((m::nt::xs), succ s, succ d)

  (* insert node n into tree t --
     this operation happens in consolidate, therefore t and n have the
     same degree
     O(1) 
  *)
  let tree_insert (t : 'a tree) (n : 'a node) =
    match t with
	([], _, _)           -> ([n], 1 + (node_size n), 1)
      | (m::xs as l, s, d)   -> 
	let s' = s + (node_size n) + 1
	and d' = succ d in
	if (node_compare n m) <= 0 
	then ((n::l), s', d') 
	else (m::n::xs, s', d')
	  
  (* insert node n2 into node n1's tree -- 
     O(1)
  *)
  let node_insert n1 n2 = 
    Node (node_color n1, node_content n1, tree_insert (node_tree n1) n2)

  (* ------------------------------------------------- *)

  type 'a t = 'a tree

  let make = tree_make

  let size = tree_size

  let add = tree_add

  let degree = tree_degree



  (* consistency check =
     it should verify that :
     - all the nodes are in coherent order, that is, any node key is below 
       the keys of its children
     - the degree of each node is correct
     - the total number of element for each node is correct
     - the min element is the first of the tree
  *)
  exception Inconsistency of string

  let check fkey (t : 'a t) = 
    let rec check_tree (l, s, d) kparent =
(*      Printf.fprintf stderr "check_tree input : parent = '%s' s = %d, d = %d\n" (fkey kparent) s d; *)
      let rs, rd = check_list l kparent in
(*      Printf.fprintf stderr "check_tree check_list : '%s' s = %d, d = %d\n" (fkey kparent) rs rd; *)
      if rs != s then (
	let s = Printf.sprintf "invalid size for node '%s' : %d (real : %d)" (fkey kparent) s rs in
	raise (Inconsistency s)
      );
      if rd != d then (
	let s = Printf.sprintf "invalid degree for node '%s' : %d (real : %d)" (fkey kparent) d rd in
	raise (Inconsistency s)
      );
      rs, rd

    and check_list l kparent =
      let ls, ld = List.fold_left (fun acc n -> acc + (succ (fst (check_node kparent n)))) 0 l, List.length l in
(*      Printf.fprintf stderr "check_list output : parent = '%s' s = %d, d = %d\n" (fkey kparent) ls ld; *)
      ls, ld

    and check_node kparent (Node (c, (k,v), t)) =
(*      Printf.fprintf stderr "check_node input : parent = '%s'\n"  (fkey kparent); *)
      if compare k kparent < 0 then (
	let s = Printf.sprintf "invalid node order : parent key '%s' above current '%s'" (fkey kparent) (fkey k) in
	raise (Inconsistency s)
      );
      check_tree t k

    in
(*    prerr_endline "-- CHECK ---------------------------------------------";
    Printf.fprintf stderr "check_tree root input : s = %d, d = %d\n" (tree_size t) (tree_degree t); *)
    ignore (check_tree t O.minus_infinity)
(*    prerr_endline "------------------------------------------------------" *)

  (* ------------------------------------------------- *)

  let dump fkey fvalue (t : 'a t) filename dirname = 
    let file = open_out (dirname^"/"^filename^".dot") in
    let dump_link parent child =
      output_string file (parent^" -> "^child^";\n")
    and make_label n = (fkey (node_key n))^"_"^(fvalue (node_value n))
    and make_id n = fkey (node_key n)
    and string_of_color c = match c with Black -> "black", "white" | _ -> "grey", "black" 
    in
    let node_attr id label c s d =
      let bc, fc = string_of_color c in
      (id^" [ style=filled, fillcolor= "^bc^", fontcolor= "^fc^", label =\""^label^":["^(string_of_int s)^";"^(string_of_int d)^"]\" ];\n")
    in
    let rec node_dump parent (Node (c, k, (l, s, d)) as n) = 
      let label = make_label n
      and id = make_id n in 
      dump_link parent id;
      output_string file (node_attr id label c s d);
      List.iter (fun x -> node_dump id x) l
    in
    output_string file ("digraph "^filename^" {\n");
    output_string file ("name ="^filename^";\n");
    output_string file "node [shape=ellipse];\n";
    output_string file (node_attr "root" "root" Gray (size t) (degree t));
    List.iter (fun x -> node_dump "root" x) (tree_roots t);
    output_string file "}";
    close_out file

  (* ------------------------------------------------- *)

  let find ((l, s, d) as t : 'a t)  (k : key_t) : 'a =
    let rec find_node n k =
      match compare (node_key n) k with
	  0             -> Some (node_value n)
	| c when c < 0  -> find_list (tree_roots (node_tree n)) k
	| _             -> None
    and find_list l k =
      match l with 
	| []    -> None
	| n::ns -> 
	  match find_node n k with
	      None -> find_list ns k
	    | r    -> r
    in
    match find_list l k with
	None   -> raise Not_found
      | Some v -> v


  (* the correct ordering is not to be expected *)
  let iter f t =
    let rec iter_node f (Node (c, v, l)) =
      f v;
      iter_tree l
    and iter_tree t =
      let l = tree_roots t in
      List.iter (fun n -> iter_node f n) l
    in
    iter_tree t

  (* search the new min value to point to *)
  let update_min ((l, s, d) as t : 'a t) =
    let rec update_min m l nl = 
      match l with
	  []    -> m::nl
	| x::xs -> ( 
	  if node_compare m x <= 0 
	  then 
	    update_min m xs (x::nl)
	  else 
	    update_min x xs (m::nl)
	)
    in
    match l with 
	[]    -> (l, s, d)
      | x::xs -> (
	let l = update_min x xs [] in
	(l, s, d)
      )

  let log_phi s d = 
    max (
      if s <= 7 then 3
      else 
	s / 2 ) (succ d)

  (* check the heap and make sure that we don't have any couple of trees of the same degree *)
  let consolidate (t : 'a t) = 
    let s = tree_size t in
    let max_i = log_phi s (tree_degree t) in
    let v = Array.make max_i (None) in
    let restore_t () = 
      (* find the first node in the array *)
      let i, m = 
	let rec first_insert i = 
	  if i >= max_i 
	  then failwith "consolidate : empty array on restore !!"
	  else 
	    match v.(i) with
	      | None   -> first_insert (succ i)
	      | Some x -> v.(i) <- None; i, x
	in first_insert 0
      in
      (* fold left starting at index i *)
      let rec fold_left f acc v i =
	if i >= max_i then acc 
	else 
	  fold_left f (f acc v.(i)) v (succ i)
      in
      (* insert the rest of the array *)
      let insert (m, l, d) xo = 
	match xo with
	  | None   -> (m, l, d)
	  | Some x -> 
	    let nd = succ d in
	    if node_compare m x <= 0 then (m, x::l, nd) else (x, m::l, nd)
      in
      let (m, l, d) = fold_left insert (m, [], 1) v i in
      (m::l, s, d)
    in
    let rec consolidate c l =
      let combine (n1 : 'a node) (n2 : 'a node) : 'a node =
	if (node_compare n1 n2) <= 0 then node_insert n1 n2 else node_insert n2 n1
      in
      let d = node_degree c in
      match v.(d) with
	  None    -> (
	    v.(d) <- Some c; 
	    match l with 
	      | []    -> restore_t ()
	      | x::xs -> consolidate x xs
	  )
	| Some c' -> (
	  v.(d) <- None;
	  consolidate (combine c c') l
	)
    in
    match tree_roots t with
      | []    -> t
      | m::l  -> consolidate m l

  (* union of 2 heaps : O(degree1 + degree2) *)
  let union ((l1, n1, d1) as t1) ((l2, n2, d2) as t2) =
    match l1, l2 with
	[], _             -> t2
      | _ , []            -> t1
      | m1::x1s, m2::x2s  -> 
	if compare m1 m2 <= 0 
	then (m1::m2::(x1s @ x2s), n1 + n2, max d1 d2)
	else (m2::m1::(x1s @ x2s), n1 + n2, max d1 d2)
	  
  (* removal of minimum element : O(ln n) *)
  let remove_min (t : 'a tree) : 'a tree =
(*    Printf.fprintf stderr "remove_min input : s = %d d = %d\n" (tree_size t) (tree_degree t); *)
    match t with
      | ([], _, _)    -> raise Not_found
      | (m::xs, n, d) -> 
	let tm = node_tree m in
	let d' = (pred d) + (tree_degree tm)
	and l = xs @ (tree_roots tm) in
	let t' = consolidate (l, pred n, d') in
(*	Printf.fprintf stderr "remove_min consolidate : s = %d d = %d\n" (tree_size t') (tree_degree t'); *)		
	update_min t'

  (* decrease key : reduce the priority of value of key k to k' 
     possible outcomes:
     0 - the key isn't found
     1 - the decrease doesn't change the order 
     2 - the decrease put the node n below its parent 
         => move the node to the heap roots
         2a - its parent isn't marked : mark it
         2b - its parent is marked, unmark and move it to the roots, loop to gp
     => the function goes down the heap, find the node to change, and check the state
        as noted above, doing 2b while moving back up
     => the function must check at each step what is the returned value : a new node list for
        the current node, a node list to add to the roots, and a bool indicating if we have to
        check the color.
   *)
  let decrease_key t k k' : 'a tree =
    let rec find_node (Node (nc, ((nk, nv) as nkv), nt) as n) kparent : (('a node) option * 'a tree * bool) option =
      match compare nk k with
	| 0             -> (
	  let n' = Node (nc, (k', nv), nt) in
	  match compare kparent k' with 
	    | 0            -> failwith "fix-me : duplicate key"
	    | c when c < 0 -> Some (Some n', ([], 0, 0), false)                      (* case 1 *)
	    | c when c > 0 -> Some (None,([n'], succ (tree_size nt), 1), true)       (* case 2 *)
	)
	| c when c > 0  -> None (* case 0 *)
	| c when c < 0  -> (
	  match find_tree nt nk with
	    | None                            -> None       (* case 0 *)
	    | Some (nt', (rl, rs, rd), true)  -> Some (     (* case 2 *)
	      match nc with
		| Gray  -> 
		  Some (Node (Black, nkv, nt')), (rl, rs, rd), false          (* case 2a *)
		| Black -> 
		  let n' = Node (Gray, nkv, nt') in
		  None, (n'::rl, rs + (tree_size nt') + 1, succ rd), true     (* case 2b *)
	    )
	    | Some (nt', (rl, rs, rd), false) -> Some ( (* case 1 *)
	      Some (Node (nc, (nk, nv), nt')), (rl, rs, rd), false
	    )
	)
    and find_tree (l, s, d) kparent : ('a tree * 'a tree * bool) option =
      match l with
	| []     -> None (* case 0 *)
	| n::ns  -> 
	  match find_node n kparent with
	    | None                 -> (
		match find_tree (ns, pred s, pred d) kparent with
		    None                        -> None                   (* case 0 *)
		  | Some ((nl, ns, nd), rt, b)  -> Some (
		    (n::nl,succ ns, succ nd), rt, b)                      (* case 1, 2 *)
	      )
	    | Some (Some n, t, b)  -> Some ((n::ns, s - (tree_size t), d), t, b)       (* case 1 *)
	    | Some (None, t, b)    -> Some ((ns, s - (tree_size t), pred d), t, b)     (* case 2 *)
    in
    let merge (l1, s1, d1) (l2, s2, d2) = 
      let rec merge m l1 l2 =
	match l2 with 
	  | []    -> m::l1
	  | x::xs -> if node_compare m x <= 0 then merge m (x::l1) xs else merge x (m::l1) xs
      in
      match l1 with
	| []    -> update_min (l2, s2, d2) 
	| m::xs -> (merge m xs l2, s1 + s2, d1 + d2)
    in
    match find_tree t k with 
      | None              -> raise Not_found
      | Some (nt, rt, _)  -> merge nt rt
	
  let min (l, s, d) = 
    match l with
      | []    -> raise Not_found
      | x::xs -> node_content x

  let remove t k =
    let t' = decrease_key t k O.minus_infinity in
    let m = min t' in
    remove_min t', snd m

end

