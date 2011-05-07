(* module CList = CircularList *)

(*
  Fibonacci heap implementation.
  This structure is very good for priority queues. 
  make-heap, insert, find-min, union, decrease-key should be done in amortized O(1)
  and delete-min, delete in amortized O(log n).
  However, this implementation doesn't use the circular double linked list as it should
  and therefore some operations fall back to a worse case of O(n) :(
  
*)

module type OrderedType =
sig 
  type key_t
  val compare       : key_t -> key_t -> int
end

module Make(O : OrderedType) =
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
  let tree_degree (l, _, d) = List.length l

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
  (* the heap (or root tree) is structurally the same as the inner trees, 
     however  the last int represents the maximum degree within the tree, 
     not  the  degree  of the tree, since the root node list isn't solid.
     We  need  the  maximum  degree  for the consolidation phase, when we 
     allocate an array to store the trees to merge. 
     The  root  tree  list can be as large as the number of elements, but 
     then  we  will  combine  the  first elements, and we will need up to 
     log_phi(n) cells in the array anyway. 
  *)

  type 'a t = 'a tree

  let make = tree_make

  let size = tree_size

  let degree = tree_degree

  let dump fkey (t : 'a t) filename dirname = 
    let file = open_out (dirname^"/"^filename^".dot") in
    let dump_link parent child =
      output_string file (parent^" -> "^child^";\n")
    and make_label n = fkey (node_content n)
    and make_id n = fkey (node_content n) 
    and string_of_color c = match c with Black -> "black", "white" | _ -> "grey", "black" 
    in
    let node_attr id label c s d =
      let bc, fc = string_of_color c in
      (id^" [ style=filled, fillcolor= "^bc^", color= "^fc^", label =\""^label^":["^(string_of_int s)^";"^(string_of_int d)^"]\" ];\n")
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


(*
  (* add a (key,value) to a heap --
     max degree doesn't change
     O(1) 
  *)
  let add (t : 'a t) (k : key_t) (v : 'a) = 
    let nt = node_make Gray k v in
    match t with
	([], _, _)           -> ([nt], 1, 1)
      | (m::xs as l, s, d)   -> 
	if (node_compare nt m) <= 0 
	then ((nt::l), succ s, d) 
	else (m::nt::xs, succ s, d)
*)
  let add = tree_add

  (* search the new min value to point to, check the max degree *)
  let update_min ((l, s, d) as t : 'a t) =
    let max_degree n d = max (node_degree n) d in
    let rec update_min m l nl d = 
      match l with
	  []    -> m::nl, d
	| x::xs -> ( 
	  let d = max_degree x d in
	  if node_compare m x <= 0 
	  then 
	    update_min m xs (x::nl) d
	  else 
	    update_min x xs (m::nl) d
	)
    in
    match l with 
	[]    -> (l, s, d)
      | x::xs -> (
	let l, d = update_min x xs [] d in
	(l, s, d)
      )

  (* not computing the real value here, takes time, ideally, we should create a table of logs *)
  let log_phi x = 
    if x <= 7 then 3
    else 
      x / 2

  (* check the heap and make sure that we don't have any couple of trees of the same degree *)
  let consolidate (l, s, d) = 
(*    Printf.fprintf stderr "consolidate : size = %d\n" s;
    Printf.fprintf stderr "consolidate : max degree = %d\n" d; *)
    let max_i = log_phi s in
(*    Printf.fprintf stderr "consolidate : array size = %d\n" max_i; *)
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
	    let nd = max d (node_degree x) in  (* find the max degree *)
	    if node_compare m x <= 0 then (m, x::l, nd) else (x, m::l, nd)
      in
      let (m, l, d) = fold_left insert (m, [], 0) v i in
      (m::l, s, d)
    in
    let rec consolidate c l =
      let combine (n1 : 'a node) (n2 : 'a node) : 'a node =
	if (node_compare n1 n2) <= 0 then node_insert n1 n2 else node_insert n2 n1
      in
      let d = node_degree c in
(*      Printf.fprintf stderr "consolidate : current = %d - degree = %d\n" (Obj.magic (node_key c)) d; *)
      match v.(d) with
	  None    -> (
(*	    Printf.fprintf stderr "consolidate : no duplicate for current\n"; *)
	    v.(d) <- Some c; 
	    match l with 
	      | []    -> restore_t ()
	      | x::xs -> consolidate x xs
	  )
	| Some c' -> (
(*	    Printf.fprintf stderr "consolidate : duplicate = %d found for current\n" (Obj.magic (node_key c')); *)
	  v.(d) <- None;
	  consolidate (combine c c') l
	)
    in
    match l with
      | []    -> (l, s, d)
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
  let delete_min (t : 'a tree) : 'a tree =
(*    Printf.fprintf stderr "delete_min\n"; *)
    match t with
      | ([], _, _)    -> raise Not_found
      | (m::xs, n, d) -> 
	let tm = node_tree m in
	let d' = d + (tree_degree tm)
	and l = xs @ (tree_roots tm) in
	update_min (consolidate (l, pred n, d'))

  (*
  (* decrease key : reduce the priority of value of key k to k' 
     possible outcomes:
     1 - the decrease doesn't change the order 
     2 - the decrease put the node n below its parent 
         move the node to the heap roots
         2a - its parent isn't marked : mark it
         2b - its parent is marked, unmark and move it to the roots, loop to gp
     => the function goes down the heap, find the node to change, and check the state
        as noted above, doing 2b while moving back up
     => the function must check at each step what is the returned value : a new node list for
        the current node, a node list to add to the roots, and a bool indicating if we have to
        check the color.
   *)
  let decrease_key t k k' : 'a tree =
   let rec find_node (Node (nc, (nk, nv), nt) as n) k : ('a node option, 'a tree, bool) option =
      match compare nk k with
	  0             -> Some (Some (Node (nc, (k', nv), nt)), ([], 0, 0), true)
	| c when c > 0  -> None 
	| c when c < 0  -> (
	  match find_tree nt k with
	    | None                           -> None
	    | Some (nt, (rl, rs, rd), true)  -> Some (
	      match nc with
		  Grey  -> Some (Node (Black, (nk, nv), nt)), (rl, rs, rd), false
		| Black -> None, ((Node (Grey, (nk, nv), nt)::rl, succ rs, succ rd)), true
	    )
	    | Some (nt, (rl, rs, rd), false) -> Some (
	      Some (Node (nc, (nk, nv), nt)), (rl, rs, rd), false
	    )
	)
   and find_tree (l, s, d) k : ('a tree, 'a tree, bool) option =
     match l with
       | []     -> None
       | n::ns  -> 
	 match find_node n k with
	     None                 -> (
	       match find_tree (ns, pred s, pred d) k with
		   None                           -> None
		 | Some ((nl, ns, nd), rt, b)     -> Some ((n::nl,succ ns, succ nd), t, b)
	     )
	   | Some (Some n, t, b)  -> Some ((n::ns, s, d), t, b)
	   | Some (None, t, b)    -> Some ((ns, pred s, pred d), t, b)
   in
   match find_tree t k with 
       None              -> raise Not_found
     | Some (nt, rt, b)  -> union nt rt
  *)
  let min (l, s, d) = 
    match l with
      | []    -> raise Not_found
      | x::xs -> node_content x

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



  (* the correct ordering is not guaranteed *)
  let iter f t =
    let rec iter_node f (Node (c, v, l)) =
      f v;
      iter_tree l
    and iter_tree t =
      let l = tree_roots t in
      List.iter (fun n -> iter_node f n) l
    in
    iter_tree t

end

