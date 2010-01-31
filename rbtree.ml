(* Red Black Tree implementation - functional style 
   
   the customary OrderedType module type describes 
   the datatype to be stored in the tree. In this instance
   the storage key should be accessible through the 
   application of the get_key function on the value to
   be stored. IOW, the key,value pair is bound and stored 
   as one lump in the tree.
   This choice has been driven by the implementation needs of
   the PHP array. This is bad, I know, but I don't want to store
   the key twice): I should probably factor out the key of the 
   pair, and use references instead.
   
   
*)
module Rbtree =
struct

  let debug x = (* prerr_string x; prerr_newline*) ()

  module type OrderedType =
  sig 
    type key_t
    type 'a t
    val get_key : 'a t  -> key_t
    val compare : key_t -> key_t -> int
    val string_of_key : key_t -> string
  end

  module Make (O: OrderedType ) =
  struct
 
    type color_t = Red | Black

    type 'a content_t = Content of 'a O.t | EmptyContent

    type ('a) node_t =   
	Node of color_t * ('a content_t) * ('a node_t) * ('a node_t) 

    type 'a t = 'a node_t

    let rec empty_leaf =  Node (Black, EmptyContent, empty_leaf, empty_leaf)
      
    let create_leaf () = empty_leaf
      
    let create () = create_leaf ()
      
    let create_node v = Node(Red, Content v, create_leaf (), create_leaf ())

    let is_empty x = match x with (_,EmptyContent,_,_) -> true | _ -> false
  
    let get_content node = match node with Node (_,Content v,_,_) -> v | Node (_,EmptyContent,_,_) -> raise Not_found 

    let string_of_value x = O.string_of_key (O.get_key x)

    type compare_t = Below | Equal | Above 
	
    let compare_k_v k v = 
      let c = O.compare k (O.get_key v) in
	if c < 0 then Below else if c > 0 then Above else Equal
	     
    let dump tree filename filedir =
      let file = open_out (filedir^"/"^filename^".dot") in
	  
      let dump_link parent x child =
	output_string file (parent^":"^x^" -> "^child^":n;\n")
	  
      and make_id node = 
	match node with 
	    Node(_,EmptyContent,_,_) -> ""
	  | Node(_,Content v,_,_)    -> O.string_of_key (O.get_key v)

      and string_of_color c = match c with Black -> "Black" | Red -> "Red" 

      in
      let record_struct id c l r =
 	(id^" [ label = \" <l> | <c> "^(string_of_color c)^" | <v> "^(id)^" | <r> \" ];")
	
      in
	
      let rec dump_r parent x node =
	match node with
	    Node(_,EmptyContent, _, _)       -> ()
	  | Node (c, Content v, l, r)        -> 
	      let id = make_id node in 
		dump_link parent x id; 
		output_string file (record_struct id c l r);
		dump_r id "l" l;
		dump_r id "r" r
	      
      in 
	output_string file ("digraph "^filename^" {\n");
	output_string file ("name ="^filename^";\n");
	output_string file "node [shape=record];\n";
	dump_r "root" "n" tree;
	output_string file "}";
	close_out file

    (* -- consistency check function ------ *)

    exception Inconsistency of  (O.key_t) * int * int

    let check tree =
      let rec comp v l r nc =
	let lc = check_ l nc
	and rc = check_ r nc
	in
	  if lc <> rc 
	  then raise (Inconsistency (O.get_key v, lc, rc))
	  else lc

      and check_ node c =
	match node with
	    Node (_,EmptyContent,_,_)  -> c
	  | Node (Black,Content v,l,r) -> comp v l r (c+1)
	  | Node (Red  ,Content v,l,r) -> comp v l r c
		
      in check_ tree 0

    (* -- iterating functions etc ---- *)
	  
    let rec fold_left f acc tree =
      match tree with
	  Node (_, EmptyContent, _, _) -> acc
	| Node (_, Content v, l, r)    ->
	    fold_left f (f (fold_left f acc l) v) r

    let rec iter f tree =
      let f' s x = f x in fold_left f' () tree
			    

    (* -- add value to tree --------------- *)

    (* check wikipedia article for detailed explanations on the algorithms
       http://en.wikipedia.org/wiki/Red_black_tree
       there isn't any link back to parent nodes in the node type, thus we should have to check 
       the structure of each subtree - one check is done in constant time 
       (upper bound by the longest pattern matching below) 
       so it should still be O(log n) overall
       see below for a simple trick I came up with to avoid checking the whole thing 
    *)
    let add tree v =
      (* check_bal_* will check the node structure for cases as in the article 
	 node is the node to check
	 c is a counter to indicate if we need to do further checks up the tree
	 it allows to skip checking after a few rounds if it's not deemed necessary anymore
	 it passes my functional tests, but is it really safe? 
	 a new check is necessary only when "case 3" is matched, and then, 
	 it must be performed on the gparent only, which will perhaps call for another check on his own gp
      *)
      let check_bal_l node c =
	if c = 0
	then node, c
	else 
	match node with
	    
	    (*      [g]                   [g]                 [n]
	     *      / \                   / \                 / \
	     *    [p] [u]         =>    [n] [u]      =>     [p] [g]
	     *      \                   / \                   \ / \
	     *      [n]               [p]  nr                nl nr[u]
	     *      / \                 \
	     *     nl nr                nl
	     *) 
	    Node( Black, gpv, Node(Red, pv, pleft, Node( Red, nv, nl, nr)),(Node( Black, _, _, _) as u)) -> ( 
	      (* case 4 *) debug "case 4 l";
	      let ng = Node( Red, gpv,  nr, u) and np = Node( Red, pv, pleft, nl) 
	      in  Node ( Black, nv, np, ng), (c-1)
	    )
	      
	      
	  (*      [g]                [p]
	   *      / \                / \
	   *    [p] [u]      =>    [n] [g]
	   *    / \                    / \
	   *  [n] [pr]               [pr][u]
	   *) 
	  | Node( Black, gpv, Node( Red, pv, (Node ( Red, _, _, _) as n), pright), (Node( Black, _, _, _) as u)) -> (
	      (* case 5 *) debug "case 5 l";
	      let np =  Node ( Red, gpv, pright, u) 
	      in Node ( Black, pv, n, np), (c-1)
	    )
	      
	  | Node( Black, gpv, Node (Red, lv, lleft, lright) , Node( Red, rv, rleft, rright )) -> (
	      (* case 3 *) debug "case 3 l";
	      match lleft, lright, rleft, rright with (* we need one child to be red *)
		  Node(Red, _, _, _), _, _, _  
		| _, Node(Red, _, _, _), _, _ 
		| _, _, Node(Red, _, _, _), _
		| _, _, _, Node(Red, _, _, _)  ->
		    Node(Red, gpv, Node (Black, lv, lleft, lright), Node( Black, rv, rleft, rright)), (c+2)
		| _                               -> node, (c-1)
	    )
	  | _                                             -> debug "case else else l"; node, (c-1)
	      
	      
      and check_bal_r node c =
	if c = 0 
	then
	  node, c
	else
	match node with
	    
	    (*    [g]                   [g]                    [n] 
	     *    / \                   / \                    / \
	     *  [u] [p]         =>    [u] [n]        =>      [g] [p]
	     *      /                     / \                / \   
	     *    [n]                    nl [p]            [u]  nl
	     *    / \                       / 
	     *   nl nr                     nr
	     *) 
	    Node( Black, gpv, (Node( Black, _, _, _) as u), Node( Red, pv, Node( Red, nv, nl, nr), pright)) -> (
	      (* case 4 *) debug "case 4 r";
	      let ng = Node( Red, gpv, u, nl) and np = Node( Red, pv, nr, pright) 
	      in Node ( Black, nv, ng, np), (c-1)
	    )
	      
	  (*      [g]                 [p]
	   *      / \                 / \
	   *    [u] [p]       =>    [g] [n]
	   *        / \             / \
	   *      [pl][n]         [u] [pl]
	   *) 
	  | Node(  Black, gpv, (Node( Black, _, _, _) as u), Node(  Red, pv, pleft, (Node ( Red, _, _, _) as n))) -> (
	      (* case 5 *) debug "case 5 r";
	      let np = Node ( Red, gpv, u, pleft) 
	      in Node ( Black, pv, np, n), (c-1)
	    )
	  | Node( Black, gpv, Node (Red, lv, lleft, lright) , Node( Red, rv, rleft, rright )) -> (
	      (* case 3 *) debug "case 3 r"; 
	      match lleft, lright, rleft, rright with (* we need one child to be red *)
		  Node(Red, _, _, _), _, _, _  
		| _, Node(Red, _, _, _), _, _ 
		| _, _, Node(Red, _, _, _), _
		| _, _, _, Node(Red, _, _, _)  ->
		    Node(Red, gpv, Node (Black, lv, lleft, lright), Node( Black, rv, rleft, rright)), (c+2)
		| _                               -> node, (c-1)
	    )
	  | _                                             -> debug "case else else r"; node, (c-1)
      in

      let compare v1 v2 = compare_k_v (O.get_key v1) v2 in

      let rec add_r node v =
	match node with 
	    Node(nc, EmptyContent, _, _) -> create_node v, 2 (* insure that we're going to check at least parent and gparent *)
	  | Node(nc, Content nv, nl, nr) -> add_node nc nv nl nr v
	      
      and add_node nc nv nl nr v =
	match compare v nv with
	    Below -> (
	      let nnl, check =  add_r nl v 
	      in
		check_bal_l (Node(nc, Content nv, nnl, nr)) check
	    )
	  | Above -> (
	      let nnr, check = add_r nr v 
	      in
		check_bal_r (Node(nc, Content nv, nl, nnr)) check
	    )
	  | Equal -> Node(nc, Content v, nl, nr), 0
	      
      in match tree with
	  Node(nc, EmptyContent, _, _) -> create_node v
	| Node(nc, Content nv, nl, nr) -> fst (add_node Black nv nl nr v)
	   
    let find tree v =
    
      let rec find_ node v =
	match node with
	    Node(_,EmptyContent, _, _) -> raise Not_found
	  | Node(nc, Content nv, l, r) -> (
	      match compare_k_v v nv with
		  Below -> find_ l v
		| Above -> find_ r v
		| Equal -> nv
	    )

      in find_ tree v 
	      

    let remove tree k =
      
      (* check p structure according to cases described in the wikipedia article, 
	 returns the new node and a flag indicating if we have to do the check 
	 again at upper level (a variation of the trick above for node insertion)
	 the wikipedia article uses again the parent link to figure out which check 
	 to perform, but we don't have this information, thus we get the fact from
	 the recursive search down. One tricky situation arises from the fact
	 that our black nodes contains either Content or EmptyContent,and that 
	 an EmptyContent as itself for children, thus allowing more matches: 
	 we need to filter out the EmptyContent in some cases to really match the original
	 algorithm.
      *)
      let check_remove_l p c = 
	if not c then p, false else 
	let np =
	  match p with 
	      Node(Black, pv, (Node( Black,_,_,_) as n), Node(Red,sv,(Node(Black,_,_,_) as sl),(Node(Black,_,_,_) as sr))) -> 
		debug "check_remove_l: case 2";(* case 2 *)
		Node(Black, sv, Node(Red, pv, n, sl), sr)
	    | _  -> p
	in
	  match np with
	      Node(Black, pv, (Node( Black,_,_,_) as n), Node(Black,Content sv,(Node(Black,_,_,_) as sl),(Node(Black,_,_,_) as sr))) ->
		debug "check_remove_l: case 3";(* case 3 *)
		Node(Black, pv, n, Node(Red, Content sv, sl, sr)), true
	    | Node(Red, pv, (Node( Black,_,_,_) as n), Node(Black,Content sv,(Node(Black,_,_,_) as sl),(Node(Black,_,_,_) as sr))) -> 
		debug "check_remove_l: case 4";(* case 4 *)
		Node(Black, pv, n, Node(Red, Content sv, sl, sr)), false
		  
	    (*
	     *        [p]                [p]                      [sl]
	     *        / \                / \                      /  \
	     *      [n] [s]       =>   [n] [sl]         =>      [p]  [s]
	     *          / \                /  \                 / \   | \
	     *        [sl][sr]            sll [s]             [n] sll slr [sr]
	     *                                / \  
	     *                              slr [sr]
	     *)
	    | Node( pc, pv, n, Node(Black,sv,Node(Red,slv,sll,slr),(Node(Black,_,_,_) as sr))) -> 
		debug "check_remove_r: case 5+6";(* case 5 + 6 *)
		Node(pc,slv, Node (Black, pv, n, sll), Node(Black, sv, slr, sr)), false
	    | Node( pc, pv, n, Node(Black,sv,sl,(Node(Red,_,_,_) as sr))) -> 
		debug "check_remove_r: case 6";(* case 6 *)
		Node( pc, sv, Node(Black, pv, n, sl), sr), false
	    | _                                                            -> p, false


      (* same as above, for symmetrical cases : n on the right side *)
      and check_remove_r p c = 
	if not c then p, false else 
	let np =
	  match p with 
	      Node(Black, pv, Node(Red,sv,(Node(Black,_,_,_) as sl),(Node(Black,_,_,_) as sr)), (Node( Black,_,_,_) as n)) -> 
		debug "check_remove_r: case 2";(* case 2 *)
		Node(Black, sv, sl, Node(Red, pv, sr, n))
	    | _  -> p
	in
	  match np with
	      Node(Black, pv, Node(Black,Content sv,(Node(Black,_,_,_) as sl),(Node(Black,_,_,_) as sr)), (Node( Black,_,_,_) as n)) ->
		debug "check_remove_r: case 3";(* case 3 *)
		Node(Black, pv, Node(Red, Content sv, sl, sr), n), true
	    | Node(Red, pv, Node(Black,Content sv,(Node(Black,_,_,_) as sl),(Node(Black,_,_,_) as sr)), (Node( Black,_,_,_) as n)) -> 
		debug "check_remove_r: case 4";(* case 4 *)
		Node(Black, pv, Node(Red, Content sv, sl, sr), n), false
		  
	    (*
	     *        [p]                [p]                      [sr]
	     *        / \                / \                      /   \
	     *      [s] [n]      =>   [sr] [n]         =>      [s]    [p]
	     *      / \               / \                      / \     | \
	     *  [sl] [sr]           [s] srr                  [sl] srl srr [n]
	     *                      / \  
	     *                    [sl] srl
	     *)
	    | Node( pc, pv, Node(Black,sv,(Node(Black,_,_,_) as sl),Node(Red,srv,srl,srr)), n) -> 
		debug "check_remove_r: case 5+6";(* case 5 + 6 *)
		Node(pc,srv, Node(Black, sv, sl, srl), Node (Black, pv, srr, n)), false
	    | Node( pc, pv, Node(Black,Content sv,(Node(Red,_,_,_) as sl), sr), n) -> 
		debug "check_remove_r: case 6";(* case 6 *)
		Node( pc, Content sv, sl, Node(Black, pv, sr, n)), false

	    | _                                                            -> p, false
      in
	(* look for the target node to apply a swap and once done, 
	   apply one or more times a balance check *)
      let rec swap_remove_l node v =
	match node with
	    Node(x, Content y, (Node(_, EmptyContent, _, _) as z), Node(_, EmptyContent, _, _)) -> (* we found the target, and it's a leaf, just discard it *)
	      debug ("swap_remove_l: found leaf "^(string_of_value y));
	      z, y, true
	  | Node(x, Content y, Node(_, EmptyContent, _, _), z) -> (* we found the target, let's swap *)
	      debug ("swap_remove_l: found "^(string_of_value y));
 	      z, y, true
	  | Node(x, Content y, l, z)                                   -> (* dig down a bit more, and check the result *)
	      debug ("swap_remove_l: following "^(string_of_value y));
	      let nl, rv, check = swap_remove_l l v 
	      in 
	      let nnl, check = check_remove_l nl check 
	      in Node(x, Content y, nnl, z), rv, check
	  | Node(_, EmptyContent, _, _) -> raise Not_found (* this to remove a compiler warning *)

      and swap_remove_r node v =
	match node with
	    Node(x, Content y, (Node(_, EmptyContent, _, _) as z), Node(_, EmptyContent, _, _)) -> (* we found the target, and it's a leaf, just discard it *)
	      debug ("swap_remove_r: found leaf "^(string_of_value y));
	      z, y, true
	  | Node(x, Content y, z, Node(_, EmptyContent, _, _)) -> (* we found the target, let's swap *)
	      debug ("swap_remove_r: found "^(string_of_value y));
	      z, y, true
	  | Node(x, Content y, z, r)                                   -> (* dig down a bit more, and check the result *)
	      debug ("swap_remove_r: following "^(string_of_value y));
	      let nr, rv, check = swap_remove_r r v 
	      in 
	      let nnr,check = check_remove_r nr check
	      in Node(x, Content y, z, nnr), rv, check
	  | Node(_, EmptyContent, _, _) -> raise Not_found (* this to remove a compiler warning *)
		    
      (* look for the node to be deleted *)
      and remove_ node v =
	match node with
	    Node(_ , EmptyContent, _, _) -> raise Not_found
	  | Node(nc,   Content nv, l, r) -> 
	      debug ("remove: compare "^(O.string_of_key v)^" "^(string_of_value nv));
	      match compare_k_v v nv with
		  Below -> Node(nc, Content nv, remove_ l v, r)
		| Above -> Node(nc, Content nv, l, remove_ r v)
		| Equal -> 
		    match l, r with 
			Node(_, EmptyContent, _, _), Node(_, EmptyContent,_,_) -> l (* node has no child *)
		      | Node(_, EmptyContent, _, _), Node(_, _, rl, _)         ->   (* leftmost of right child for replacement *)
			  let nr, rv, check = swap_remove_l r v
			  in 
			  let nnr, _ = check_remove_l nr check
			  in Node(nc, Content rv, l, nnr)
		      | Node( _, _, _, lr), Node( _, _, _, _)                  ->   (* rightmost of left child for replacement *)
			  let nl, rv, check = swap_remove_r l v
			  in 
			  let nnl, _ = check_remove_r nl check
			  in Node(nc, Content rv, nnl, r)
      in remove_ tree k

  end
	 
end

