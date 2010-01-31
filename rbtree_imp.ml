(* red black tree implementation - imperative style 
*)

module Rbtree_imp =
struct

  let debug x = (* prerr_string x; prerr_newline *) ()

  module type OrderedType =
  sig 
    type t
    type key_t
    val get_key : t     -> key_t
    val compare : key_t -> key_t -> int
    val string_of_key : key_t -> string
  end

  module Make (O: OrderedType ) =
  struct
 
    type color_t = Red | Black

    type content_t = Content of O.t | EmptyContent

    type node_t  = {mutable c: color_t; mutable v: content_t;mutable l: node_t;mutable r: node_t}

    type t = {mutable root: node_t}

    let rec empty_leaf = {c=Black;v=EmptyContent;l=empty_leaf;r=empty_leaf}

    let create_leaf () = empty_leaf

    let create () = {root=create_leaf ()}
  
    let create_node v =  {c=Red;v=Content v;l=empty_leaf;r=empty_leaf}

    let is_empty x = match x.v with EmptyContent -> true | _ -> false
  
    let get_content node = match node.v with Content v -> v | _ -> raise Not_found 

    let string_of_value x = O.string_of_key (O.get_key x)

    type compare_t = Below | Equal | Above 
	
    (* compare a given key to a key embedded in a value *)
    let compare_k_v k v = 
      let c = O.compare k (O.get_key v) in
	if c < 0 then Below else if c > 0 then Above else Equal

    let string_of_color c = match c with Black -> "Black" | _ -> "Red"

    let rec string_of_node node =
      match node.v with
	  EmptyContent         -> "{"^(string_of_color node.c)^";empty}"
	| Content v            -> "{"^(string_of_color node.c)^";"^(string_of_value v)^";"^(string_of_node node.l)^";"^(string_of_node node.r)^"}"

    let dump tree filename filedir =
      let file = open_out (filedir^"/"^filename^".dot") in
	  
      let dump_link parent x child =
	output_string file (parent^":"^x^" -> "^child^":n;\n")
	  
      and make_id node = 
	match node.v with 
	    EmptyContent -> ""
	  | Content v    -> O.string_of_key (O.get_key v)

      and dump_empty name =
	output_string file (name^" [ label = \"empty\"];")

      in
      let record_struct node =
	let id = make_id node in
 	(id^" [ label = \" <l> | <c> "^(string_of_color node.c)^" | <v> "^(id)^" | <r> \" ];")
	
      in
      let rec dump_ parent x node =
	match node.v with
	    EmptyContent         -> let e = (x^parent) in (dump_link parent x e;dump_empty e)
	  | Content v            -> 
	      let id = make_id node in 
		dump_link parent x id; 
		output_string file (record_struct node);
		dump_ id "l" node.l;
		dump_ id "r" node.r
		  
      in 
	output_string file ("digraph "^filename^" {\n");
	output_string file ("name ="^filename^";\n");
	output_string file "node [shape=record];\n";
	dump_ "root" "n" tree.root;
	output_string file "}";
	close_out file

    (* -- iterating functions etc ------------- *)
	  
    let fold_left f acc tree =
      let rec fold_left_ f acc node =
	match node.v with
	    EmptyContent -> acc
	  | Content v    ->
	      fold_left_ f (f (fold_left_ f acc node.l) v) node.r
		
      in fold_left_ f acc tree.root
	   
    let iter f tree =
      let f' s x = f x in fold_left f' () tree
			    
    (* -- in place node rotation functions ---- *)

    (*          [g]                 [p]
     *          / \                 / \
     *        [u] [p]      =>     [g] [n]
     *            / \             / \
     *           nl [n]         [u]  nl
     *) 
    let rotate_left node =
      let u  = node.l
      and nr = node.r.l
      and p  = node.r.r
      and gv = node.v
      and nv = node.r.v
      in
	node.l   <- node.r;
	node.r   <- p;
	node.l.r <- nr;
	node.l.l <- u;
	node.v   <- nv;
	node.l.v <- gv

    (*          [g]                 [p]
     *          / \                 / \
     *        [p] [u]      =>     [n] [g]
     *        / \                     / \
     *      [n]  nr                  nr [u]
     *) 
    let rotate_right node =
      let u  = node.r
      and nr = node.l.r
      and p  = node.l.l
      and gv = node.v
      and nv = node.l.v
      in
	node.r   <- node.l;
	node.l   <- p;
	node.r.l <- nr;
	node.r.r <- u;
	node.v   <- nv;
	node.r.v <- gv
	      
    (* -- consistency check function ------ *)

    exception Inconsistency of O.t * int * int

    let check tree =

      let rec check_ node c =
	match node.v with
	    EmptyContent  -> c
	  | Content v     -> 
	      let nc =
		match node.c with
		    Black -> c+1
		  | Red   -> c
	      in
	      let lc = check_ node.l nc
	      and rc = check_ node.r nc
	      in
		if lc <> rc 
		then raise (Inconsistency (v, lc, rc))
		else lc
		
      in check_ tree.root 0

    (* -- add value to tree --------------- *)

    (* check wikipedia article for detailed explanations on the algorithms
       http://en.wikipedia.org/wiki/Red_black_tree
    *)
    let add tree v =

      (* check_bal_* will check the node structure for cases as in the article 
	 node is the node to check
      *)
      let check_bal_l node c =
	if c = 0
	then c
	else 
	match node.c, node.l.c, node.r.c with
	    
	    (*      [g]                   [g]                 [n]
	     *      / \                   / \                 / \
	     *    [p] [u]         =>    [n] [u]      =>     [p] [g]
	     *      \                   / \                   \ / \
	     *      [n]               [p]  nr                nl nr[u]
	     *      / \                 \
	     *     nl nr                nl
	     *) 
	    Black,Red,Black when node.l.r.c = Red -> ( 
	      (* case 4 + 5 *) debug "case 4 l";
	      let nl = node.l.r.l
	      and p  = node.l
	      and n  = node.l.r
	      in
		node.l     <- n;
		node.l.l   <- p;
		node.l.l.r <- nl;
		rotate_right node;
		node.c   <- Black;
		node.l.c <- Red;
		node.r.c <- Red;
		c-1
	    )
	      
	  (*      [g]                [p]
	   *      / \                / \
	   *    [p] [u]      =>    [n] [g]
	   *    / \                    / \
	   *  [n] [pr]               [pr][u]
	   *) 
	  | Black,Red,Black when node.l.l.c = Red -> (
	      (* case 5 *) debug "case 5 l";
	      rotate_right node;
	      node.c   <- Black;
	      node.l.c <- Red;
	      node.r.c <- Red;
	      c-1
	    )
	      
	  | Black, Red, Red                       -> (
	      (* case 3 *) debug "case 3 l";
	      match node.l.l.c, node.l.r.c, node.r.l.c, node.r.r.c with (* we need one child to be red *)
		  Red, _, _, _  
		| _, Red, _, _
		| _, _, Red, _
		| _, _, _, Red  ->
		    node.c   <- Red;
		    node.l.c <- Black;
		    node.r.c <- Black;
		    c+2
		| _             -> (c-1)
	    )
	  | _                                     -> debug "case else else l"; (c-1)
	      
      and check_bal_r node c =
	if c = 0 
	then
	  c
	else
	  match node.c, node.l.c, node.r.c with
	    
	    (*    [g]                   [g]                    [n] 
	     *    / \                   / \                    / \
	     *  [u] [p]         =>    [u] [n]        =>      [g] [p]
	     *      /                     / \                / \   
	     *    [n]                    nl [p]            [u]  nl
	     *    / \                       / 
	     *   nl nr                     nr
	     *) 
	    Black, Black, Red when node.r.l.c = Red -> (
	      (* case 4+5 *) debug "case 4 r";
	      let nr  = node.r.l.r
	      and p   = node.r
	      and n   = node.r.l
	      in
		node.r     <- n;
		node.r.r   <- p;
		node.r.r.l <- nr;
		rotate_left node;
		node.c   <- Black;
		node.r.c <- Red;
		node.l.c <- Red;
		c-1
	    )
	      
	  (*      [g]                 [p]
	   *      / \                 / \
	   *    [u] [p]       =>    [g] [n]
	   *        / \             / \
	   *      [pl][n]         [u] [pl]
	   *) 
	  | Black, Black, Red when node.r.r.c = Red -> (
	      (* case 5 *) debug "case 5 r";
	      rotate_left node;
	      node.c   <- Black;
	      node.r.c <- Red;
	      node.l.c <- Red;
	      c-1
	    )

	  | Black, Red, Red                         -> (
	      (* case 3 *) debug "case 3 r"; 
	      match node.l.l.c, node.l.r.c, node.r.l.c, node.r.r.c with (* we need one child to be red *)
		  Red, _, _, _  
		| _, Red, _, _
		| _, _, Red, _
		| _, _, _, Red  ->
		    node.c   <- Red;
		    node.l.c <- Black;
		    node.r.c <- Black;
		    c+2
		| _             -> (c-1)
	    )
	  | _                                       -> debug "case else else r"; (c-1)


      in

      let compare v1 v2 = compare_k_v (O.get_key v1) v2 in

      let rec add_r parent node v =
	match node.v with 
	    EmptyContent ->
	      parent.r <- (create_node v); 2 (* insure that we're going to check at least parent and gparent *)
	  | Content nv   -> 
	      match compare v nv with
		  Below -> check_bal_l node (add_l node node.l v)
		| Above -> check_bal_r node (add_r node node.r v)
		| Equal -> node.v <- Content v; 0
		      
      and add_l parent node v =
	match node.v with 
	    EmptyContent ->
	      parent.l <- (create_node v); 2 (* insure that we're going to check at least parent and gparent *)
	  | Content nv   -> 
	      match compare v nv with
		  Below -> check_bal_l node (add_l node node.l v)
		| Above -> check_bal_r node (add_r node node.r v)
		| Equal -> node.v <- Content v; 0
 
      in (
	match tree.root.v with
	    EmptyContent -> tree.root <- create_node v
	  | Content tv   -> 
	      match compare v tv with
		  Below -> ignore (check_bal_l tree.root (add_l tree.root tree.root.l v)); tree.root.c <- Black
		| Above -> ignore (check_bal_r tree.root (add_r tree.root tree.root.r v)); tree.root.c <- Black
		| Equal -> tree.root.v <- Content v; tree.root.c <- Black
	)
	   
    let find tree k =
    
      let rec find_ node k =
	match node.v with
	    EmptyContent -> raise Not_found
	  | Content nv   -> (
	      match compare_k_v k nv with
		  Below -> find_ node.l k
		| Above -> find_ node.r k
		| Equal -> nv
	    )

      in find_ tree.root k 

	      
    let remove tree k =

      (* check p structure according to cases described in the wikipedia article,
	 with n on the left. since we're basing all check from p, the "case 2" rotation 
	 changing the node configuration invalidates tests 4,5,6 afterward as in
	 the article. Thus we need to amend the tests to take that rotation in account
      *)

      (*    modified node (left), sibling (right), sibling children *)
      let rec check_remove_l p c = 
	let debug x = let v = match p.v with Content v -> string_of_value v | _ -> "" in  debug ("check_remove_l: "^x^" - "^v) 
	in 
	let check3456 p =
	  match p.c, p.l.c, p.r.c, p.r.r.c, p.r.l.c with
	      Black, Black, Black, Black, Black ->
		debug "case 3";(* case 3 *)
		p.r.c <- Red;
		true
	    | Red, Black, Black, Black, Black   -> 
		debug "case 4";(* case 4 *)
		p.c   <- Black; 
		p.r.c <- Red;
		false
	    (*
	     *        [p]                [p]                      [sl]
	     *        / \                / \                      /  \
	     *      [n] [s]       =>   [n] [sl]         =>      [p]  [s]
	     *          / \                /  \                 / \   | \
	     *        [sl][sr]            sll [s]             [n] sll slr [sr]
	     *                                / \  
	     *                              slr [sr]
	     *)
	    | _, Black, Black, Black, Red       ->
		debug "case 5+6";(* case 5 + 6 *)
		let pc = p.c in
		  (* change sl color *)
		  p.r.l.c <- Black;
		  (* rotate right s *)
		  rotate_right p.r;
		  (* rotate left p *)
		  rotate_left p;
		  (* change s color *)
		  p.r.c <- Black;
		  (* put p color back *)
		  p.c   <- pc;
		  false
	    (*
	     *        [p]                [s]
	     *        / \                / \     
	     *      [n] [s]       =>   [p] [sr] 
	     *          / \            / \     
	     *        [sl][sr]       [n] [sl] 
	     * 
	     *)
	    | _, Black, Black, Red, _       ->
		debug "case 6";(* case 6 *)
		let pc = p.c in
		  rotate_left p;
		  p.r.c <- Black;
		  p.l.c <- Black;
		  p.c   <- pc;
		  false
	    | _                                 -> debug "case else"; false

	in
	if not c then false else (
	  debug "testing";
	  match p.v with 
	      EmptyContent -> c
	    | _            -> 
	  (* sibling color *)
		match p.r.c, p.r.v with
		    Red, Content _ -> debug "case 2"; rotate_left p; p.l.c <- Red; p.c <- Black;check_remove_l p (check3456 p.l)
		  | _              -> check3456 p
	)
      (* same as above, for symmetrical cases : n on the right side *)
      and check_remove_r p c = 
	let debug x = let v = match p.v with Content v -> string_of_value v | _ -> "" in  debug ("check_remove_r: "^x^" - "^v) 
	in 
	let check3456 p = 
	  match p.c, p.r.c, p.l.c, p.l.l.c, p.l.r.c with
	      Black, Black, Black, Black, Black ->
		debug "case 3";(* case 3 *)
		p.l.c <- Red;
		true
	    | Red, Black, Black, Black, Black  -> 
		debug "case 4";(* case 4 *)
		p.c   <- Black; 
		p.l.c <- Red;
		false
	    (*
	     *        [p]                [p]                      [sr]
	     *        / \                / \                      /   \
	     *      [s] [n]      =>   [sr] [n]         =>      [s]    [p]
	     *      / \               / \                      / \     | \
	     *  [sl] [sr]           [s] srr                  [sl] srl srr [n]
	     *                      / \  
	     *                    [sl] srl
	     *)
	    | _, Black, Black, Black, Red ->
		 debug "case 5+6";(* case 5 + 6 *)
		let pc = p.c in
		  p.l.r.c <- Black;
		  rotate_left p.l;
		  rotate_right p;
		  p.l.c <- Black;
		  p.c   <- pc;
		  false
	    (*
	     *        [p]                [s]
	     *        / \                / \
	     *      [s] [n]      =>   [sl] [p]
	     *      / \                    / \
	     *  [sl] [sr]               [sr] [n]
	     *                      
	     *)
	    | _, Black, Black, Red, _ ->
		 debug "case 6";(* case 6 *)
		let pc = p.c in
		  rotate_right p;
		  p.l.c <- Black;
		  p.r.c <- Black;
		  p.c   <- pc;
		  false
	    |  _                                -> debug "case else"; false

      in
	if not c then false else ( 
	  debug "testing";
	  match p.v with 
	      EmptyContent -> c
	    | _            -> 
		match p.l.c, p.l.v with
		    Red, Content _ -> debug "case 2"; rotate_right p; p.r.c <- Red; p.c <- Black; check_remove_r p (check3456 p.r)
		  | _              -> check3456 p
	)


      in

      let check_color n1 n2 =
	match n1.c, n2.c with
	    Red, Black -> false
	  | Black, Red -> n2.c <- Black; false
	  | _          -> true 
      in
      (* look for the left most child, and swap value *)
      let rec swap_remove_l node v =
	match node.v, node.l.v, node.r.v with
	    Content y, EmptyContent, EmptyContent ->
	      debug ("swap_remove_l: found "^(string_of_value y));
 	      node.r, y, (node.c = Black)
	  | Content y, EmptyContent, _            -> (* we found the target, let's swap *)
	      debug ("swap_remove_l: found "^(string_of_value y));
 	      node.r, y, (check_color node node.r)
	  | _                                     -> (* dig down a bit more, and check the result *)
	      debug ("swap_remove_l: following "^(string_of_value (get_content node)));
	      let nl, rv , check = swap_remove_l node.l v 
	      in 
		node.l <- nl; 
		let check = check_remove_l node check
		in
		  node, rv ,check
		  
      (* look for the right most child, and swap value *)
      and swap_remove_r node v =
	match node.v, node.r.v, node.l.v with
	    Content y, EmptyContent, EmptyContent -> (* we found the target, let's swap *)
	      debug ("swap_remove_r: found leaf "^(string_of_value y));
 	      node.l, y, (node.c = Black)
	  | Content y, EmptyContent, _            -> (* we found the target, let's swap *)
	      debug ("swap_remove_r: found "^(string_of_value y));
 	      node.l, y, (check_color node node.l)
	  | _                                     -> (* dig down a bit more, and check the result *)
	      debug ("swap_remove_r: following "^(string_of_value (get_content node)));
	      let nr, rv, check = swap_remove_r node.r v 
	      in 
		node.r <- nr;
		let check = check_remove_r node check
		in 
		  node, rv, check

		  
      (* look for the node to be deleted *)
      and remove_ node v =
	match node.v with
	    EmptyContent                  -> raise Not_found
	  | Content nv                    -> 
	      debug ("remove: compare "^(O.string_of_key v)^" "^(string_of_value nv));
	      match compare_k_v v nv with
		  Below ->
		    let nl, check, rv = remove_ node.l v in
		      node.l <- nl; node, check_remove_l node check, rv
		| Above ->
		    let nr, check, rv = remove_ node.r v in
		      node.r <- nr; node, check_remove_r node check, rv
		| Equal ->
		    match node.l.v, node.r.v with 
			EmptyContent, EmptyContent -> empty_leaf, (node.c = Black), nv (* node has no child *)
		      | EmptyContent, _            ->                              (* leftmost of right child for replacement *)
			  let nr, rv, check = swap_remove_l node.r v 
			  in 
			    node.v <- Content rv; 
			    node.r <- nr; 
			    node, check_remove_r node check, nv
		      | _                          ->                              (* rightmost of left child for replacement *)
			  let nl, rv, check = swap_remove_r node.l v
			  in 
			    node.v <- Content rv; 
			    node.l <- nl;
			    node, check_remove_l node check, nv

      in 
      let n, _, rv = remove_ tree.root k
      in tree.root <- n; rv

  end
	 
end

