(*
  Btree implementation
  
  Copyright (C) 2010,2011  Didier Cassirame
  
  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.
  
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  
  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
  
*)

open Array

let debug_mode = true

let debug = if debug_mode then (fun s -> prerr_string s;prerr_newline ()) else (fun s -> ())

module type BtreeConf = 
sig
  type key_t
  type value_t
  val compare       : key_t -> key_t -> int
  val max           : int 
  val string_of_key : key_t -> string
end

(* common types to both implementations *)
module Common (O : BtreeConf) =
struct

  type key_t   = O.key_t
  type value_t = O.value_t

  (* some constants *)
  let a_min   = (O.max / 2)                 (* minimum number of used cells *)
  let a_max   = O.max                       (* maximum number of used cells *)
  let a_med   = a_min + (O.max mod 2)       (* median index *)
    
  let dicho_threshold = 9                   (* btree of median above this value will use dichotomic search -
					       the gain is marginal for values below  
					    *)

  type cell_t = 
      EmptyCell 
    | Cell of (key_t * value_t)       
	
  and  node_t = 
      EmptyNode
    | Leaf of ((cell_t) array )                    (* array of cells *)
    | Node of ((node_t) array * (cell_t) array )   (* array of cells + intervals *)


  let create_cell_array ()     = Array.make (a_max+1) EmptyCell 
    
  let create_interval_array () = Array.make (a_max+2) EmptyNode
    
  let create_empty_leaf ()     = 
    let a = create_cell_array () in
    Leaf (a) 

  let set_cell a i c = a.(i) <- c
  let get_cell a i = a.(i)

  let get_sub s i = s.(i)
  let set_sub s i v = s.(i) <- v
    

  (* -- internal utils functions ---------------- *)

  let size_ v limit a = 
    let i = ref 0 in
    while ((!i < limit) && (a.(!i) <> v)) do incr i done; !i

  let size_cells = size_ EmptyCell (a_max+1) 

  let size_nodes = size_ EmptyNode (a_max+2)

  let is_full a = a.(a_max)<>EmptyCell

  let is_underflow a = (a.(a_min-1)=EmptyCell)

  let get_key x = match x with
      EmptyCell  -> ""
    | Cell (a,b) -> O.string_of_key a


  (* -- comparison values filter ---------------- *)

  type compare_t = Below | Above | Equal

  let compare k1 k2 = let c = O.compare k1 k2 in
		      if c < 0 then Below else if c > 0 then Above else Equal



  (* -- add node utils ------------------------- *)

  (* extract the second half of the cell array a starting from med_idx *)
  let extract_second_half med_idx min_idx a =
    let na = create_cell_array () 
    and median = a.(med_idx)
    in 
    blit a (med_idx+1) na 0 min_idx;          (* copy the second half of the cells      *)
    fill a (med_idx) (min_idx+1) EmptyCell;   (* erase them from the full node          *)
    (median,na)

  (* -- remove node utils ---------------------- *)

  let guard_ia = 
    if debug_mode 
    then (fun name f ->
      try (
	f
      ) with Invalid_argument x -> raise (Invalid_argument (name^": "^x))
    )
    else (fun _ f -> f)
      
 
end

module Mutable =
struct

  module type S =
  sig

    type key_t
    type value_t

    type t
      
    val create    : unit -> t

    val fold_left : ('a -> key_t -> value_t -> 'a) -> 'a -> t -> 'a
    val iter      : t -> (key_t -> value_t -> unit) -> unit
    val find      : t -> key_t -> value_t
    val add       : t -> key_t -> value_t -> unit
    val remove    : t -> key_t -> unit

    val dump      : t -> string -> string -> unit

  end

  module Make (O: BtreeConf) : S with type key_t = O.key_t and type value_t = O.value_t =
  struct

    include Common(O)

    type t = {mutable root: node_t}


    let create () = {root = create_empty_leaf ()}

    (* - array manipulation -- *)

    (* shift right of count elements the array a in b *)
    let shift_r count a = 
      try (
	blit a 0 a (count) ((Array.length a) - count)
      ) with Invalid_argument x -> raise (Invalid_argument ("shift_r:"^x))
	
    (* shift left of count elements the array a in b *)
    let shift_l count a = 
      try (
	blit a (count) a 0 ((Array.length a) - count)
      ) with Invalid_argument x -> raise (Invalid_argument ("shift_l:"^x))


    (* 3 [ 1 2 3 4 5 6 7 ] -> [ 1 2 3 4 _ _ _ ]  *)
    (* fill the last n entries in array a with value *)
    let fill_end value a n =
      let l = Array.length a in
      fill a (l-n) n value
	
    let clear_cells = fill_end EmptyCell
      
    let clear_nodes = fill_end EmptyNode
      
    (* shift 1 step on the right elements of a starting at position i (element i is duplicated) *)
    let shift_right a i c = 
      try (
	blit a 0 a 0 i;
	blit a i a (i+1) ((Array.length a) - i - 1);
	a.(i) <- c
      ) with Invalid_argument x -> raise (Invalid_argument ("shift_right:"^x))

    (* shift 1 step on the left elements of a starting at position i+1 (we loose element i) *)
    (* [ 1 2 3 4 5 6 ] -> [ 1 3 4 5 6 _ ]  *)
    let shift_left  a i = 
      try (
	blit a 0 a 0 (pred i);
	blit a (i+1) a i ((Array.length a) - i - 1)
      ) with Invalid_argument x -> raise (Invalid_argument ("shift_left:"^x))


    (* - iterators etc.... -------------------------- *)

    let fold_left f acc tree =
      let rec fold_node f acc node =
	let racc = ref acc in
	match node with
	    EmptyNode  -> acc
	  | Node (s,a) -> 
	    for i=0 to a_max do 
	      racc := fold_cell f (fold_node f (!racc) (get_sub s i)) (get_cell a i)
	    done; 
	    fold_node f (!racc) (get_sub s (a_max+1))
	  | Leaf (a)   -> 
	    for i=0 to a_max do 
	      racc := fold_cell f !racc (get_cell a i) 
	    done; !racc

      and fold_cell f acc cell =
	match cell with
	    EmptyCell      -> acc
	  | Cell(k, v)     -> (f acc k v)

      in fold_node f acc tree.root 

    let size t =
      let f acc k v = succ acc
      in
      fold_left f 0 t

    let iter tree f =
      let f' () = f 
      in fold_left f' () tree

      
    (* dump a tree structure in a dotty file *)
    let dump tree filename directory =
      let file = open_out (directory^"/"^filename^".dot") in
      
      let dump_link parent child =
	output_string file (parent^" -> "^child^":n;\n")
	  
      and range cells = 
	let sz = size_cells cells in
	if sz = 0 then 0,"n_empty_"
	else
	  match cells.(0), cells.(sz-1) with
	      Cell(k0,v0), Cell(k1,v1) ->
		sz, ("n_"^(O.string_of_key k0)^"_"^(O.string_of_key k1)^"_")
	    | _                              -> invalid_arg "Btree.range"
	      
      and record_struct node cells = 
	let rec build_lbl s i = 
	  if i = O.max then (s^"\" ];")
	  else 
	    match cells.(i) with
		Cell(k,_) -> build_lbl (s^" | <l"^(string_of_int (i+1))^"> "^(O.string_of_key k)^" | <i"^(string_of_int (i+1))^"> ") (i+1)
	      | EmptyCell   -> (s^"\" ];\n")
	in build_lbl (node^" [ label = \"<i0> ") 0

      in
      let rec dump_r parent node =
	match node with
	    EmptyNode  -> debug "dump_r: empty node";()
 	  | Node (s,a) -> dump_node parent s a
	  | Leaf (a)   -> dump_leaf parent a
	    
      and dump_node parent s cells =
	let sz, id = range cells in
	dump_link parent id;
	output_string file (record_struct id cells);
	for i = 0 to (sz) do
	  dump_r (id^":i"^(string_of_int i)) s.(i)
	done

      and dump_leaf parent cells =
	let sz, id = range cells in
	dump_link parent id;
	output_string file (record_struct id cells)

      in 
      output_string file ("digraph "^filename^" {\n");
      output_string file ("name ="^filename^";\n");
      output_string file "node [shape=record];\n";
      (match tree.root with
	  Leaf (a)   -> if size_cells a > 0 then dump_leaf "root" a else ()
	| _          -> dump_r "root" tree.root);
      output_string file "}";
      close_out file


    (* -- find a value in tree -------------------- *)
	
    (* a 0 b 1 c 2 d 3 e 4 f 5 g 6 h 7 i *)

    let find =
      let find_dicho tree k =
	let dicho i = if i = 1 then 0 else (i lsr 1) + (i mod 2) in
	let rec find_node node k =
	  match node with
	      EmptyNode   -> raise Not_found
	    | Leaf (a)    -> find_leaf_r a k (a_med) (a_med)
	    | Node (s,a)  -> find_node_r a s k (a_med) (a_med)
	      
	and find_leaf_r cells k i j = 
	  debug ("find_leaf: checking "^(string_of_int i)^" "^(string_of_int j));
	  let j' = dicho j in
	  match get_cell cells i with 
	      EmptyCell    -> if j=0 then raise Not_found else find_leaf_r cells k (i-j') (j')
	    | Cell(ck,v)   ->
	      debug ("key = "^(O.string_of_key ck));
	      match compare k ck with
		  Below -> if j=0 then raise Not_found else find_leaf_r cells k (i-j') (j')
		| Equal -> v
		| Above -> if j=0 then raise Not_found else find_leaf_r cells k (i+j') (j')
		    
	and find_node_r cells s k i j =
	  debug ("find_node: checking "^(string_of_int i)^" "^(string_of_int j));
	  let j' = dicho j in
	  match get_cell cells i with 
	      EmptyCell       -> if j=0 then find_node (get_sub s i) k else find_node_r cells s k (i-j') (j')
	    | Cell(ck, v)     -> 
	      debug ("key = "^(O.string_of_key ck));
	      match compare k ck with
		  Below -> if j=0 then find_node (get_sub s i) k else find_node_r cells s k (i-j') (j')
		| Equal -> v
		| Above -> if j=0 then find_node (get_sub s (i+1)) k else find_node_r cells s k (i+j') (j')
		    
	in 
	debug ("searching: "^(O.string_of_key k));
	find_node tree.root k

      and find_linear tree k =
	let rec find_node node k =
	  match node with 
	      EmptyNode   -> raise Not_found
	    | Leaf (a)    -> find_leaf_r a k 0
	    | Node (s,a)  -> find_node_r a s k 0
	      
	and find_leaf_r cells k i = 
	  match get_cell cells i with 
	      EmptyCell    -> raise Not_found
	    | Cell(ck,v)   ->
	      match compare k ck with
		  Below -> raise Not_found
		| Equal -> v
		| Above -> find_leaf_r cells k (i+1)
		  
	and find_node_r cells s k i =
	  if i = a_max 
	  then 
	    find_node (get_sub s i) k 
	  else 
	    match get_cell cells i with 
		EmptyCell       -> find_node (get_sub s i) k
	      | Cell(ck, v)     -> match compare k ck with
		  Below -> find_node (get_sub s i) k
		  | Equal -> v
		  | Above -> find_node_r cells s k (i+1)
		    
	in 
	find_node tree.root k

      in if a_med > dicho_threshold 
	then find_dicho 
	else find_linear


    (* -- add a value in tree -------------------- *)

    let add tree k v =

      (* split a leaf node in 2 and returns the median value *)
      (* ex: [ 1 2 3 4 5 ] -> [ 1 2 ] [3] [ 4 5 ] *)
      let split_leaf =
	let split_leaf_even a =
	  let median, na = extract_second_half a_min a_min a
	  in
	  Some(median,Leaf(na))
	and split_leaf_odd a =
	  let median, na = extract_second_half a_med a_min a
	  in
	  Some(median,Leaf(na))
	in
	if (a_max mod 2) = 0
	then split_leaf_even
	else split_leaf_odd

	  
      (* split an internal node in 2 and returns the median value *)
      (* [ a 1 b 2 c 3 d 4 e 5 f ] -> [a 1 b 2 c ] [3] [ d 4 e 5 f ] *)
      and split_node =
	let extract_second_half_interval med_idx min_idx s =
	  let ns = create_interval_array ()
	  in 
	  blit s med_idx ns 0 min_idx;          (* copy the second half of the nodes      *)
	  fill s med_idx min_idx EmptyNode;     (* erase them from the full node          *)
	  ns
	in
	let split_node_even s a = 
	  let median, na = extract_second_half a_min a_min a
	  and ns = extract_second_half_interval (a_min+1) (a_min+1) s
	  in
	  Some(median,Node(ns,na))                (* return the copy as a median + new node *)
	and split_node_odd s a =
	  let median, na = extract_second_half a_med a_min a
	  and ns =  extract_second_half_interval (a_med+1) a_med s
	  in 
	  Some(median,Node(ns,na))                (* return the copy as a median + new node *)
	    
	in if (a_max mod 2) = 0 
	  then split_node_even
	  else split_node_odd
	    
      in
      let rec add_r node k v =
	match node with
	    EmptyNode -> Some(Cell(k,v), EmptyNode)
	  | Leaf(a)   -> add_to_leaf a k v
	  | Node(s,a) -> add_to_node s a k v
	    
      and add_to_leaf a k v =
	let check_overflow a =
	  if is_full a then split_leaf a else None
	in
	let rec add_leaf_r a k v i =
	  match get_cell a i with 
	      EmptyCell   -> set_cell a i (Cell(k,v)); check_overflow a
	    | Cell(ck,cv) -> 
	      match compare k ck with
		  Above -> add_leaf_r a k v (i+1)
		| Below -> (shift_right a i (Cell(k,v)); check_overflow a)
		| Equal -> (set_cell a i (Cell(k,v)); None)
	in add_leaf_r a k v 0
	
      and add_to_node s a k v = 
	let rec add_node_r s a k v i =
	  let check_bubble b =
	    match b with
		None        -> None
	      | Some((m,n)) -> (
		shift_right a i m; 
		shift_right s (i+1) n; 
		if is_full a then split_node s a else None
	      )
	  in
	  match get_cell a i with 
	      EmptyCell   -> check_bubble (add_r (get_sub s i) k v)
	    | Cell(ck,cv) -> (
	      match compare k ck with
		  Above -> add_node_r s a k v (i+1)
		| Below -> check_bubble (add_r (get_sub s i) k v)
		| Equal -> set_cell a i (Cell(k,v)); None
	    )
	in add_node_r s a k v 0
	
      in let check_root_bubble tree b =
	   match b with
	       None       -> ()
	     | Some (m,n) -> 
	       let c = create_cell_array () 
	       and i = create_interval_array () 
	       in ignore ( 
		 set_sub i 0 tree.root;
		 set_sub i 1 n; 
		 set_cell c 0 m; 
		 tree.root <- Node(i,c)
	       )
	       
	 in match tree.root with
	     EmptyNode  -> 
	       let c = create_cell_array () 
	       in set_cell c 0 (Cell(k,v))
	   | Leaf (a)   -> check_root_bubble tree (add_to_leaf a k v)
	   | Node (s,a) -> check_root_bubble tree (add_to_node s a k v) 
	     

    (* -- remove a value in the tree ------------------- *)


    (* fuse node cells together:
       ex: 
       [ 1 2 _ _ _ _ ] [x] [ 3 4 _ _ _ _ ]
       [ 1 2 x 3 4 _ ]
    *)
    let fuse_cells = 
      guard_ia "fuse_cells" (fun cl cr i ->
	let offset = size_cells cl 
	and len = size_cells cr in
	set_cell cl offset i;
	blit cr 0 cl (offset+1) len
      ) 
	
    let fuse_nodes =
      guard_ia "fuse_nodes" (fun il ir ->
	let offset = size_nodes il
	and len = size_nodes ir in
	blit ir 0 il (offset) len
      )

    (* left rotation of i entries
       [ a 1 b 2 c _   _   _ _ ] [x] [ d 3 e 4 f 5 g 6 h 7 i _ ] 2
       [ a 1 b 2 c x d 3 e _ _ ] [4] [ f 5 g 6 h 7 i _   _   _ ]
    *)
    let rotate_cells_left =
      guard_ia "rotate_cells_left" (fun cl cr cells i count ->
	let lsz  = size_cells cl 
	and rsz  = size_cells cr
	in
	(* move cells 1st *)
	set_cell cl lsz (get_cell cells i);        (* copy old median                    *)
	blit cr 0 cl (lsz+1) (count-1);            (* copy cright beginning to cleft end *)
	set_cell cells i (get_cell cr (count-1));  (* set new median                     *)
	shift_l count cr;                          (* shift cr to the left               *)
	clear_cells cr (a_max-rsz+count)           (* clear cr end                       *)
      ) 

    let rotate_nodes_left =
      guard_ia "rotate_cells_left" (fun sl sr count ->
	let lsz  = size_nodes sl 
	and rsz  = size_nodes sr
	in
	(* move intervals *)
	blit sr 0 sl (lsz) count;              (* copy sright beginning to sleft end *)
	shift_l count sr;                      (* shift sright array                 *)
	clear_nodes sr (a_max+1+count-rsz)     (* clear sr end                       *)
      ) 

    (* right rotation of i entries
       [ a 1 b 2 c 3 d 4 e _ _ ] [x] [ f 5 g 6 h 7 i _   _   _ ] 2
       [ a 1 b 2 c _   _   _ _ ] [3] [ d 4 e x f 5 g 6 h 7 i _ ] 
    *)
    let rotate_cells_right =
      guard_ia "rotate_cells_right" (fun cl cr cells i count ->
	let lsz = size_cells cl 
	in
	(* move cells 1st *)
	shift_r count cr;                          (* shift cr                           *)
	set_cell cr (count-1) (get_cell cells i);  (* copy old median                    *)
	blit cl (lsz-count+1) cr 0 (count-1);      (* copy cl end to cr beginning        *)
	set_cell cells i (get_cell cl (lsz-count));(* set new median                     *)
	fill cl (lsz-count) (count) EmptyCell      (* clear cl end                       *)
      )
	
    let rotate_nodes_right =
      guard_ia "rotate_nodes_right" (fun sl sr count ->
	let lsz = size_nodes sl 
	in
	(* move intervals *)
	shift_r count sr;                      (* shift sr                           *)
	blit sl (lsz-count) sr 0 count;        (* copy sl end to sr beginning        *)
	fill sl (lsz-count) (count) EmptyNode  (* clear sl end                       *)
      )

    (* remove a (key,value) pair from the tree *)
    let remove tree k = 
      let check_underflow subs cells i =
	try (
	  let rec check_u_r subs cells i =
	    match get_sub subs i, get_sub subs (i+1) with
		Node(il, cl), Node(ir, cr) -> (
		  let l = size_cells cl 
		  and r = size_cells cr
		  in 
		  debug ("sizes : "^(string_of_int l)^" + "^(string_of_int r));
		  if (l < a_min) || (r < a_min) then
		    if (l+r) < a_max
		    then ( (* fuse nodes *)
		      debug "fusing";
		      fuse_cells cl cr (get_cell cells i);
		      fuse_nodes il ir;
		      shift_left subs (i+1);
		      shift_left cells i;
		    )
		    else 
		      if l < r 
		      then (debug "rotate_left";rotate_cells_left cl cr cells i (a_min - l); rotate_nodes_left il ir (a_min - l))
		      else (debug "rotate_right";rotate_cells_right cl cr cells i (a_min - r);rotate_nodes_right il ir (a_min - r))
		  else
		    check_u_r subs cells (i+1)
		)
	      | Leaf (cl), Leaf(cr)        -> (
		let l = size_cells cl 
		and r = size_cells cr
		in 
		debug ("sizes : "^(string_of_int l)^" + "^(string_of_int r));
		if (l < a_min) || (r < a_min) then
		  if (l+r) < a_max 
		  then ( (* fuse nodes *)
		    debug "fusing";
		    fuse_cells cl cr (get_cell cells i);
		    shift_left subs (i+1);
		    shift_left cells i (*;
					 check_u_r subs cells i (* we fused 2 cells, let's check if we need to do more *) *)
		  )
		  else 
		    if l < r 
		    then (debug "rotate_left";rotate_cells_left cl cr cells i (a_min - l))
		    else (debug "rotate_right";rotate_cells_right cl cr cells i (a_min - r))
		else
		  check_u_r subs cells (i+1)
	      )
	      | _                         -> ()     (* we've reached the end of the node array *)
	  in
	  if i = 0 then check_u_r subs cells 0
	  else check_u_r subs cells (i-1)
	) with Invalid_argument x -> raise (Invalid_argument ("check_underflow:"^x))	    	    
	  
      in

      let rec remove_r node k =
	match node with
	    EmptyNode  -> raise Not_found
	  | Leaf (a)   -> remove_of_leaf a k 0
	  | Node (s,a) -> remove_of_node a s k 0
	    
      and remove_of_leaf cells k i =
	match get_cell cells i with
	    EmptyCell       -> raise Not_found
	  | Cell(ck,cv)     -> 
	    match compare k ck with 
		Below -> raise Not_found
	      | Equal -> (shift_left cells i;is_underflow cells)
	      | Above -> remove_of_leaf cells k (i+1)                         (* loop to next cell *)
		
      and remove_of_node cells subs k i =
	if (
	  match get_cell cells i with
	      EmptyCell      -> remove_r (get_sub subs i) k
	    | Cell(ck,cv)    -> 
	      match compare k ck with 
		  Above -> remove_of_node cells subs k (i+1)                  (* loop to next cell *)
 		| Equal -> (swap_and_remove cells i (get_sub subs (i+1)));              
		(* we are removing a cell from a node
		   => swap with the next leaf cell and proceed from there *)
		| Below -> remove_r (get_sub subs i) k 
	)
	then 
	  (check_underflow subs cells i; is_underflow cells)
	else false

      and swap_and_remove source i node =
	match node with
	    EmptyNode        -> invalid_arg "Btree.remove: no next value for in node removal"
	  | Leaf (cells)     -> (
	    debug ("swap_of_leaf: replacing with "^(get_key (get_cell cells 0)));
	    set_cell source i (get_cell cells 0); (* swap the cells *)
	    shift_left cells 0;                   (* remove the target cell *)
	    is_underflow cells
	  )
 	  | Node (subs,cells) -> 
	    if swap_and_remove source i (get_sub subs 0) 
	    then (check_underflow subs cells 0;is_underflow cells) 
	    else false


      in debug ("remove "^(O.string_of_key k));
      ignore (remove_r tree.root k);
      match tree.root with
	  EmptyNode  -> ()
	| Node (s,a) -> if size_cells a = 0 then tree.root <- (get_sub s 0) 
	(* since all cells have been suppressed, the remaining is in the 1st subnode *)
	| Leaf (a)   -> ()

  end (* Make *)

end

(*
module Pure =
struct

  module type S =
  sig

    type key_t
    type value_t

    type t
      
    val create    : unit -> t

    val fold_left : ('a -> key_t -> value_t -> 'a) -> 'a -> t -> 'a
    val iter      : t -> (key_t -> value_t -> unit) -> unit
    val find      : t -> key_t -> value_t
    val add       : t -> key_t -> value_t -> t
    val remove    : t -> key_t -> t

    val dump      : t -> string -> string -> unit

  end

  module Make (O: BtreeConf) : S with type key_t = O.key_t and type value_t = O.value_t =
  struct

    include Common(O)


    (* - array manipulation ----------------------- *)

    (* shift right of count elements the array a in b *)
    let shift_r count a b = 
      try (
	blit a 0 b (count) ((Array.length a) - count)
      ) with Invalid_argument x -> raise (Invalid_argument ("shift_r:"^x))
	
    (* shift left of count elements the array a in b *)
    let shift_l count a b = 
      try (
	blit a (count) b 0 ((Array.length a) - count)
      ) with Invalid_argument x -> raise (Invalid_argument ("shift_l:"^x))


    (* 3 [ 1 2 3 4 5 6 7 ] -> [ 1 2 3 4 _ _ _ ]  *)
    (* fill the last n entries in array a with value *)
    let fill_end value a n =
      let l = Array.length a in
      fill a (l-n) n value
	
    let clear_cells = fill_end EmptyCell
      
    let clear_nodes = fill_end EmptyNode
      
    (* shift 1 step on the right elements of a starting at position i (element i is duplicated) *)
    let shift_right a i b c = 
      try (
	blit a 0 b 0 i;
	blit a i b (i+1) ((Array.length a) - i - 1);
	b.(i) <- c
      ) with Invalid_argument x -> raise (Invalid_argument ("shift_right:"^x))

    (* shift 1 step on the left elements of a starting at position i+1 (we loose element i) *)
    (* [ 1 2 3 4 5 6 ] -> [ 1 3 4 5 6 _ ]  *)
    let shift_left  a i b = 
      try (
	blit a 0 b 0 (pred i);
	blit a (i+1) b i ((Array.length a) - i - 1)
      ) with Invalid_argument x -> raise (Invalid_argument ("shift_left:"^x))


    type t = {mutable root: node_t}

    let create () = {root = create_empty_leaf ()}

    (* - iterators etc.... -- *)

    let fold_left f acc tree =
      let rec fold_node f acc node =
	let racc = ref acc in
	match node with
	    EmptyNode  -> acc
	  | Node (s,a) -> for i=0 to a_max do racc := fold_cell f (fold_node f (!racc) s.(i)) a.(i) done; fold_node f (!racc) s.(a_max+1)
	  | Leaf (a)   -> for i=0 to a_max do racc := fold_cell f !racc a.(i) done; !racc

      and fold_cell f acc cell =
	match cell with
	    EmptyCell      -> acc
	  | Cell(k, v)     -> (f acc k v)

      in fold_node f acc tree.root 

    let size t =
      let f acc k v = succ acc
      in
      fold_left f 0 t

    let iter tree f =
      let f' () = f 
      in fold_left f' () tree

      
    (* dump a tree structure in a dotty file *)
    let dump tree filename directory =
      let file = open_out (directory^"/"^filename^".dot") in
      
      let dump_link parent child =
	output_string file (parent^" -> "^child^":n;\n")
	  
      and range cells = 
	let sz = size_cells cells in
	if sz = 0 then 0,"n_empty_"
	else
	  match cells.(0), cells.(sz-1) with
	      Cell(k0,v0), Cell(k1,v1) ->
		sz, ("n_"^(O.string_of_key k0)^"_"^(O.string_of_key k1)^"_")
	    | _                              -> invalid_arg "Btree.range"
	      
      and record_struct node cells = 
	let rec build_lbl s i = 
	  if i = O.max then (s^"\" ];")
	  else 
	    match cells.(i) with
		Cell(k,_) -> build_lbl (s^" | <l"^(string_of_int (i+1))^"> "^(O.string_of_key k)^" | <i"^(string_of_int (i+1))^"> ") (i+1)
	      | EmptyCell   -> (s^"\" ];\n")
	in build_lbl (node^" [ label = \"<i0> ") 0

      in
      let rec dump_r parent node =
	match node with
	    EmptyNode  -> debug "dump_r: empty node";()
 	  | Node (s,a) -> dump_node parent s a
	  | Leaf (a)   -> dump_leaf parent a
	    
      and dump_node parent s cells =
	let sz, id = range cells in
	dump_link parent id;
	output_string file (record_struct id cells);
	for i = 0 to (sz) do
	  dump_r (id^":i"^(string_of_int i)) s.(i)
	done

      and dump_leaf parent cells =
	let sz, id = range cells in
	dump_link parent id;
	output_string file (record_struct id cells)

      in 
      output_string file ("digraph "^filename^" {\n");
      output_string file ("name ="^filename^";\n");
      output_string file "node [shape=record];\n";
      (match tree.root with
	  Leaf (a)   -> if size_cells a > 0 then dump_leaf "root" a else ()
	| _          -> dump_r "root" tree.root);
      output_string file "}";
      close_out file


    (* -- find a value in tree -------------------- *)
	
    (* a 0 b 1 c 2 d 3 e 4 f 5 g 6 h 7 i *)

    let find =
      let find_dicho tree k =
	let dicho i = if i = 1 then 0 else (i lsr 1) + (i mod 2) in
	let rec find_node node k =
	  match node with
	      EmptyNode   -> raise Not_found
	    | Leaf (a)    -> find_leaf_r a k (a_med) (a_med)
	    | Node (s,a)  -> find_node_r a s k (a_med) (a_med)
	      
	and find_leaf_r cells k i j = 
	  debug ("find_leaf: checking "^(string_of_int i)^" "^(string_of_int j));
	  let j' = dicho j in
	  match cells.(i) with 
	      EmptyCell    -> if j=0 then raise Not_found else find_leaf_r cells k (i-j') (j')
	    | Cell(ck,v)   ->
	      debug ("key = "^(O.string_of_key ck));
	      match compare k ck with
		  Below -> if j=0 then raise Not_found else find_leaf_r cells k (i-j') (j')
		| Equal -> v
		| Above -> if j=0 then raise Not_found else find_leaf_r cells k (i+j') (j')
		    
	and find_node_r cells s k i j =
	  debug ("find_node: checking "^(string_of_int i)^" "^(string_of_int j));
	  let j' = dicho j in
	  match cells.(i) with 
	      EmptyCell       -> if j=0 then find_node s.(i) k else find_node_r cells s k (i-j') (j')
	    | Cell(ck, v)     -> 
	      debug ("key = "^(O.string_of_key ck));
	      match compare k ck with
		  Below -> if j=0 then find_node s.(i) k else find_node_r cells s k (i-j') (j')
		| Equal -> v
		| Above -> if j=0 then find_node s.(i+1) k else find_node_r cells s k (i+j') (j')
		    
	in 
	debug ("searching: "^(O.string_of_key k));
	find_node tree.root k

      and find_linear tree k =
	let rec find_node node k =
	  match node with 
	      EmptyNode   -> raise Not_found
	    | Leaf (a)    -> find_leaf_r a k 0
	    | Node (s,a)  -> find_node_r a s k 0
	      
	and find_leaf_r cells k i = 
	  match cells.(i) with 
	      EmptyCell    -> raise Not_found
	    | Cell(ck,v)   ->
	      match compare k ck with
		  Below -> raise Not_found
		| Equal -> v
		| Above -> find_leaf_r cells k (i+1)
		  
	and find_node_r cells s k i =
	  if i = a_max 
	  then 
	    find_node s.(i) k 
	  else 
	    match cells.(i) with 
		EmptyCell       -> find_node s.(i) k
	      | Cell(ck, v)     -> match compare k ck with
		  Below -> find_node s.(i) k
		  | Equal -> v
		  | Above -> find_node_r cells s k (i+1)
		    
	in 
	find_node tree.root k

      in if a_med > dicho_threshold 
	then find_dicho 
	else find_linear


    (* -- add a value in tree -------------------- *)

    let add tree k v =

      let copy_second_half a cf mf =
	let na = create_cell_array () 
	and median = a.(a_min)
	in 
	blit a (a_min+1) na 0 a_min;             (* copy the second half of the cells      *)
	fill a (a_min) (a_min+1) EmptyCell;      (* erase them from the full leaf          *)
	Some(median,Leaf(na))
	  

    (* [ 1 2 3 4 5 ] -> [ 1 2 ] [3] [ 4 5 ] *)
    let split_leaf =
      let split_leaf_even a =
	let na = create_cell_array () 
	and median = a.(a_min)
	in 
	blit a (a_min+1) na 0 a_min;             (* copy the second half of the cells      *)
	fill a (a_min) (a_min+1) EmptyCell;      (* erase them from the full leaf          *)
	Some(median,Leaf(na))
      and split_leaf_odd a =
	let na = create_cell_array ()
	and median = a.(a_med)
	in 
	blit a (a_med+1) na 0 a_min;             (* copy the second half of the cells      *)
	fill a (a_med) (a_min+1) EmptyCell;      (* erase them from the full leaf          *)
	Some(median,Leaf(na))
      in
      if (a_max mod 2) = 0
      then split_leaf_even
      else split_leaf_odd

	
    (* [ a 1 b 2 c 3 d 4 e 5 f ] -> [a 1 b 2 c ] [3] [ d 4 e 5 f ] *)
    and split_node =
      let split_node_even s a = 
	let na = create_cell_array ()
	and ns = create_interval_array ()
	and median = a.(a_min)                  (* the median value of the full node      *)
	in 
	blit a (a_min+1) na 0 a_min;            (* copy the second half of the cells      *)
	fill a (a_min) (a_min+1) EmptyCell;     (* erase them from the full node          *)
	blit s (a_min+1) ns 0 (a_min+1);        (* copy the second half of the nodes      *)
	fill s (a_min+1) (a_min+1) EmptyNode;   (* erase them from the full node          *)
	Some(median,Node(ns,na))                (* return the copy as a median + new node *)
      and split_node_odd s a =
	let na = create_cell_array ()
	and ns = create_interval_array ()
	and median = a.(a_med)                  (* the median value of the full node      *)
	in 
	blit a (a_med+1) na 0 a_min;            (* copy the second half of the cells      *)
	fill a (a_med) (a_med) EmptyCell;       (* erase them from the full node          *)
	blit s (a_med+1) ns 0 (a_med);          (* copy the second half of the nodes      *)
	fill s (a_med+1) (a_med) EmptyNode;     (* erase them from the full node          *)
	Some(median,Node(ns,na))                (* return the copy as a median + new node *)
	  
      in if (a_max mod 2) = 0 
	then split_node_even
	else split_node_odd
	  
    in
    let rec add_r node k v =
      match node with
	  EmptyNode -> Some(Cell(k,v), EmptyNode)
	| Leaf(a)   -> add_to_leaf a k v
	| Node(s,a) -> add_to_node s a k v
	  
    and add_to_leaf a k v =
      let check_overflow a =
	if is_full a then split_leaf a else None
      in
      let rec add_leaf_r a k v i =
	match a.(i) with 
	    EmptyCell   -> a.(i) <- Cell(k,v); check_overflow a
	  | Cell(ck,cv) -> 
	    match compare k ck with
		Above -> add_leaf_r a k v (i+1)
	      | Below -> shift_right a i; a.(i) <- Cell(k,v); check_overflow a
	      | Equal -> a.(i) <- Cell(k,v); None
      in add_leaf_r a k v 0
      
    and add_to_node s a k v = 
      let rec add_node_r s a k v i =
	let check_bubble b =
	  match b with
	      None        -> None
	    | Some((m,n)) -> 
	      shift_right a i; 
	      a.(i) <- m; shift_right s (i+1); s.(i+1) <- n; 
	      if is_full a then split_node s a else None
	in
	match a.(i) with 
	    EmptyCell   -> check_bubble (add_r s.(i) k v)
	  | Cell(ck,cv) -> 
	    match compare k ck with
		Above -> add_node_r s a k v (i+1)
	      | Below -> check_bubble (add_r s.(i) k v)
	      | Equal -> (a.(i) <- Cell(k,v)); None
		
      in add_node_r s a k v 0
      
    in let check_root_bubble tree b =
	 match b with
	     None       -> ()
	   | Some (m,n) -> 
	     let c = create_cell_array () 
	     and i = create_interval_array () 
	     in ignore ( 
	       i.(0) <- tree.root; 
	       i.(1) <- n; 
	       c.(0) <- m; 
	       tree.root <- Node(i,c)
	     )
       in match tree.root with
	   EmptyNode  -> 
	     let c = create_cell_array () 
	     in c.(0) <- Cell(k,v)
	 | Leaf (a)   -> check_root_bubble tree (add_to_leaf a k v)
	 | Node (s,a) -> check_root_bubble tree (add_to_node s a k v) 


    (* -- remove a value in the tree ------------------- *)

    (* remove a key,value from the tree *)
    let remove tree k = 
      let check_underflow subs cells i =
	try (
	  let rec check_u_r subs cells i =
	    match subs.(i), subs.(i+1) with
		Node(il, cl), Node(ir, cr) -> (
		  let l = size_cells cl 
		  and r = size_cells cr
		  in 
		  debug ("sizes : "^(string_of_int l)^" + "^(string_of_int r));
		  if (l < a_min) || (r < a_min) then
		    if (l+r) < a_max
		    then ( (* fuse nodes *)
		      debug "fusing";
		      fuse_cells cl cr cells.(i);
		      fuse_nodes il ir;
		      shift_left subs (i+1);
		      shift_left cells i;
		    )
		    else 
		      if l < r 
		      then (
			debug "rotate_left";
			rotate_cells_left cl cr cells i (a_min - l); 
			rotate_nodes_left il ir (a_min - l)
		      )
		      else (
			debug "rotate_right";
			rotate_cells_right cl cr cells i (a_min - r);
			rotate_nodes_right il ir (a_min - r)
		      )
		  else
		    check_u_r subs cells (i+1)
		)
	      | Leaf (cl), Leaf(cr)        -> (
		let l = size_cells cl 
		and r = size_cells cr
		in 
		debug ("sizes : "^(string_of_int l)^" + "^(string_of_int r));
		if (l < a_min) || (r < a_min) then
		  if (l+r) < a_max 
		  then ( (* fuse nodes *)
		    debug "fusing";
		    fuse_cells cl cr cells.(i);
		    shift_left subs (i+1);
		    shift_left cells i (*;
					 check_u_r subs cells i (* we fused 2 cells, let's check if we need to do more *) *)
		  )
		  else 
		    if l < r 
		    then (debug "rotate_left";rotate_cells_left cl cr cells i (a_min - l))
		    else (debug "rotate_right";rotate_cells_right cl cr cells i (a_min - r))
		else
		  check_u_r subs cells (i+1)
	      )
	      | _                         -> ()     (* we've reached the end of the node array *)
	  in
	  if i = 0 then check_u_r subs cells 0
	  else check_u_r subs cells (i-1)
	) with Invalid_argument x -> raise (Invalid_argument ("check_underflow:"^x))	    	    
	  
      in

      let rec remove_r node k =
	match node with
	    EmptyNode  -> raise Not_found
	  | Leaf (a)   -> remove_of_leaf a k 0
	  | Node (s,a) -> remove_of_node a s k 0
	    
      and remove_of_leaf cells k i =
	match cells.(i) with
	    EmptyCell       -> raise Not_found
	  | Cell(ck,cv)     -> 
	    match compare k ck with 
		Below -> raise Not_found
	      | Equal -> (shift_left cells (i);is_underflow cells)
	      | Above -> remove_of_leaf cells k (i+1)                         (* loop to next cell *)
		
      and remove_of_node cells subs k i =
	if (
	  match cells.(i) with
	      EmptyCell      -> remove_r subs.(i) k
	    | Cell(ck,cv)    -> 
	      match compare k ck with 
		  Above -> remove_of_node cells subs k (i+1)                  (* loop to next cell *)
 		| Equal -> (swap_and_remove cells i subs.(i+1));              
		(* we are removing a cell from a node
		   => swap with the next leaf cell and proceed from there *)
		| Below -> remove_r subs.(i) k 
	)
	then 
	  (check_underflow subs cells i; is_underflow cells)
	else false

      and swap_and_remove source i node =
	match node with
	    EmptyNode        -> invalid_arg "Btree.remove: no next value for in node removal"
	  | Leaf (cells)     -> (
	    debug ("swap_of_leaf: replacing with "^(get_key (cells.(0))));
	    source.(i) <- cells.(0);              (* swap the cells *)
	    shift_left cells 0;                   (* remove the target cell *)
	    is_underflow cells
	  )
 	  | Node (subs,cells) -> 
	    if swap_and_remove source i subs.(0) then (check_underflow subs cells 0;is_underflow cells) else false


      in debug ("remove "^(O.string_of_key k));
      ignore (remove_r tree.root k);
      match tree.root with
	  EmptyNode  -> ()
	| Node (s,a) -> if size_cells a = 0 then tree.root <- s.(0) 
	(* since all cells have been suppressed, the remaining is in the 1st subnode *)
	| Leaf (a)   -> ()

  end (* Make *)

end
*)

