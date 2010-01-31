
module Btree =
struct

  open Array

  let debug s = prerr_string s;prerr_newline ()


  module type BtreeConf = 
  sig
    type key_t
    type value_t
    val compare : key_t -> key_t -> int
    val max     : int 
    val string_of_key : key_t -> string
  end


  module Make(O: BtreeConf) =
  struct

    exception Compare_error
    exception Duplicate

    (* some constants *)
    let a_min = O.max / 2
    let a_max = O.max
    
    type cell_t = 
	EmptyCell 
      | Cell of (O.key_t * O.value_t)       

    and  node_t = 
	EmptyNode
      | Leaf of ((cell_t) array )                    (* array of cells *)
      | Node of ((node_t) array * (cell_t) array )   (* array of cells + intervals *)

    type t = {mutable root: node_t}

    let create_cell_array ()     = Array.make (a_max+1) EmptyCell 

    let create_interval_array () = Array.make (a_max+2) EmptyNode
		      
    let create_empty_leaf () = 
      let a = create_cell_array () in
	Leaf (a) 

    let create () = {root = create_empty_leaf ()}

    let size v limit a = 
      let i = ref 0 in
	while ((!i < limit) && (a.(!i) <> v)) do incr i done; !i

    let size_cells = size EmptyCell (a_max+1) 

    let size_nodes = size EmptyNode (a_max+2)

    let is_full a = a.(a_max)<>EmptyCell

    let is_underflow a = (a.(a_min-1)=EmptyCell)


    (* -- comparison values filter ---------------- *)

    type compare_t = Below | Above | Equal

    let compare k1 k2 =
      match O.compare k1 k2 with
	  -1 -> Below
	|  1 -> Above
	|  0 -> Equal
	|  _ -> raise (Compare_error)


    (* - array manipulation -- *)


    (* shift right of count elements the array a *)
    let shift_r count a = 
      blit a 0 a (count) ((Array.length a) - count)
    
    (* shift left of count elements the array a *)
    let shift_l count a  = 
      blit a (count) a 0 ((Array.length a) - count)


    (* 3 [ 1 2 3 4 5 6 7 ] -> [ 1 2 3 4 _ _ _ ]  *)
    (* fill the last n entries in array a with value *)
    let fill_end value a n =
      let l = Array.length a in
      fill a (l-n) n value

    let clear_cells = fill_end EmptyCell

    let clear_nodes = fill_end EmptyNode

    let shift_right a i = blit a i a (i+1) ((Array.length a) - i - 1)

    (* [ 1 2 3 4 5 6 ] -> [ 1 3 4 5 6 _ ]  *)
    let shift_left  a i = 
      blit a (i+1) a i ((Array.length a) - i - 1)

    (* - iterators etc.... -- *)


    let fold_left f acc tree =
      let rec fold_node f acc node =
	match node with
	    EmptyNode  -> ()
	  | Node (s,a) -> for i=0 to a_max do fold_node f acc s.(i); fold_cell f acc a.(i) done; fold_node f acc s.(a_max+1)
	  | Leaf (a)   -> for i=0 to a_max do fold_cell f acc a.(i) done

      and fold_cell f acc cell =
	match cell with
	    EmptyCell      -> ()
	  | Cell(k, v)     -> (f acc k v)

      in fold_node f acc tree.root 

    let iter tree f =
      let f' s = f 
      in fold_left f' () tree


    let dump tree filename directory =
      let file = open_out (directory^"/"^filename^".dot") in

      let dump_link parent child =
	output_string file (parent^" -> "^child^":n;\n")

      and range cells = 
	let sz = size_cells cells in
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

    let find tree k =
      
      let rec find_node node k =
	match node with 
	    EmptyNode   -> debug ("find_node '"^(O.string_of_key k)^"': hit an empty node");raise Not_found
	  | Leaf (a)    -> find_in_leaf a k
	  | Node (s,a)  -> find_in_node a s k

      and find_in_leaf a k =
	let debug k i m = debug ("find_in_leaf k:'"^(O.string_of_key k)^"' i:'"^(string_of_int i)^"' : "^m)
	in
	let rec find_leaf_r cells k i = 
 	  match cells.(i) with 
	      EmptyCell    -> debug k i "empty cell"; raise Not_found
	    | Cell(ck,v)   ->
		match compare k ck with
		    Below -> (debug k i (" k < cell.k '"^(O.string_of_key ck)^"'"); raise Not_found)
		  | Equal -> (prerr_string ("B.find_in_leaf: found "^(O.string_of_key ck));prerr_newline ();v)
		  | Above -> find_leaf_r cells k (i+1)
	in 
	  find_leaf_r a k 0
	     
      and find_in_node a s k =
	let rec find_node_r cells s k i =
	  if i = a_max 
	  then 
	    find_node s.(i) k 
	  else 
	    match cells.(i) with 
		EmptyCell       -> find_node s.(i) k
	      | Cell(ck, v)     -> match compare k ck with
		    Below -> find_node s.(i) k
		  | Equal -> (prerr_string ("B.find_in_node: found "^(O.string_of_key ck));prerr_newline ();v)
		  | Above -> find_node_r cells s k (i+1)
	in
	  find_node_r a s k 0
	     
      in 
	find_node tree.root k

    (* -- add a value in tree -------------------- *)

    let add tree k v =

      (* [ 1 2 3 4 5 ] -> [ 1 2 ] [3] [ 4 5 ] *)
      let split_leaf a =
	let na = create_cell_array () 
	and median = a.(a_min)
	in 
	  blit a (a_min+1) na 0 a_min;
	  fill a (a_min) (a_min+1) EmptyCell;
	  Some(median,Leaf(na))

	    
      (* [ a 1 b 2 c 3 d 4 e 5 f ] -> [a 1 b 2 c ] [3] [ d 4 e 5 f ] *)
      and split_node s a = 
	let na = create_cell_array ()
	and ns = create_interval_array ()
	and median = a.(a_min)                    (* the median value of the full node      *)
	in 
	  blit a (a_min+1) na 0 a_min;            (* copy the second half of the cells      *)
	  fill a (a_min) (a_min+1) EmptyCell;     (* erase them from the full node          *)
	  blit s (a_min+1) ns 0 (a_min+1);        (* copy the second half of the nodes      *)
	  fill s (a_min+1) (a_min+1) EmptyNode;   (* erase them from the full node          *)
	  Some(median,Node(ns,na))                (* return the copy as a median + new node *)
	
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
	    | Cell(ck,cv) -> match compare k ck with
		  Above -> add_leaf_r a k v (i+1)
		| Below -> shift_right a i; a.(i) <- Cell(k,v); check_overflow a
		| Equal -> a.(i) <- Cell(k,v); None
	in add_leaf_r a k v 0
	     
      and add_to_node s a k v = 
	let rec add_node_r s a k v i =
	  let check_bubble b =
	    match b with
		None        -> None
	      | Some((m,n)) -> shift_right a i; a.(i) <- m; shift_right s (i+1); s.(i+1) <- n; if is_full a then split_node s a else None
	  in
	    match a.(i) with 
		EmptyCell   -> check_bubble (add_r s.(i) k v)
	      | Cell(ck,cv) -> match compare k ck with
		    Above -> add_node_r s a k v (i+1)
		  | Below -> check_bubble (add_r s.(i) k v)
		  | Equal -> (a.(i) <- Cell(k,v)); None

	in add_node_r s a k v 0

      in let check_root_bubble tree b =
	  match b with
	      None       -> ()
	    | Some (m,n) -> let c = create_cell_array () 
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
      (* fuse nodes together:
	 ex: cells ->
	 [ 1 2 _ _ _ _ ] [x] [ 3 4 _ _ _ _ ]
	 [ 1 2 x 3 4 _ ]
      *)
      let fuse_cells cl cr i =
	let offset = size_cells cl 
	and len = size_cells cr in
	  cl.(offset) <- i;
	  blit cr 0 cl (offset+1) len

      and fuse_nodes il ir =
	let offset = size_nodes il
	and len = size_nodes ir in
	  blit ir 0 il (offset) len	  

      (* left rotation of i entries
	 [ a 1 b 2 c _   _   _ _ ] [x] [ d 3 e 4 f 5 g 6 h 7 i _ ] 2
	 [ a 1 b 2 c x d 3 e _ _ ] [4] [ f 5 g 6 h 7 i _   _   _ ]
      *)
      and rotate_cells_left cl cr cells i count =
	let lsz  = size_cells cl 
	and rsz  = size_cells cr
	in
	  (* move cells 1st *)
	  cl.(lsz)  <- cells.(i);                (* copy old median *)
	  blit cr 0 cl (lsz+1) (count-1);        (* copy cright beginning to cleft end *)
	  cells.(i) <- cr.(count-1);             (* set new median *)
	  shift_l count cr;                      (* shift cr to the left *)
	  clear_cells cr (a_max-rsz+count);      (* clear cr end *)


      and rotate_nodes_left sl sr count =
	let lsz  = size_nodes sl 
	and rsz  = size_nodes sr
	in
	  (* move intervals *)
	  blit sr 0 sl (lsz) count;            (* copy sright beginning to sleft end *)
	  shift_l count sr;                      (* shift sright array *)
	  clear_nodes sr (a_max+1+count-rsz)


      (* right rotation of i entries
	 [ a 1 b 2 c 3 d 4 e _ _ ] [x] [ f 5 g 6 h 7 i _   _   _ ] 2
	 [ a 1 b 2 c _   _   _ _ ] [3] [ d 4 e x f 5 g 6 h 7 i _ ] 
      *)
      and rotate_cells_right cl cr cells i count =
	let lsz = size_cells cl 
	and rsz = size_cells cr
	in
	  (* move cells 1st *)
	  shift_r count cr;                      (* shift cr        *)
	  cr.(count-1) <- cells.(i);             (* copy old median *)
	  blit cl (lsz-count+1) cr 0 (count-1);  (* copy cl end to cr beginning *)
	  cells.(i) <- cl.(lsz-count);           (* set new median  *)
	  fill cl (lsz-count) (count) EmptyCell  (* clear cl end    *)
	    
      and rotate_nodes_right sl sr count =
	let lsz = size_nodes sl 
	and rsz = size_nodes sr
	in
	  (* move intervals *)
	  shift_r count sr;                      (* shift sr        *)
	  blit sl (lsz-count) sr 0 count;        (* copy sl end to sr beginning *)
	  fill sl (lsz-count) (count) EmptyNode  (* clear sl end    *)
	    
      in

      let check_underflow subs cells i =
	let rec check_u_r subs cells i =
	match subs.(i), subs.(i+1) with
	    Node(il, cl), Node(ir, cr) -> 
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
		    then (debug "rotate_left";rotate_cells_left cl cr cells i (a_min - l); rotate_nodes_left il ir (a_min - l))
		    else (debug "rotate_right";rotate_cells_right cl cr cells i (a_min - r);rotate_nodes_right il ir (a_min - r))
		  else
		    check_u_r subs cells (i+1)
	    | Leaf (cl), Leaf(cr)      ->
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
	    | _                        -> ()     (* we've reached the end of the node array *)
	in
	  if i = 0 then check_u_r subs cells 0
	  else check_u_r subs cells (i-1)
		
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
		| Above -> remove_of_leaf cells k (i+1)                       (* loop to next cell *)
		    
      and remove_of_node cells subs k i =
	if
  	(match cells.(i) with
	    EmptyCell      -> remove_r subs.(i) k
	  | Cell(ck,cv)    -> 
	      match compare k ck with 
		  Above -> remove_of_node cells subs k (i+1)                  (* loop to next cell *)
 		| Equal -> (swap_and_remove cells i subs.(i+1));              (* we are removing a cell from a node
										 => swap with the next leaf cell and proceed from there *)
		| Below -> remove_r subs.(i) k )
	then 
	  (check_underflow subs cells i; is_underflow cells)
	else false

      and swap_and_remove source i node =
	match node with
	    EmptyNode  -> invalid_arg "Btree.remove: no next value for in node removal"
	  | Leaf (a)   -> swap_of_leaf source i a
 	  | Node (s,a) -> swap_of_node source i s a

      and swap_of_leaf source i cells =
	let r = source.(i) in 
	  source.(i) <- cells.(0);              (* swap the cells *)
	  shift_left cells 0;                   (* remove the target cell *)
	  is_underflow cells

      and swap_of_node source i subs cells =
	if swap_and_remove source i subs.(0) then (check_underflow subs cells i;is_underflow cells) else false	      

      in remove_r tree.root k; 
	match tree.root with
	    EmptyNode  -> ()
	  | Node (s,a) -> if size_cells a = 0 then tree.root <- s.(0) (* since all cells have been suppressed, the remaining is in the 1st subnode *)
	  | Leaf (a)   -> ()

  end (* Make *)

end
