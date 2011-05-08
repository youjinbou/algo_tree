open OUnit
open Random
open Setup

(* unit tests for the sorted tree implementations 
   for each kind of tree we do the following:


   - the tree is instancied as a (int, int) map
   - A range of ints from 'min' to 'max' are then
   mapped to themselves in the tree, in a random
   order. 
   - The same range is then seeked in a different random
   order.
   - The same range is then remove from the tree, again
   with a different order.


   Each implementation requires its own set of tests

   'dump_data' indicates if we dump a graphviz 
   dot compatible representation of the tree
   at certain steps of the tests.
   
*)




(* TEST SUITE -------------------------------------- *)


let tree_test_list =
  TestLabel ("[test int list]", TestList [
	       TestLabel ("Btree (imperative)", TestCase(fun _ -> Btree_test.test ()));
	       TestLabel ("Rbtree (functional)", TestCase(fun _ -> Rbtree_test.fun_test ()));
	       TestLabel ("Rbtree (imperative)", TestCase(fun _ -> Rbtree_test.imp_test ()));
	       TestLabel ("Fibonacci (functional)", TestCase(fun _ -> Fib_test.test ()))
	     ]
	    )

let test_suite = TestLabel("[ Test Suite ]",
			   TestList 
			     [
			       tree_test_list
			     ]
			  );;


let _ =
  run_test_tt test_suite

