(* good32.sml
 *
 * Test of polymorphism in data structures
 *)

(* is not well formed, but the compiler raises Fail impossible on it *)
datatype t = A of 'a

