(* good09.sml
 *
 * tests for the translation of polymorphic let-bound variables to CPS
 *)

fun queue_to_list q = q

val make_empty_queue = []

fun make_singleton_queue item = [item]
