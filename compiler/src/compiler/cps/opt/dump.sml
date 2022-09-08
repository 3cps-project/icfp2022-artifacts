(* dump.sml
 * 
 * dump aggregate optimization results
 *)

structure DumpCPSOpt : sig

   val dump : unit -> unit

end = struct

   fun dump () = let
       fun say_num (msg, num) = DumpOptimizationSummary.say [msg, ": ", Int.toString num, "\n"]
       val {elim_count=elim_count} = CPSContraction.stats ()
       val _ = say_num ("Contraction eliminations", elim_count)
       val {elim_arg_count=elim_arg_count} = CPSSimpleArgumentElimination.stats ()
       val _ = say_num ("Argument eliminations", elim_arg_count)

       val {intro_arg_count=intro_arg_count} = CPSSimpleArityRaising.stats ()
       val _ = say_num ("Arity raising introductions", intro_arg_count)

       val {elim_select_count=elim_select_count,
            elim_switch_count=elim_switch_count} = CPSRedundantSelection.stats ()
       val _ = say_num ("Redun. sel. select eliminations", elim_select_count)
       val _ = say_num ("Redun. sel. switch eliminations", elim_switch_count)

       val {elim_move_count=elim_move_count} = CPSPropagateMoves.stats ()
       val _ = say_num ("Moves eliminated", elim_move_count)

   in () end

end

