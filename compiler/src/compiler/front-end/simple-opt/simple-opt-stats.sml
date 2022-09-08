(* simple-opt-stats.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure SimpleOptStats =
  struct

    val group = Stats.Group.newWithPri Stats.Group.root ("simple-opt", [1, 1])

  end

