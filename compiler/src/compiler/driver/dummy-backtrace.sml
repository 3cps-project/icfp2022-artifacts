(* dummy-backtrace.sml
 *
 * COPYRIGHT (c) 2020 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * Dummy backtrace wrapper.
 *)

structure BackTrace : sig

    val monitor : (unit -> 'a) -> 'a

  end = struct

    fun monitor f = f()

  end
