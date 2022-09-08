(* backtrace.sml
 *
 * COPYRIGHT (c) 2020 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * Wrapper to use the SML/NJ Backtrace mechanism.
 *)

structure BackTrace : sig

    val monitor : (unit -> 'a) -> 'a

  end = struct

    val _ = (
        SMLofNJ.Internals.TDP.mode := true;
        Coverage.install ();
        BackTrace.install ())

    val monitor = BackTrace.monitor

  end
