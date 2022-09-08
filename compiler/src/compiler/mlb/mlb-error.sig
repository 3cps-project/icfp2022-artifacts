(* mlb-error.sig
 *
 * COPYRIGHT (c) 2021 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * An interface to error reporting that is used to specialize the MLB Kit
 * modules that may encounter errors in the MLB syntax or specification.
 *
 * A trivial implementation of this signature is to define the context as
 * the `unit` type and to raise an exception for errors.
 *)

signature MLB_ERROR =
  sig

  (* context information for error reporting *)
    type context

  (* `error (cxt, lnum, msg)` reports an error at the given line number (we assume that the
   * context includes the source file name); the message should not have a terminating newline
   *)
    val errorAt : context * int * string -> unit

  (* `error (cxt, msg)` reports an error; the message should not have a terminating newline *)
    val error : context * string -> unit

  end
