
(* At calls, there are two choices:
   if there is any continuation passed whose frame is not the current
   one (i.e. an argument to us) then we search through all of the
   values and cannot stack-allocate any bindings on this frame that
   are closed over in those values, since the continuation passed may
   be called which will turn into a long jump.

   However, this may pop more than desired. In particular, only some
   of the values passed down may come back up. So we create a "ghost"
   continuation, which is a pair of a throw and a continuation
   address, which indicates that the continuation value was threaded
   through this frame. This not only gives us a precise representation
   of the stack (we can tell where tail-called frames were) but it
   allows us to only search through the return values at the call to
   determine what to pop.

   In the below program, even though a is passed downwards with the
   exn handler, it is not passed back up when that handler is called.
*)

exception Break of int -> int

fun f xxx = let
    val x = 1
    val y = 2
    fun a i = x
    fun b j = y
    fun g (f1, f2) = let
        val z = f1 3
    in raise Break f2 end
    val c = g (a, b)
in c 4 end

val yyy = f 100 handle Break f => f 4
