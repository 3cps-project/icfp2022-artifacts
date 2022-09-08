
(* This example shows all possible sets of extents that variables can
   have - it is possible for variables to have stack extent without
   register extent and vice-versa. This makes the possible sets of
   extents:
   {H}, {H, S}, {H, R}, and {H, S, R}
   Every variable automatically has heap extent.

   We step through the function 'f' multiple times.
   In all iterations, we'll bind 'a', and we'll also reference 'a' inside
   of 'f's return result, 'g'.  Since there are two bindings of 'a', it
   doesn't have register extent, and since it is referenced from 'g',
   which lives beyond 'f's stack frame, it doesn't have stack extent. 
   We have to make sure to use 'a' in the else branch, after the recursive call.
   If we don't then 'a' is not live in the else branch, and so on re-entry
   to 'f' the new binding for 'a' would be unique (i.e. possible to overwrite).
   {H} - a
   The variable 'b' has all three extents - it never lives past the
   lifetime of 'f's stack frame, and there is only a single binding of
   it live at any time.
   {H, S, R} - 'b'
   The variable 'c' has both heap and register extent - only one
   binding of it lives at any time. At first this seems obvious, since
   it doesn't occur in the recursive branch of 'f'. However, since the
   closure returned by 'f' in this case actually captures it, we need to
   do a little more reasoning. In this case, we can see that the
   result of 'f' is always immediately consumed (applied) and so only
   one binding of 'c' can be live at once. 
   {H, R} - 'c'
   Finally, the variable 'd' is bound before the recursive call, and
   so there will exist multiple bindings of 'd', meaning it doesn't
   have register extent. However, since 'd' is not captured by any
   returned closures, it still has stack extent.
   {H, S} - 'd'
*)

fun f n = let
    val a = 1 (* {H} *)
in if (n = 0)
   then let
       val b = 2 (* {H, S, R} *)
       val c = b + 1 (* {H, R} *)
       fun g () = a + c
   in g end
   else let 
       val d = 1 (* {H, S} *)
       val result = f (n-1) ()
       val result2 = result + d + a
   in fn () => result2 end
end

val top = (f 10) ()
