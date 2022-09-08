(* good27.sml
 *
 * Test array operations
 *)

structure Array =
  struct
    (*
    FIXME
    fun array (n, init) = if (n < 0)
            then raise Size
          else if (n = 0)
            then array0()
            else array_alloc(n, init)
    *)
    fun array (n, init) = if (n <= 0)
            then raise Size
          else array_alloc(n, init)

    val length = array_length
    val sub = array_sub
    val update = array_update

    (* 
    FIXME
    fun fromList [] = array0()
      | fromList (v::r) = let
          fun len ([], n) = n
            | len (_::r, n) = len(r, n+1)
          val n = len(r, 1)
          val arr = array_alloc(n, v)
          fun init (_, []) = ()
            | init (i, x::xs) = (array_update(arr, i, x); init(i+1, xs))
          in
            init (1, r);
            arr
          end
    *)
    fun fromList [] = raise Size
      | fromList (v::r) = let
          fun len ([], n) = n
            | len (_::r, n) = len(r, n+1)
          val n = len(r, 1)
          val arr = array_alloc(n, v)
          fun init (_, []) = ()
            | init (i, x::xs) = (array_update(arr, i, x); init(i+1, xs))
          in
            init (1, r);
            arr
      end
  end

val result = (Array.array(2, 1) = Array.fromList [1, 1])
