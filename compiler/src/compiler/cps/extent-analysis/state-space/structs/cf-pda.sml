(* cf-pda.sml
 *
 * Push-down control flow.
 *)

structure CF_PDA :> ADDR
    where type var = CVar.t
    where type info = Env.t
  = struct

    type t = CVar.t * Env.t

    type var = CVar.t

    type info = Env.t

    fun alloc (k : CVar.t, env') = (k, env')

    fun toString (k, _) = let
          val i = Word.toIntX (CVar.hash k)
          val bg = 4
          val fg = i mod 7
          val fg = if fg >= bg then fg+1 else fg
          in
            ANSIText.fmt ({fg=SOME fg, bg=SOME bg, bf=true, ul=true}, (CVar.toString k) ^ "/" ^ (Int.toString i))
          end

    fun same ((k1, env1), (k2, env2)) = 
        CVar.same(k1, k2)
        andalso (case Env.compare(env1, env2)
                  of EQUAL => true
                   | _ => false
                (* end case *))

    fun compare ((k1, env1), (k2, env2)) = 
        (case CVar.compare(k1, k2)
          of EQUAL => Env.compare(env1, env2)
           | ord => ord
        (* end case *))
            
    (* for now, we just hash the continuation variable, since Env does not have a hash function *)
    fun hash (k, _) = CVar.hash k
                                   
    local
        structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)
    
    structure Tbl = HashTableFn (
        struct
        type hash_key = t
        val hashVal = hash
        val sameKey = same
        end)
                                
  end
