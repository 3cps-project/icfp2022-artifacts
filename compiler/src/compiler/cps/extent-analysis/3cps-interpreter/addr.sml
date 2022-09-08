
structure ThreeCPSAddr = struct

  datatype t = HeapAddr of int
             | StackAddr of int
             | RegAddr of LVar.t

  fun compare (a1, a2) =
      case (a1, a2) 
       of (HeapAddr index1, HeapAddr index2) => Int.compare (index1, index2)
        | (HeapAddr index1, _) => LESS
        | (_, HeapAddr index2) => GREATER
        | (StackAddr index1, StackAddr index2) => Int.compare (index1, index2)
        | (StackAddr index1, _) => LESS
        | (_, StackAddr index2) => GREATER
        | (RegAddr x1, RegAddr x2) => LVar.compare (x1, x2)

  fun same (a1, a2) = compare (a1, a2) = EQUAL

  fun toString a =
      case a
       of HeapAddr i => "(H " ^ (Int.toString i) ^ ")"
       | StackAddr i => "(S " ^ (Int.toString i) ^ ")"
       | RegAddr x => "(R " ^ (LVar.toString x) ^ ")"

end
