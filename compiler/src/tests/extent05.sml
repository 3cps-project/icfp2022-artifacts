
val x =
    let fun f_SR (k : int) =
            let fun id_SR (x_SR : int -> int) = x_SR
                val b_SR : int = 2
                val a_R : int = 1
                fun u_SR (w1_SR : int) = a_R
                fun v_SR (w2_SR : int) = b_SR
                val w_SR : int -> int = id_SR v_SR
            in (id_SR u_SR) end
    in f_SR 3 end
       
