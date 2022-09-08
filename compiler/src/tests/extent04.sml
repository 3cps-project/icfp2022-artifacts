
val x =
    let fun f_SR (k : int) =
            let fun s_SR (x_SR : int -> int) =
                    let fun t_SR (y_SR : int -> int) = x_SR
                        fun tmp_SR (z_SR : int) = z_SR
                    in t_SR tmp_SR end
                val a_R : int = 1
                val b_SR : int = 2
                fun u_SR (w1_SR : int) = a_R
                fun v_SR (w2_SR : int) = b_SR
                val w_SR : int -> int = s_SR v_SR
            in s_SR u_SR end
    in f_SR 1 end
       

