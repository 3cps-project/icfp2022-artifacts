
val x = let fun s_SR (a_H : int -> int) (b_SR : int -> int) = a_H
            fun x_SR (c_SR : int) = c_SR
            fun y_SR (d_SR : int) = d_SR
            fun z_SR (e_SR : int) = e_SR
            fun w_SR (f_SR : int) = f_SR
            val t_SR = s_SR (x_SR) 
            val u_SR = s_SR (z_SR) 
        in
            (t_SR y_SR 1) + (u_SR w_SR 2)
        end
