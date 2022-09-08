
val x = let fun f_SR (x_R : int -> int) (y_SR : int -> int) = x_R
            fun tmp1_SR (z_SR : int) = z_SR
            fun tmp2_SR (w_SR : int) = w_SR 
            val g_SR = f_SR tmp1_SR
            val h_SR = g_SR tmp2_SR
        in
            (h_SR 1)
        end

