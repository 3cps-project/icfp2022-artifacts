
val x =
    let fun f_RS x_RS =
            let fun g_RS y_RS = (x_RS + y_RS)
                val a_RS = g_RS 5
                val b_RS = g_RS 7
            in a_RS + b_RS end
    in f_RS 6 end
