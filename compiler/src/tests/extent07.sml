
val x = let val s = (fn (u, v) => case true of true => u 
                                             | false => v)
                        (fn (x : int) => x, fn (y : int) => y)
        in s end
