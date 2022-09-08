
val x = let val s = case true of true => (fn (x : int) => x) 
                              | false =>  (fn (y : int) => y)
        in s end
