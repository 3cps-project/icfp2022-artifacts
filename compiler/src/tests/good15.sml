fun casey4And (b1, b2, b3, b4) =
    (case b1
      of true =>
         (case b2
           of true =>
              (case b3
                of true =>
                   (case b4
                     of true => true
                      | false => false)
                 | false => false)
            | false => false)
       | false => false);

fun confusingCase (x, y, z) =
case x
of 10 => 10
| 11 =>
case y
of 1 => 1
| 2 => 2
| 3 => case z
of 16 => 32
| 17 => 332
| 18 => 3332
| q => 100;

val _ = "hi"
