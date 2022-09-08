(* precedence tests *)

fun b1 (n1,n2,n3,n4) =
    n1 = n2 andalso n1 <= n3 andalso n3 < n4 orelse
    n1 + n2 < 0 andalso n2 - n3 - n4 <= 100 andalso n1 * n2 + n3 div n4 = n2 mod n3 orelse
    n1 + n2 * n3 mod n4 = n1 div n2 * n3 + n4;

fun glueSums (n1,n2,n3,n4) = n1 + n2 :: n2 + n3 :: n3 + n4 :: nil;

val _ = "precedence tests"
