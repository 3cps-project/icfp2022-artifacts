(* test references *)

fun inc ri = (ri := !ri + 1);
fun dec ri = (ri := !ri - 1);

val x = let val ri = ref 0 in inc ri; dec ri; !ri end;
