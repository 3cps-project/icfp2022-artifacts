(* basic tests of word operations *)

val x = 0w42 + 0w17;
val y = word_toIntX x;
val z = word_andb(x, word_fromInt y);

