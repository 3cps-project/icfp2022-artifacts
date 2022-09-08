(* test of cases, datatypes, :: associativity *)

datatype fruit = APP | PLM | PCH;

type bushel = fruit list;

val mineAllMine = APP :: PLM :: PCH :: PCH :: PCH :: PLM :: nil;

fun discardApples b =
     case b
      of nil => nil
       | hd::tl => (case hd
               of APP => discardApples tl
                | _ => hd :: discardApples tl);

val _ = discardApples mineAllMine
