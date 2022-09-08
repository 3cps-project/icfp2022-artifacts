type rgb = int * int * int;

type image = rgb list list;

(* Is there no support for :: patterns in this language? *)
fun map (f, xs) =
     case xs
       of nil => nil
        | x::xr => f x :: map (f, xr);

fun comp255 n = 255 - n;

fun neg (r, g, b) = (comp255 r, comp255 g, comp255 b);

fun negImg img =
    let fun mapneg cs =
             case cs
               of nil => nil
                | x::xr => neg x :: mapneg xr
    in
      map (mapneg, img)
    end;

val black = (0,0,0);

val white = (255,255,255);

val i0 = (black::white::nil)::(white::white::nil)::nil;

val _ = negImg i0
