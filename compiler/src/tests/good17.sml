datatype file
  = DIR of string * file list
  | FILE of string * int;

fun foldr (f, b, xs) =
     (case xs
       of nil => b
        | (x::xr) => f (x, foldr (f, b, xr))
     (* end case *));

fun map (f, xs) =
     (case xs
       of nil => nil
        | (x::xr) => (f x) :: (map (f, xr))
     (* end case *));

fun plus (a, b) = a + b;

fun sum xs = foldr (plus, 0, xs);

(* count files (including directories) *)
fun countFiles x =
     (case x
       of DIR (_, fs) => 1 + sum (map (countFiles, fs))
        | FILE _ => 1
     (* end case *));

fun countDirs x =
     (case x
       of DIR (_, fs) => 1 + sum (map (countDirs, fs))
        | FILE _ => 0
     (* end case *));

fun totalFileSize x =
     (case x
       of DIR (_, fs) => sum (map (totalFileSize, fs))
        | FILE (_, s) => s
     (* end case *));

val _ = "hi"
