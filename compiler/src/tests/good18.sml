fun evenLength xs =
     (case xs
       of nil => true
        | _::xr => oddLength xr
     (* end case *))

and oddLength xs =
     (case xs
       of nil => false
        | _::xr => evenLength xr
     (* end case *));

val _ = "mutual recursion"
