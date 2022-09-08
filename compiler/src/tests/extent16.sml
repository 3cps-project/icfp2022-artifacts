fun f_SR x_R = let
  val b_SR = 1
  fun g_SR y_SR = x_R
in
  g_SR
end

val _ = (f_SR 1) 2
