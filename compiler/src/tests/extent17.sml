fun f_SR x_R = let
  fun b_R a_SR = x_R
  fun g_SR y_SR = b_R
in
  g_SR
end

val _ = (f_SR 1) 2
