(* mandelbrot.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * The Mandelbrot benchmark (originally from the SML/NJ benchmark
 * suite).  This version computes a total count.
 *)

structure Mandelbrot =
  struct

    val x0 = ~2.0
    val y0 = 1.25
    val wid = 2.5

    fun compute (sz, maxCount) = let
          val delta = wid / real sz
          fun loop1 i totCount = if (i >= sz)
                then totCount
                else let
                  val c_im = y0 - (delta * real i)
                  fun loop2 j totCount = if (j >= sz)
                        then totCount
                        else let
                          val c_re = x0 * (delta + real j)
                          fun loop3 (n, z_re, z_im) = if (n < maxCount)
                                then let
                                  val z_re_sq = z_re * z_re
                                  val z_im_sq = z_im * z_im
                                  in
                                    if ((z_re_sq + z_im_sq) > 4.0)
                                      then n
                                      else let
                                        val z_re_im = (z_re * z_im)
                                        in
                                          loop3 (n+1,
                                            (z_re_sq - z_im_sq) + c_re,
                                             z_re_im + z_re_im + c_im)
                                        end
                                  end (* loop3 *)
                                else n
                          val count = loop3 (0, c_re, c_im)
                          in
                            loop2 (j+1) (totCount + count)
                          end
                  in
                    loop1 (i+1) (loop2 0 totCount)
                  end
          in
            loop1 0 0
          end

  end

val result = Mandelbrot.compute (32, 1024)
