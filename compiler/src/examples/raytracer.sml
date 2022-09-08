(* raytrace.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Ray tracer from Impala benchmarks; the original was written in Id and was ported to
 * SML by John Reppy.
 *)

structure List =
  struct
    fun foldl f b l = let
          fun f2 (xs, acc) = (case xs of [] => acc | a::r => f2 (r, f (a, acc)))
          in
            f2 (l, b)
          end
  end

structure Math =
  struct
    val pi = 3.14159265358979323846
    val sqrt = sqrt
    val tan = tan
    val pow = pow
  end

local
fun error s = raise Fail s
fun expt a b = Math.pow(a, b)
(*
 *
 * generally handy stuff
 *)
val EPSILON = 1.0e~6;
val INFINITY = 1.0e20;
fun not b = (case b of true => false | false => true);
fun map f = let
      fun mapf l = (case l of nil => nil | x::xs => f x :: mapf xs)
      in
        mapf
      end;
fun hd l = (case l
       of nil => error("expecting a head")
        | x::xs => x);
fun tl l = (case l
       of nil => error("expecting a tail")
        | x::xs => xs);
(*
 * convenient vector operations
 *)
type vec = (real * real * real)
fun vecadd ((x1,y1,z1) : vec) (x2,y2,z2) = (x1+x2, y1+y2, z1+z2);
fun vecsum (x : vec list) = List.foldl (fn (a, b) => vecadd a b) (0.0,0.0,0.0) x;
fun vecsub ((x1,y1,z1) : vec) (x2,y2,z2) = (x1-x2, y1-y2, z1-z2);
fun vecmult ((x1,y1,z1) : vec) (x2,y2,z2) = (x1*x2, y1*y2, z1*z2);
fun vecnorm ((x,y,z) : vec) = let
      val len = Math.sqrt (x*x + y*y + z*z)
      in ((x/len, y/len, z/len), len) end
fun vecscale ((x,y,z) : vec) a = (a*x, a*y, a*z);
fun vecdot ((x1,y1,z1) : vec) (x2,y2,z2) = x1*x2 + y1*y2 + z1*z2;
fun veccross ((x1,y1,z1) : vec) (x2,y2,z2) = (y1*z2-y2*z1, z1*x2-z2*x1, x1*y2-x2*y1);
(* Note the following code is broken for negative vectors, but it was in the original
 * version.
 *)
fun zerovector ((x,y,z) : vec) =
      (x < EPSILON andalso y < EPSILON andalso z < EPSILON);

(*
 * type declarations
 *)
datatype Light
  = Directional of (vec * vec)          (* direction, color *)
  | Point of (vec * vec)                (* position, color *)
(* the following are not used
defsubst lightpos (Point pos col) = pos;
defsubst lightdir (Directional dir col) = { d,_ = vecnorm dir in d };
*)
fun lightcolor l = (case l
       of (Directional(_, c)) => c
        | (Point(_, c)) => c
      (* end case *));
datatype Surfspec
  = Ambient of vec      (* all but specpow default to zero *)
  | Diffuse of vec
  | Specular of vec
  | Specpow of real     (* default 8. *)
  | Reflect of real
  | Transmit of real
  | Refract of real     (* default 1, like air == no refraction *)
  | Body of vec         (* body color, default 1.,1.,1. *)
  ;
fun ambientsurf surf = (case surf
       of nil => (0.0, 0.0, 0.0)
        | (Ambient v :: ss) => v
        | (_ :: ss) => ambientsurf ss
      (* end case *));
fun diffusesurf surf = (case surf
       of nil => (0.0, 0.0, 0.0)
        | (Diffuse v :: ss) => v
        | (_ :: ss) => diffusesurf ss
      (* end case *));
fun specularsurf surf = (case surf
       of nil => (0.0, 0.0, 0.0)
        | (Specular v :: ss) => v
        | (_ :: ss) => (specularsurf ss)
      (* end case *));
fun specpowsurf surf = (case surf
       of nil => 8.0
        | (Specpow r :: ss) => r
        | (_ :: ss) => specpowsurf ss
      (* end case *));
fun reflectsurf surf = (case surf
       of nil => 0.0
        | (Reflect r :: ss) => r
        | (_ :: ss) => reflectsurf ss
      (* end case *));
fun transmitsurf surf = (case surf
       of nil => 0.0
        | (Transmit r :: ss) => r
        | (_ :: ss) => transmitsurf ss
      (* end case *));
fun refractsurf surf = (case surf
       of nil => 1.0
        | (Refract r :: ss) => r
        | (_ :: ss) => refractsurf ss
      (* end case *));
fun bodysurf surf = (case surf
       of nil => (1.0,1.0,1.0)
        | (Body v :: ss) => v
        | (_ :: ss) => bodysurf ss
      (* end case *));

datatype Sphere = Sphere of vec * real * Surfspec list (* pos, radius, surface type *)
fun spheresurf (Sphere(pos, rad, surf)) = surf;

(*
% camera static:
%   lookfrom = 0 -10 0   <--- Camera.pos
%   lookat = 0 0 0
%   vup = 0 0 1
%   fov = 45
% yields
%   dir = norm(lookat - lookfrom) = 0 1 0
%   lookdist = length(lookat-lookfrom) = 10
*)
(*val lookfrom = (0.0, ~10.0, 0.0);*)
val lookfrom = (2.1, 1.3, 1.7);
val lookat = (0.0, 0.0, 0.0);
val vup = (0.0, 0.0, 1.0);
val fov = 45.0;

(*%%%%%%
%% standard balls
*)
val s2 = [(Ambient (0.035,0.0325,0.025)), (Diffuse(0.5,0.45,0.35)),
       (Specular(0.8,0.8,0.8)), (Specpow 3.0), (Reflect 0.5)];
val s3 = [(Ambient (0.1,0.0,0.0)),(Diffuse (0.3,0.0,0.0)),
           (Specular (0.8,0.4,0.4)),(Transmit 0.7)];
val sempty = [];
val testspheres = [
     Sphere((0.0,0.0,0.0), 0.5, s3),
     Sphere((0.272166,0.272166,0.544331), 0.166667, s2),
     Sphere((0.643951,0.172546,0.0), 0.166667, s2),
     Sphere((0.172546,0.643951,0.0), 0.166667, s2),
     Sphere(((~0.371785),0.0996195,0.544331), 0.166667, s2),
     Sphere(((~0.471405),0.471405,0.0), 0.166667, s2),
     Sphere(((~0.643951),(~0.172546),0.0), 0.166667, s2),
     Sphere((0.0996195,(~0.371785),0.544331), 0.166667, s2),
     Sphere(((~0.172546),(~0.643951),0.0), 0.166667, s2),
     Sphere((0.471405,(~0.471405),0.0), 0.166667, s2)]
val testlights = [Point((4.0,3.0,2.0), (0.288675,0.288675,0.288675)),
              Point((1.0, ~4.0,4.0), (0.288675,0.288675,0.288675)),
              Point((~3.0,1.0,5.0), (0.288675,0.288675,0.288675))
                   (* added by BQ for expression coverage *)
              , Directional ((~11.0, 1.0, 0.5), (11.0, ~1.0, 0.5))];
val background = (0.078, 0.361, 0.753);
val world = testspheres;
(*%%%%%%%*)


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% sphere specific items
%
% figure when a ray hits a sphere
%
%%% Assumes direction vector is normalized!
*)
fun sphereintersect pos dir sp = let
    val Sphere(center, rad, _) = sp
    val m = vecsub pos center;  (* x - center *)
    val m2 = vecdot m m;    (* (x-center).(x-center) *)
    val bm = vecdot m dir;  (* (x-center).dir *)
    val disc = bm * bm - m2 + rad * rad;  (* discriminant *)
    in
      if (disc < 0.0) then (false, 0.0)  (* imaginary solns only *)
      else let
          val slo = ~bm - (Math.sqrt disc);
          val shi = ~bm + (Math.sqrt disc);
          in
          if (slo < 0.0) then  (* pick smallest positive intersection *)
              if (shi < 0.0) then (false, 0.0)
              else (true, shi)
          else (true, slo)
          end
    end

(*
% for shading, need normal at a point
*)
fun spherenormal pos sp = let
      val Sphere(spos, rad, _) = sp;
      in
        vecscale (vecsub pos spos) (1.0/rad)
      end

(*
% compute camera parameters
*)
fun dtor x = x * Math.pi / 180.0;
fun camparams lookfrom lookat vup fov winsize = let
    val initfirstray = vecsub lookat lookfrom;   (* pre-normalized! *)
    val (lookdir, dist) = vecnorm initfirstray;
    val (scrni, _) = vecnorm (veccross lookdir vup);
    val (scrnj, _) = vecnorm (veccross scrni lookdir);
    val xfov = fov;
    val yfov = fov;
    val xwinsize = (real winsize);  (* for now, square window *)
    val ywinsize = (real winsize);
    val magx = 2.0 * dist * (Math.tan (dtor (xfov / 2.0))) / xwinsize;
    val magy = 2.0 * dist * (Math.tan (dtor (yfov / 2.0))) / ywinsize;
    val scrnx = vecscale scrni magx;
    val scrny = vecscale scrnj magy;
    val firstray = (vecsub initfirstray
          (vecadd
           (vecscale scrnx (0.5 * xwinsize))
           (vecscale scrny (0.5 * ywinsize))));
    in
      (firstray, scrnx, scrny)
    end

(*
% color the given pixel
*)
fun tracepixel spheres lights x y firstray scrnx scrny = let
  val pos = lookfrom;
  val (dir, _) = vecnorm (vecadd (vecadd firstray (vecscale scrnx (real x)))
                    (vecscale scrny (real y)));
  val (hit, dist, sp) = trace spheres pos dir;  (* pick first intersection *)
                                                (* return color of the pixel x,y *)
  in
    if hit then
      shade lights sp pos dir dist (1.0,1.0,1.0)
    else
      background
  end

(*
% find first intersection point in set of all objects
*)
and trace spheres pos dir = let
    (* make a list of the distances to intersection for each hit object *)
      fun sphmap l = (case l
             of nil => nil
              | (x::xs) => let
                val (hit, where') = sphereintersect pos dir x
                in
                  if hit then
                    (where', x) :: (sphmap xs)
                  else
                    (sphmap xs)
                end)
      val dists = sphmap spheres;
      (* return a sphere and its distance *)
      in
        case dists
         of [] => (false, INFINITY, (hd spheres))  (* missed all *)
          | first::rest => let
              val (mindist, sp) = List.foldl
                    (fn ((d1, s1), (d2, s2)) => if (d1 < d2) then (d1,s1) else (d2,s2))
                      first rest
              in
                (true, mindist, sp)
              end
      end

(*
% complete shader, given set of lights, sphere which was hit, ray which hit
%   that sphere, and at what distance, return a color
% contrib answers "what's the most my result can add to the working pixel?"
%   and will abort a reflected or transmitted ray if it gets too small
*)
and shade lights sp lookpos dir dist contrib = let
    val hitpos = vecadd lookpos (vecscale dir dist);
    val ambientlight = (1.0, 1.0, 1.0);  (* full contribution as default *)
    val surf = spheresurf sp;
    val amb = vecmult ambientlight (ambientsurf surf);
    (*  reflected_ray_dir = incoming_dir - (2 cos theta) norm; *)
    val norm = spherenormal hitpos sp;
    val refl = vecadd dir (vecscale norm ((~2.0)*(vecdot dir norm)));
    (*  diff is diffuse and specular contribution *)
    val diff = vecsum (map (fn l => lightray l hitpos norm refl surf) lights);
    val transmitted = transmitsurf surf;
    val simple = vecadd amb diff;
    (* calculate transmitted ray; it adds onto "simple" *)
    val trintensity = vecscale (bodysurf surf) transmitted;
    val (tir, trcol) = if (transmitted < EPSILON) then (false, simple)
                    else let
                      val index = refractsurf surf;
                      in
                        transmitray lights simple hitpos dir index trintensity
                          contrib norm
                      end
    (*  reflected ray; in case of TIR, add transmitted component *)
    val reflsurf = vecscale (specularsurf surf) (reflectsurf surf);
    val reflectiv = if tir then (vecadd trintensity reflsurf) else reflsurf;
    val rcol = if (zerovector reflectiv) then
             trcol
           else
             reflectray hitpos refl lights reflectiv contrib trcol;
   in
     rcol
   end

(*
% Transmit a ray through an object
*)
and transmitray lights color pos dir index intens contrib norm = let
    val newcontrib = vecmult intens contrib;
    in
      if (zerovector newcontrib) then (false, color)  (* cutoff *)
      else let
        val (tir, newdir) = refractray index dir norm;
        in
          if tir then (true, color)
          else let
              val nearpos = vecadd pos (vecscale newdir EPSILON);
              val (hit, dist, sp) = trace world nearpos newdir;
              val newcol = if hit then
                  shade lights sp nearpos newdir dist newcontrib
                  else background;
              in (false, vecadd (vecmult newcol intens) color)
              end
        end
    end

(*
 * Reflect a ray from an object
*)
and reflectray pos newdir lights intens contrib color = let
    val newcontrib = vecmult intens contrib;
    in
    if (zerovector newcontrib) then color
    else let
        val nearpos = vecadd pos (vecscale newdir EPSILON);
        val (hit, dist, sp) = trace world nearpos newdir;
        val newcol = if (hit) then shade lights sp nearpos newdir dist newcontrib
        else background
        in (vecadd color (vecmult newcol intens))
    end
end

(*
 * refract a ray through a surface (ala Foley, vanDamm, p. 757)
 *   outputs a new direction, and if total internal reflection occurred or not
 *)
and refractray newindex olddir innorm = let
    val dotp = ~(vecdot olddir innorm);
    val (norm, k, nr) = if (dotp < 0.0)
        then (vecscale innorm ~1.0, ~dotp, 1.0/newindex)
        else (innorm, dotp, newindex);   (* trans. only with air *)
    val disc = 1.0 - nr*nr*(1.0-k*k);
    in if (disc < 0.0) then (true, (0.0,0.0,0.0)) (* total internal reflection *)
    else let
        val t = nr * k - (Math.sqrt disc);
        in (false, vecadd (vecscale norm t) (vecscale olddir nr))
    end
end

(*
 * For a given light l, surface hit at pos, with norm and refl components
 * to incoming ray, figure out which side of the surface the light is on,
 * and if it's shadowed by another object in the world.  Return light's
 * contribution to the object's color
*)
and lightray l pos norm refl surf = let
    val (ldir, dist) = lightdirection l pos;
    val cosangle = vecdot ldir norm;  (* lightray is this far off normal *)
    val (inshadow, lcolor) = shadowed pos ldir (lightcolor l);
    in
    if (inshadow) then (0.0,0.0,0.0)
    else let
        val diff = diffusesurf surf;
        val spow = specpowsurf surf;  (* assumed trans is same as refl *)
        in
        if (cosangle <= 0.0) then let (* opposite side *)
            val bodycol = bodysurf surf;
            val cosalpha = ~(vecdot refl ldir);
            val diffcont = vecmult (vecscale diff (~cosangle)) lcolor;
            val speccont = if (cosalpha <= 0.0) then (0.0,0.0,0.0)
                else vecmult (vecscale bodycol (expt cosalpha spow)) lcolor;
            in vecadd diffcont speccont
        end else let
            val spec = specularsurf surf;
            val cosalpha = vecdot refl ldir;  (* this far off refl ray (for spec) *)
            val diffcont = vecmult (vecscale diff cosangle) lcolor;
            val speccont = if (cosalpha <= 0.0) then (0.0,0.0,0.0)
                else vecmult (vecscale spec (expt cosalpha spow)) lcolor;
            in vecadd diffcont speccont
        end
    end
end

and lightdirection dir pt = (case dir
       of (Directional(dir, col)) => let
            val (d,_) = vecnorm dir in (d, INFINITY) end
        | (Point(pos, col)) => vecnorm (vecsub pos pt)
      (* end case *))

and shadowed pos dir lcolor = let (* need to offset just a bit *)
    val (hit, dist, sp) = trace world (vecadd pos (vecscale dir EPSILON)) dir;
    in
      if (not hit) then (false, lcolor)
      else (true, lcolor)  (* for now *)
    end

in (* local *)

(*
% "main" routine
*)
(* build the image as a list of pixels in row-major order *)
  fun ray winsize = let
        val lights = testlights;
        val (firstray, scrnx, scrny) = camparams lookfrom lookat vup fov winsize;
        fun f (i, j) = tracepixel world lights i j firstray scrnx scrny
        fun doRow (i, pxls) = let
              fun doCol (j, pixls) = if (j < 0)
                    then doRow (i-1, pixls)
                    else doCol (j-1, f(i, j) :: pixls)
              in
                if (i < 0) then pxls else doCol(winsize-1, pxls)
              end
        in
          doRow (winsize-1, nil)
        end;

end (* local *)


structure Main =
  struct

  (* render 5x5 image *)
    val img = ray 5

  end
