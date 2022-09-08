(* mc-ray.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * An SML implementation of the "Weekend Raytracer" by Peter Shirley.  This
 * code is an SML port of UChicago CMCS15100 course project (Winter 2019).
 *)

structure Real =
  struct
    val posInf = 1.0/0.0
  end

structure Math =
  struct
    val pi = 3.14159265358979323846
    val sqrt = sqrt
    val tan = tan
    val pow = pow
    val atan2 = atan2
    val cos = cos
    val sin = sin
  end

structure List =
  struct
    exception Empty
    fun hd [] = raise Empty
      | hd (x::_) = x
    fun tl [] = raise Empty
      | tl (_::xs) = xs
    fun tabulate (n, f) = if (n < 0)
          then raise Size
          else let
            fun mk 0 = []
              | mk i = f (n-i) :: mk (i-1)
            in
              mk n
            end
    fun foldl f init xs = let
          fun foldf ([], acc) = acc
            | foldf (x::xr, acc) = foldf (xr, f(x, acc))
          in
            foldf (xs, init)
          end
  end

(*********************)

(* rand-64.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Park-Miller RNG (MINSTD) for 64-bit architectures.  This implementation is
 * from
 *      https://en.wikipedia.org/wiki/Lehmer_random_number_generator
 *)

(* NOTE: we currently do not have words, hex literals, or bit operations, so this
 * module was rewritten to use integers
 *)
structure Rand =
  struct

    local
      val state = ref 1234567

      fun init 0 = (state := 1234567)
        | init w = (state := w)

      fun gen32 () = let
            val x = !state
            val x = (x * 48271) mod 2147483647
            in
              state := x;
              x
            end

      val scale : real = 1.0 / 2147483647.0

    in

    fun rand () = scale * real (gen32 ())

    fun randInt n = if (n <= 1)
          then 1
          else gen32() mod n

    end (* local *)
  end

(*********************)

(* interval.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Interval (* : sig

    type t = (real * real)

    val within : real * t -> bool

    val toString : t -> string

  end *) = struct

    type t = (real * real)

    fun within (t, (min, max) : t) = (min <= t) andalso (t <= max)

  end

(*********************)

(* rgb.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure RGB (* : sig

    type t = (real * real * real)

    val add : (t * t) -> t
    val adds : (t * real * t) -> t
    val modulate : (t * t) -> t

    val scale : (real * t) -> t

  (* lerp (u, t, v) = (1-t)*u + t*v; we assume that 0 <= t <= 1 *)
    val lerp : (t * real * t) -> t

  (* standard colors *)
    val black : t
    val red : t
    val green : t
    val blue : t
    val white : t
    val gray : real -> t

  end *) = struct

    type t = (real * real * real)

    fun add ((r1, g1, b1) : t, (r2, g2, b2)) = (r1 + r2, g1 + g2, b1 + b2)
    fun adds ((r1, g1, b1) : t, s, (r2, g2, b2)) = (r1 + s*r2, g1 + s*g2, b1 + s*b2)
    fun modulate ((r1, g1, b1) : t, (r2, g2, b2)) = (r1 * r2, g1 * g2, b1 * b2)

    fun scale (s, (r, g, b) : t) = (s*r, s*g, s*b)

    fun lerp (c1, t, c2) = add (scale(1.0 - t, c1), scale(t, c2))

  (* standard colors *)
    val black : t = (0.0, 0.0, 0.0)
    val red : t = (1.0, 0.0, 0.0)
    val green : t = (0.0, 1.0, 0.0)
    val blue : t = (0.0, 0.0, 1.0)
    val white : t = (1.0, 1.0, 1.0)
    fun gray v = (v, v, v)

  end

(*********************)

(* color.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Color (* : sig

    type t = Word8.word * Word8.word * Word8.word

    val fromRGB : RGB.t -> t

  (* convert an RGB value to an image color value with a gamma correction of 1/2 *)
    val fromRGBWithGamma : RGB.t -> t

  end *) = struct

    type t = int * int * int

    fun toByte (f : real) = let
          val f' = floor (f * 255.99)
          in
            if (f' <= 0) then 0
            else if (255 <= f') then 255
            else f'
          end

    fun fromRGB ((r, g, b) : RGB.t) = (toByte r, toByte g, toByte b)

    fun fromRGBWithGamma ((r, g, b) : RGB.t) = let
          fun cvt f = toByte (Math.sqrt f)
          in
            (cvt r, cvt g, cvt b)
          end

  end

(*********************)

(* vec3.sml
 *
 * COPYRIGHT (c) 2012 The SML3d Project (http://sml3d.cs.uchicago.edu)
 * All rights reserved.
 *
 * Operations on vectors in R^3 (scalar version)
 *)

structure Vec3 (* : sig

    type t = (real * real * real)

    val toString : t -> string

  (* zero vector *)
    val zero : t

  (* vector arithmetic *)
    val negate : t -> t
    val add : (t * t) -> t
    val sub : (t * t) -> t
    val mul : (t * t) -> t

    val scale : (real * t) -> t

  (* adds (u, s, v) = u + s*v *)
    val adds : (t * real * t) -> t

  (* lerp (u, t, v) = (1-t)*u + t*v; we assume that 0 <= t <= 1 *)
    val lerp : (t * real * t) -> t

    val dot : (t * t) -> real

    val normalize : t -> t

    val length : t -> real

  (* cross product *)
    val cross : t * t -> t

  (* iterators *)
    val app  : (real -> unit) -> t -> unit
    val map  : (real -> 'a) -> t -> ('a * 'a * 'a)

  (* graphics related functions *)

  (* `reflect (v, n)` reflects `v` around the normal vector `n` *)
    val reflect : (t * t) -> t

    val rotateX : real -> t -> t
    val rotateY : real -> t -> t
    val rotateZ : real -> t -> t

    val randomPointInSphere : unit -> t

  end *) = struct

    val epsilon = 0.0001

    type t = (real * real * real)

(*
    fun toString ((x, y, z) : t) = concat[
            "<", Real.toString x, ",", Real.toString y, ",", Real.toString z, ">"
          ]
*)

    val zero : t = (0.0, 0.0, 0.0)

    val e1 : t = (1.0, 0.0, 0.0)
    val e2 : t = (0.0, 1.0, 0.0)
    val e3 : t = (0.0, 0.0, 1.0)

    fun negate ((x, y, z) : t) = (~x, ~y, ~z)

    fun add ((x1, y1, z1) : t, (x2, y2, z2)) = (x1+x2, y1+y2, z1+z2)

    fun sub ((x1, y1, z1) : t, (x2, y2, z2)) = (x1-x2, y1-y2, z1-z2)

    fun mul ((x1, y1, z1) : t, (x2, y2, z2)) = (x1*x2, y1*y2, z1*z2)

    fun scale (s, (x, y, z) : t) = (s*x, s*y, s*z)

    fun adds (v1, s, v2) = add(v1, scale(s, v2))

    fun dot ((x1, y1, z1) : t, (x2, y2, z2)) = (x1*x2 + y1*y2 +z1*z2)

    fun lerp (v1, t, v2) = adds (scale(1.0 - t, v1), t, v2)

    fun cross ((x1, y1, z1) : t, (x2, y2, z2)) = (
            y1*z2 - z1*y2,
            z1*x2 - x1*z2,
            x1*y2 - y1*x2
          )

    fun lengthSq v = dot(v, v)
    fun length v = Math.sqrt(lengthSq v)

    fun distanceSq (u, v) = lengthSq (sub (u, v))
    fun distance (u, v) = length (sub (u, v))

    fun lengthAndDir v = let
          val l = length v
          in
            if (l < epsilon)
              then (0.0, zero)
              else (l, scale(1.0 / l, v))
          end

    fun normalize v = let val (_, d) = lengthAndDir v in d end

    fun reflect (v, n) = adds (v, ~2.0 * dot(v, n), n)

    fun rotateX angle = let
          val theta = (Math.pi * angle) / 180.0
          val s = Math.sin theta
          val c = Math.cos theta
          in
            fn ((x, y, z) : t) => (x, c * y - s * z, s * y + c * z)
          end

    fun rotateY angle = let
          val theta = (Math.pi * angle) / 180.0
          val s = Math.sin theta
          val c = Math.cos theta
          in
            fn ((x, y, z) : t) => (c * x + s * z, y, c * z - s * x)
          end

    fun rotateZ angle = let
          val theta = (Math.pi * angle) / 180.0
          val s = Math.sin theta
          val c = Math.cos theta
          in
            fn ((x, y, z) : t) => (c * x - s * y, s * x + c * y, z)
          end

    fun randomPointInSphere () = let
          val pt = (Rand.rand(), Rand.rand(), Rand.rand())
          in
            if (dot(pt, pt) < 1.0) then pt else randomPointInSphere()
          end

  (* iterators *)
    fun map f (x, y, z) = (f x, f y, f z)
    fun app (f : 'a -> unit) (x, y, z) = (f x; f y; f z)

  end

(*********************)

(* ray.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Ray (* : sig

    type t = Vec3.t * Vec3.t

    val make : Vec3.t * Vec3.t -> t

    val eval : t * real -> Vec3.t

  end *) = struct

    type t = (Vec3.t * Vec3.t)

    fun make (origin, dir) = (origin, Vec3.normalize dir)

    fun eval ((origin, dir), t) = Vec3.adds (origin, t, dir)

  end

(*********************)

(* material.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Material (* : sig

    type t

  (* Hit(t, pt, norm, material) *)
    datatype hit = Hit of real * Vec3.t * Vec3.t * t

    val getEmission : hit -> RGB.t
    val getHitInfo : hit * Ray.t -> (RGB.t * Ray.t) option

    val flat : RGB.t -> t
    val normal : t
    val lambertian : RGB.t -> t
    val metal : RGB.t * real -> t
    val diffuseLight : RGB.t -> t

  end *) = struct

    datatype hit = Hit of real * Vec3.t * Vec3.t * t

    and t = Material of
        (hit -> RGB.t) *                                (* emit *)
        (Ray.t * hit -> (RGB.t * Ray.t) option)         (* scatter *)

    fun getEmission hit = (case hit
      of Hit(_, _, _, Material(emit, _)) => emit hit
      (* end case *))

    fun getHitInfo (hit, ray) = (case hit
      of Hit(_, _, _, Material(_, scatter)) => scatter (ray, hit)
      (* end case *))

    fun flat rgb = Material(
          fn _ => RGB.black,
          fn _ => SOME(rgb, (Vec3.zero, Vec3.zero)))

    val normal = Material(
          fn _ => RGB.black,
          fn (_, Hit(_, _, (x, y, z), _)) => SOME(
                (0.5 * (x + 1.0), 0.5 * (y + 1.0), 0.5 * (z + 1.0)),
                (Vec3.zero, Vec3.zero)))

    fun lambertian albedo = Material(
          fn _ => RGB.black,
          fn (ray, Hit(_, pt, norm, _)) => SOME(
                albedo,
                Ray.make(pt, Vec3.add(norm, Vec3.randomPointInSphere()))))

    fun metal (albedo, fuzz) = Material(
          fn _ => RGB.black,
          fn ((_, rdir), Hit(_, pt, norm, _)) => let
                val dir = Vec3.adds(
                      Vec3.reflect(rdir, norm),
                      fuzz,
                      Vec3.randomPointInSphere())
                in
                  if Vec3.dot(dir, norm) <= 0.0
                    then NONE
                    else SOME(albedo, Ray.make(pt, dir))
                end)

    fun diffuseLight rgb = Material(
          fn _ => rgb,
          fn _ => NONE)

  end

(*********************)

(* object.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Object (* : sig

    datatype maybe_hit = Miss | Hit of Material.hit

    datatype t = Obj of Ray.t * Interval.t -> maybe_hit

  (* test a ray against an object *)
    val hitTest : t * Ray.t * Interval.t -> maybe_hit

  (* an empty object that cannot be hit by rays *)
    val empty : t

  (* make an object from a list of objects *)
    val fromList : t list -> t

  (* translate the object by the given offset *)
    val translate : Vec3.t * t -> t

  (* rotate the object counter-clockwise by the specified angle (in degrees) *)
    val rotateX : real * t -> t
    val rotateY : real * t -> t
    val rotateZ : real * t -> t

  end *) = struct

    datatype maybe_hit = Miss | Hit of Material.hit

    datatype t = Obj of Ray.t * Interval.t -> maybe_hit

    fun hitTest (Obj hit, ray, minMaxT) = hit(ray, minMaxT)

    val empty = Obj(fn _ => Miss)

  (* fast min/max functions for reals *)
    fun fmin (x : real, y) = if (x < y) then x else y
    fun fmax (x : real, y) = if (x > y) then x else y

    fun closer (Miss, maybeHit) = maybeHit
      | closer (maybeHit, Miss) = maybeHit
      | closer (hit1, hit2) = (case (hit1, hit2)
        of (Hit(Material.Hit(t1, _, _, _)), Hit(Material.Hit(t2, _, _, _))) =>
            if (t1 <= t2) then hit1 else hit2
        (* end case *))

    fun fromList nil = empty
      | fromList (obj :: nil) = obj
      | fromList objs = let
          val obj1 = List.hd objs
          val objr = List.tl objs
          fun hitTest' (ray, minMaxT) = List.foldl
                (fn (obj, mhit) => closer(mhit, hitTest(obj, ray, minMaxT)))
                  Miss objs
          in
            Obj hitTest'
          end

    fun translate (delta, Obj hit) = let
          fun hitTest' ((origin, dir), minMaxT) = (
                case hit ((Vec3.sub(origin, delta), dir), minMaxT)
                 of Hit(Material.Hit(t, pt, norm, material)) =>
                      Hit(Material.Hit(t, Vec3.add(pt, delta), norm, material))
                  | Miss => Miss
                (* end case *))
          in
            Obj hitTest'
          end

    fun rotateX (angle, Obj hit) = let
          val toObj = Vec3.rotateX (~angle)
          val toWorld = Vec3.rotateX angle
          fun hitTest' ((origin, dir), minMaxT) = (
                case hit ((toObj origin, toObj dir), minMaxT)
                 of Hit(Material.Hit(t, pt, norm, material)) =>
                      Hit(Material.Hit(t, toWorld pt, toWorld norm, material))
                  | Miss => Miss
                (* end case *))
          in
            Obj hitTest'
          end

    fun rotateY (angle, Obj hit) = let
          val toObj = Vec3.rotateY (~angle)
          val toWorld = Vec3.rotateY angle
          fun hitTest' ((origin, dir), minMaxT) = (
                case hit ((toObj origin, toObj dir), minMaxT)
                 of Hit(Material.Hit(t, pt, norm, material)) =>
                      Hit(Material.Hit(t, toWorld pt, toWorld norm, material))
                  | Miss => Miss
                (* end case *))
          in
            Obj hitTest'
          end

    fun rotateZ (angle, Obj hit) = let
          val toObj = Vec3.rotateZ (~angle)
          val toWorld = Vec3.rotateZ angle
          fun hitTest' ((origin, dir), minMaxT) = (
                case hit ((toObj origin, toObj dir), minMaxT)
                 of Hit(Material.Hit(t, pt, norm, material)) =>
                      Hit(Material.Hit(t, toWorld pt, toWorld norm, material))
                  | Miss => Miss
                (* end case *))
          in
            Obj hitTest'
          end

  end

(*********************)

(* sphere.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Sphere (* : sig

    val make : Vec3.t * real * Material.t -> Object.t

  end *) = struct

    fun make (center, radius, material) = let
          val rSq = radius * radius
          val invR = 1.0 / radius
    fun hitTest (ray, minMaxT) = let
                val (ro, rd) = ray
                val q = Vec3.sub(ro, center)
                val b = 2.0 * Vec3.dot(rd, q)
                val c = Vec3.dot(q, q) - rSq
                val disc = b*b - 4.0*c
                in
                  if (disc < 0.0)
                    then Object.Miss
                    else let
                      val t = 0.5 * (~b - Math.sqrt disc)
                      in
                        if Interval.within(t, minMaxT)
                          then let
                            val pt = Ray.eval(ray, t)
                            in
                              Object.Hit(Material.Hit(
                                t, pt,
                                Vec3.scale(invR, Vec3.sub(pt, center)),
                                material))
                            end
                          else Object.Miss
                      end
                end
          in
            Object.Obj hitTest
          end

  end

(*********************)

(* image.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Image (* : sig

  (* Img(wid, ht, pixels) *)
    datatype t = Img of int * int * Color.t list

    val writePPM : string * t -> unit

  end *) = struct

    datatype t = Img of int * int * Color.t list

(* no I/O
    fun writePPM (file, Img(wid, ht, pixels)) = let
      val outS = TextIO.openOut file
      fun pr s = TextIO.output(outS, s)
      fun pixToS (r, g, b) = concat [Int.toString r, " ", Int.toString g, " ", Int.toString b]
      in
      (* write header for Plain PPM file: http://netpbm.sourceforge.net/doc/ppm.html *)
        pr "P3\n";
        pr (concat[Int.toString wid, " ", Int.toString ht, "\n"]);
        pr "255\n";
      (* write pixels *)
        List.app (fn pix => (pr (pixToS pix); pr "\n")) pixels;
      (* close file *)
        TextIO.closeOut outS
      end
*)

  end

(*********************)

(* camera.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Camera (* : sig

    type t

 (* make (wid, ht, ns, pos, lookAt, up, fov) *)
    val make : int * int * int * Vec3.t * Vec3.t * Vec3.t * real -> t

  (* simple camera located at the origin looking down the negative Z axis *)
    val simpleCamera : int * int * int * real -> t

    type pixel_renderer = (int * int -> Color.t)

    val makePixelRenderer : (int * int -> RGB.t) * (RGB.t -> Color.t) -> pixel_renderer

    val foreachPixel : t * pixel_renderer -> Image.t

    val pixelToRGB : t * (Ray.t -> RGB.t) -> int * int -> RGB.t

    val rayToRGB : Ray.t -> RGB.t

    val aaPixelToRGB : t * (Ray.t -> RGB.t) -> int * int -> RGB.t

  end *) = struct

    datatype t = Cam of (
        int *           (* width of image *)
        int *           (* height of image *)
        int *           (* number of samples per pixel *)
        Vec3.t *        (* position of camera *)
        Vec3.t *        (* upper-left-corner of image plane *)
        Vec3.t *        (* horizontal pixel-wide vector parallel to image pointing right *)
        Vec3.t)         (* vertical pixel-wide vector parallel to image pointing down *)

    fun make (wid, ht, ns, pos, lookAt, up, fov) = let
          val dir = Vec3.normalize (Vec3.sub (lookAt, pos))
          val right = Vec3.normalize (Vec3.cross (dir, up))
          val up = Vec3.normalize (Vec3.cross (right, dir))
          val pw = 2.0 / real wid
          val aspect = real ht / real wid
          val theta = (Math.pi * fov) / 180.0
          val flen = 1.0 / Math.tan (0.5 * theta)
          val imgCenter = Vec3.add(pos, Vec3.scale(flen, dir))
          val ulc = Vec3.sub(Vec3.add(imgCenter, Vec3.scale(aspect, up)), right)
          in
            Cam(wid, ht, ns, pos, ulc, Vec3.scale(pw, right), Vec3.scale(~pw, up))
          end

    fun simpleCamera (wid, ht, ns, flen) = let
          val pw = 2.0 / real wid
          val aspect = real ht / real wid
          in
            Cam(
              wid, ht, ns, Vec3.zero,
              (0.5 * pw - 1.0, aspect, ~ flen), (pw, 0.0, 0.0), (0.0, ~pw, 0.0))
          end

    type pixel_renderer = (int * int -> Color.t)

    fun makePixelRenderer (toRGB, cvt) coords = cvt(toRGB coords)

    fun foreachPixel (Cam(wid, ht, _, _, _, _, _), pr) = let
          fun rowLp (r, colors) = if (r < 0) then colors else colLp(r-1, wid-1, colors)
          and colLp (r, c, colors) = if (c < 0)
                then rowLp (r, colors)
                else colLp (r, c-1, pr(r, c) :: colors)
          in
            Image.Img(wid, ht, rowLp (ht - 1, []))
          end

    fun rayForPixel (Cam(_, _, _, pos, ulc, hvec, vvec)) = let
          val ulcCenter = Vec3.adds(ulc, 0.5, Vec3.add(hvec, vvec))
          in
            fn (r, c) => Ray.make (
                pos,
                Vec3.add (ulcCenter,
                  Vec3.add (
                    Vec3.scale (real r, vvec),
                    Vec3.scale (real c, hvec))))
          end

    fun pixelToRGB (cam, trace) = let
          val rfp = rayForPixel cam
          in
            fn coords => trace (rfp coords)
          end

    fun rayToRGB ((_, (_, y, _)) : Ray.t) =
          RGB.lerp (RGB.white, 0.5 * (y + 1.0), (0.5, 0.7, 1.0))

    fun raysForPixel (Cam(_, _, ns, pos, ulc, hvec, vvec)) (r, c) = let
          val r = real r
          val c = real c
          val ulcDir = Vec3.sub(ulc, pos)
          fun mkRay _ = let
                val dir = Vec3.adds(ulcDir, r + Rand.rand(), vvec)
                val dir = Vec3.adds(dir, c + Rand.rand(), hvec)
                in
                  Ray.make (pos, dir)
                end
          in
            List.tabulate (ns, mkRay)
          end

    fun aaPixelToRGB (cam, trace) = let
          val Cam(_, _, ns, _, _, _, _) = cam
          val rfp = raysForPixel cam
          val scale = if ns = 0 then 1.0 else 1.0 / real ns
          in
            fn coords => RGB.scale(
                scale,
                List.foldl
                  (fn (ray, c) => RGB.add(c, trace ray))
                    RGB.black (rfp coords))
          end

  end

(*********************)

(* trace.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Trace (* : sig

  (* ray caster for testing purposes *)
    val castRay : Object.t -> Ray.t -> RGB.t

  (* Given a world object and a maximum tracing depth, this function
   * returns a function that will recursively trace a ray through the
   * world to compute a color
   *)
    val traceRay : Object.t * int -> Ray.t -> RGB.t

    val rayTracer : Camera.t * Object.t -> Image.t

    val timeIt : (unit -> 'a) -> 'a

  end *) = struct

    fun castRay world ray = (
          case Object.hitTest (world, ray, (0.0, Real.posInf))
           of Object.Miss => Camera.rayToRGB ray
            | Object.Hit hit => (case Material.getHitInfo(hit, ray)
                 of NONE => Material.getEmission hit
                  | SOME(aten, _) => RGB.add(Material.getEmission hit, aten)
                (* end case *))
          (* end case *))

    fun traceRay (world, maxDepth) = let
          val minMaxT = (0.001, Real.posInf)
          fun trace (ray, depth) = if (depth <= 0)
                then RGB.black
                else (case Object.hitTest (world, ray, minMaxT)
                   of Object.Miss => Camera.rayToRGB ray
                    | Object.Hit hit => (case Material.getHitInfo(hit, ray)
                         of NONE => Material.getEmission hit
                          | SOME(aten, reflect) => RGB.add(
                              Material.getEmission hit,
                              RGB.modulate(aten, trace (reflect, depth-1)))
                        (* end case *))
                  (* end case *))
          in
            fn ray => trace(ray, maxDepth)
          end

    fun rayTracer (cam, world) =
          Camera.foreachPixel (
            cam,
            Camera.makePixelRenderer (
              Camera.aaPixelToRGB(cam, traceRay (world, 20)),
              Color.fromRGBWithGamma))

    (* fun timeIt f = let
          val rtStart = Timer.startRealTimer()
          val result = f()
          val t = Timer.checkRealTimer rtStart
          in
            print (concat["total time = ", Time.toString t, "\n"]);
            result
          end *)

  end

(*********************)

(* test-random-scene.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure TestRandomScene =
  struct

    fun randomSphere (x, z) = let
          val chooseMat = Rand.rand()
          val c = let
                val x = real x + (0.9 * Rand.rand())
                val z = real z + (0.9 * Rand.rand())
                in
                  (x, 0.2, z)
                end
          val mat = if chooseMat < 0.8
                then Material.lambertian (
                    Rand.rand() * Rand.rand(),
                    Rand.rand() * Rand.rand(),
                    Rand.rand() * Rand.rand())
                else Material.metal (
                    ( 0.5 * (1.0 + Rand.rand()),
                      0.5 * (1.0 + Rand.rand()),
                      0.5 * (1.0 + Rand.rand()) ),
                    0.5 * Rand.rand())
          in
            Sphere.make (c, 0.2, mat)
          end

    fun makeScene () = let
          fun lp (x, z, objs) =
                if (z < 11) then lp (x, z+1, randomSphere(x, z) :: objs)
                else if (x < 11) then lp (x+1, ~11, objs)
                else objs
          in
            Object.fromList (
              lp (~11, ~11, [
                  Sphere.make((0.0, ~1000.0, 0.0), 1000.0,
                    Material.lambertian(RGB.gray 0.5)),
                  Sphere.make((4.0, 1.0, 0.0), 1.0,
                    Material.metal((0.7, 0.6, 0.5), 0.0)),
                  Sphere.make((~4.0, 1.0, 0.0), 1.0,
                    Material.lambertian(0.4, 0.2, 0.1))
                ]))
          end

    fun buildScene (wid, ht, ns) = let
          val cam = Camera.make (
                wid, ht, ns,
                (13.0, 2.0, 3.0), Vec3.zero, (0.0, 1.0, 0.0),
                30.0)
          val world = makeScene()
          in
            (cam, world)
          end


    fun test (wid, ht, ns) = let
          val scene = buildScene(wid, ht, ns)
          in
            Trace.rayTracer scene
          end

  end

val result = TestRandomScene.test (3, 2, 5)
