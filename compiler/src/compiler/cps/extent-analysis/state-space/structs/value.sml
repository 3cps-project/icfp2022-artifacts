(* value.sml
 *
 * Abstract values
 *)

(* closures *)
structure CloBase : HASH_CONS_BASE =
  struct

    type t = (CPS.lambda * Env.t * TEnv.t)

    fun toString (((_, lab, _, _, _), env, tenv) : t) =
          String.concat["(clo ", Label.toString lab, ")"]

    fun compare (clo1 : t, clo2 : t) =
        (case Label.compare(#2(#1 clo1), #2(#1 clo2))
          of EQUAL =>
             (case Env.compare (#2 clo1, #2 clo2)
               of EQUAL => TEnv.compare (#3 clo1, #3 clo2)
                | ord => ord)
           | ord => ord
        (* end case *))

    fun same (clo1 : t, clo2 : t) =
        case compare (clo1, clo2)
         of EQUAL => true
          | _ => false

    fun hash (((_, lab, _, _, _), env, tenv) : t) : word =
        Label.hash lab

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

  end (* Clo *)

structure Clo = MyHashCons (structure Base = CloBase)

structure DataValueBase =
  struct

    type t = Label.t * CPSDataCon.t * Addr.t option

    fun toString (_, dcon, ao) = let
          val ao_str = (case ao
                 of NONE => ""
                  | SOME a => " " ^ Addr.toString a
                (* end case *))
          in
            String.concat["(dv ", CPSDataCon.toString dcon, ao_str, ")"]
          end

    fun compare ((lab1, dc1, a1o), (lab2, dc2, a2o)) =
        (case Label.compare (lab1, lab2)
          of EQUAL =>
             (case CPSDataCon.compare (dc1, dc2)
               of EQUAL =>
                  (case (a1o, a2o)
                    of (NONE, NONE) => EQUAL
                     | (SOME _, NONE) => GREATER
                     | (NONE, SOME _) => LESS
                     | (SOME a1, SOME a2) => Addr.compare (a1, a2)
                  (* end case *))
                | ord => ord
             (* end case *))
           | ord => ord)
            
    fun same (dv1, dv2) =
        case compare (dv1, dv2)
         of EQUAL => true
          | _ => false

    fun hash (lab, dc, a) =
        Label.hash lab

    local
        structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

  end

structure DataValue = MyHashCons (structure Base = DataValueBase)

structure TupleValueBase =
  struct

    type t = Label.t * (Addr.t list)

    fun toString (_, alist) =
          String.concat ["(tv ", String.concatWithMap " " Addr.toString alist, ")"]

    fun compare ((lab1, alist1), (lab2, alist2)) =
        case Label.compare (lab1, lab2)
         of EQUAL => List.collate Addr.compare (alist1, alist2)
          | ord => ord

    fun same (tv1, tv2) =
        case compare (tv1, tv2)
         of EQUAL => true
          | _ => false

    fun hash (lab, _) = Label.hash lab

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

  end

structure TupleValue = MyHashCons (structure Base = TupleValueBase)

structure RefValue =
  struct

    type t = Addr.t

    fun toString a = String.concat ["(ref ", Addr.toString a, ")"]

    val compare = Addr.compare

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    structure MSet = MyHashSetFn (struct type hash_key = t val sameKey = Addr.same val hashVal = Addr.hash end)
    end (* local *)

  end

signature ABS_DOM = sig

  type dom = int
  type t
  val from : dom -> t
  val join : t * t -> t
  val compare : t * t -> order
  val same : t * t -> bool
  val hash : t -> word

end

(* TODO: eventually this should track ranges, so that we can eliminate bounds checks *)
structure IntAbsDom : ABS_DOM = struct

  type dom = int
  type t = unit
  fun from _ = ()
  fun join _ = ()
  fun compare _ = EQUAL
  fun same _ = true
  fun hash _ = Word.fromInt 0

end

structure ArrayValue =
  struct

    type t = IntAbsDom.t * Addr.t

    fun toString (_, a) = String.concat ["(ref ", Addr.toString a, ")"]

    fun compare ((iad1, a1), (iad2, a2)) =
        case IntAbsDom.compare (iad1, iad2)
         of EQUAL => Addr.compare (a1, a2)
          | ord => ord
    fun same ((iad1, a1), (iad2, a2)) = IntAbsDom.same (iad1, iad2) andalso Addr.same (a1, a2)
    fun hash (iad, a) = Addr.hash a

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    structure MSet = MyHashSetFn (struct type hash_key = t val sameKey = same val hashVal = hash end)
    end (* local *)

  end

signature FULL_VALUE_BASE = sig

    include VALUE_BASE

    val empty : CPSTypes.t -> t

    val add_unknown : t -> t

    val add_clo : t * Clo.t -> t
    val add_dv : t * DataValue.t -> t
    val add_tv : t * TupleValue.t -> t
    val add_ref : t * Addr.t -> t

    val fold_clos : (Clo.t * 'a -> 'a) -> 'a -> t -> 'a
    val fold_dvs : (DataValue.t * 'a -> 'a) -> 'a -> t -> 'a
    val fold_tvs : (TupleValue.t * 'a -> 'a) -> 'a -> t -> 'a
    val fold_refs : (RefValue.t * 'a -> 'a) -> 'a -> t -> 'a
    val fold_arrs : (ArrayValue.t * 'a -> 'a) -> 'a -> t -> 'a
    val fold_unknown : ('a -> 'a) -> 'a -> t -> 'a
    val fold : (Clo.t * 'a -> 'a)
                -> (DataValue.t * 'a -> 'a)
                -> (TupleValue.t * 'a -> 'a)
                -> (RefValue.t * 'a -> 'a)
                -> (ArrayValue.t * 'a -> 'a)
                -> ('a -> 'a)
                -> 'a -> t -> 'a

    val labels : t -> Label.Set.set

    val copy : t -> t

    val select_offset : (Addr.t * 'a -> 'a) -> 'a -> (int * t) -> 'a
    val match_dcon : (Addr.t * 'a -> 'a) -> 'a -> (CPSDataCon.t * t) -> 'a

  end 

structure Value2 :> FULL_VALUE_BASE = struct

    structure DV = DataValue
    structure TV = TupleValue
    structure RV = RefValue
    structure ARRV = ArrayValue

    type t = Clo.Set.set * DV.Set.set * TV.Set.set * RV.Set.set * ARRV.Set.set * bool

    fun empty _ = (Clo.Set.empty, DV.Set.empty, TV.Set.empty, RV.Set.empty, ARRV.Set.empty, false)

    fun add_unknown (clos, dvs, tvs, rvs, arrvs, unknown) =
        (clos, dvs, tvs, rvs, arrvs, true)
    fun add_clo ((clos, dvs, tvs, rvs, arrvs, unknown), clo) =
        (Clo.Set.add (clos, clo), dvs, tvs, rvs, arrvs, unknown)
    fun add_dv ((clos, dvs, tvs, rvs, arrvs, unknown), dv) = 
        (clos, DV.Set.add (dvs, dv), tvs, rvs, arrvs, unknown)
    fun add_tv ((clos, dvs, tvs, rvs, arrvs, unknown), tv) = 
        (clos, dvs, TV.Set.add (tvs, tv), rvs, arrvs, unknown)
    fun add_ref ((clos, dvs, tvs, rvs, arrvs, unknown), a) = 
        (clos, dvs, tvs, RV.Set.add (rvs, a), arrvs, unknown)
    fun add_arr ((clos, dvs, tvs, rvs, arrvs, unknown), a) = 
        (clos, dvs, tvs, rvs, ARRV.Set.add (arrvs, (IntAbsDom.from 0, a)), unknown)

    fun isEmpty (clos, dvs, tvs, rvs, arrvs, unknown) =
        Clo.Set.isEmpty clos andalso
        DV.Set.isEmpty dvs andalso
        TV.Set.isEmpty tvs andalso
        RV.Set.isEmpty rvs andalso
        ARRV.Set.isEmpty arrvs andalso
        not unknown

    fun copy d = d

    fun join ((clos1, dvs1, tvs1, rvs1, arrvs1, unknown1),
              (clos2, dvs2, tvs2, rvs2, arrvs2, unknown2)) = let
        val clos = if Clo.Set.isEmpty clos1 then clos2
                   else if Clo.Set.isEmpty clos2 then clos1
                   else Clo.Set.union (clos1, clos2)
        val dvs = if DV.Set.isEmpty dvs1 then dvs2
                  else if DV.Set.isEmpty dvs2 then dvs1
                  else DV.Set.union (dvs1, dvs2)
        val tvs = if TV.Set.isEmpty tvs1 then tvs2
                  else if TV.Set.isEmpty tvs2 then tvs1
                  else TV.Set.union (tvs1, tvs2)
        val rvs = if RV.Set.isEmpty rvs1 then rvs2
                  else if RV.Set.isEmpty rvs2 then rvs1
                  else RV.Set.union (rvs1, rvs2)
        val arrvs = if ARRV.Set.isEmpty arrvs1 then arrvs2
                  else if ARRV.Set.isEmpty arrvs2 then arrvs1
                  else ARRV.Set.union (arrvs1, arrvs2)
        val unknown = unknown1 orelse unknown2
    in (clos, dvs, tvs, rvs, arrvs, unknown) end
    (* is perhaps more efficient than: *)
    (* (Clo.Set.union(clos1, clos2),
        DV.Set.union(dvs1, dvs2),
        TV.Set.union(tvs1, tvs2),
        RV.Set.union (rvs1, rvs2),
        unknown1 orelse unknown2) *)

    fun difference ((clos1, dvs1, tvs1, rvs1, arrvs1, unknown1), 
                    (clos2, dvs2, tvs2, rvs2, arrvs2, unknown2)) = let
        val clos = Clo.Set.difference (clos1, clos2)
        val dvs = DV.Set.difference (dvs1, dvs2)
        val tvs = TV.Set.difference (tvs1, tvs2)
        val rvs = RV.Set.difference (rvs1, rvs2)
        val arrvs = ARRV.Set.difference (arrvs1, arrvs2)
        val unknown = unknown1 andalso not unknown2
    in (clos, dvs, tvs, rvs, arrvs, unknown) end

    fun fold_clos f acc (clos, dvs, tvs, rvs, arrvs, unknown) = Clo.Set.foldl f acc clos
    fun fold_dvs f acc (clos, dvs, tvs, rvs, arrvs, unknown) = DV.Set.foldl f acc dvs
    fun fold_tvs f acc (clos, dvs, tvs, rvs, arrvs, unknown) = TV.Set.foldl f acc tvs
    fun fold_refs f acc (clos, dvs, tvs, rvs, arrvs, unknown) = RV.Set.foldl f acc rvs
    fun fold_arrs f acc (clos, dvs, tvs, rvs, arrvs, unknown) = ARRV.Set.foldl f acc arrvs
    fun fold_unknown f acc (clos, dvs, tvs, rvs, arrvs, unknown) = if unknown then f acc else acc

    fun fold f_clo f_dv f_tv f_rv f_arr f_unknown acc (clos, dvs, tvs, rvs, arrvs, unknown) = let
        val acc = if unknown then f_unknown acc else acc
        val acc = ARRV.Set.foldl f_arr acc arrvs
        val acc = RV.Set.foldl f_rv acc rvs
        val acc = TV.Set.foldl f_tv acc tvs
        val acc = DV.Set.foldl f_dv acc dvs
        val acc = Clo.Set.foldl f_clo acc clos
    in acc end

    fun select_offset f acc (offset, (clos, dvs, tvs, rvs, arrvs, un)) = let
        fun handle_tv (tv, acc) = let
            val (_, addrs) = TupleValue.get tv
        in if offset <= List.length addrs
           then let
               val a = List.nth (addrs, offset-1)
           in f (a, acc) end
           else acc
        end
    in TV.Set.foldl handle_tv acc tvs end

    fun match_dcon f acc (dcon, (clos, dvs, tvs, rvs, arrvs, un)) = let
        fun handle_dv (dv, acc) = let
            val (_, dcon', ao) = DataValue.get dv
        in case CPSDataCon.compare (dcon, dcon')
            of EQUAL =>
               (case ao
                 of NONE => raise Fail "DCON expected to be paired with value"
                  | SOME(a) => f (a, acc))
             | _ => acc
        end
    in DV.Set.foldl handle_dv acc dvs end

    (* Returns all the labels of this value *)
    (* so far the only values with labels are closures *)
    fun labels (clos, dvs, tvs, rvs, arrvs, un) =
        Clo.Set.foldl
            (fn (clo, acc) => let
                 val ((_, lab, _, _, _), _, _) = Clo.get clo
             in Label.Set.add (acc, lab) end)
              Label.Set.empty clos

    fun toString d = let
        fun toString_make toString (x, acc) = (toString x) :: acc
        val strs = fold (toString_make Clo.toString) (toString_make DV.toString)
                        (toString_make TV.toString) (toString_make RV.toString)
                        (toString_make ARRV.toString)
                        (fn (acc) => "unknown" :: acc)
                        [] d
    in String.concat["{", String.concatWith " " strs, "}"] end
                         
    fun compare ((_, _, _, _, _, false), (_, _, _, _, _, true)) = LESS
      | compare ((_, _, _, _, _, true), (_, _, _, _, _, false)) = GREATER
      | compare ((clos1, dvs1, tvs1, rvs1, arrvs1, _), (clos2, dvs2, tvs2, rvs2, arrvs2, _)) = (
          case RV.Set.compare(rvs1, rvs2)
           of EQUAL =>
              (case ARRV.Set.compare (arrvs1, arrvs2)
                of EQUAL =>
                   (case DV.Set.compare(dvs1, dvs2)
                     of EQUAL =>
                        (case TV.Set.compare(tvs1, tvs2)
                          of EQUAL => Clo.Set.compare(clos1, clos2)
                           | ord => ord
                        (* end case *))
                      | ord => ord
                   (* end case *))
                 | ord => ord
              (* end case *))
            | ord => ord
      (* end case *))

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

  end


structure Value3 :> FULL_VALUE_BASE = struct

    structure DV = DataValue
    structure TV = TupleValue
    structure RV = RefValue
    structure ARRV = ArrayValue

    type t = Clo.MSet.set * DV.MSet.set * TV.MSet.set * RV.MSet.set * ARRV.MSet.set * (bool ref)

    val size = 4

    fun empty _ = (Clo.MSet.mkEmpty size, DV.MSet.mkEmpty size, TV.MSet.mkEmpty size, RV.MSet.mkEmpty size, ARRV.MSet.mkEmpty size, ref false)

    fun add_unknown (d as (clos, dvs, tvs, rvs, arrvs, unknown)) =
        (unknown := true; d)
    fun add_clo (d as (clos, dvs, tvs, rvs, arrvs, unknown), clo) =
        (Clo.MSet.add (clos, clo); d)
    fun add_dv (d as (clos, dvs, tvs, rvs, arrvs, unknown), dv) =
        (DV.MSet.add (dvs, dv); d)
    fun add_tv (d as (clos, dvs, tvs, rvs, arrvs, unknown), tv) =
        (TV.MSet.add (tvs, tv); d)
    fun add_ref (d as (clos, dvs, tvs, rvs, arrvs, unknown), a) =
        (RV.MSet.add (rvs, a); d)
    fun add_arr (d as (clos, dvs, tvs, rvs, arrvs, unknown), a) =
        (ARRV.MSet.add (arrvs, (IntAbsDom.from 0, a)); d)

    fun isEmpty (clos, dvs, tvs, rvs, arrvs, unknown) =
        Clo.MSet.isEmpty clos andalso
        DV.MSet.isEmpty dvs andalso
        TV.MSet.isEmpty tvs andalso
        RV.MSet.isEmpty rvs andalso
        ARRV.MSet.isEmpty arrvs andalso
        not (! unknown)

    fun join (d1 as (clos1, dvs1, tvs1, rvs1, arrvs1, unknown1) : t,
              (clos2, dvs2, tvs2, rvs2, arrvs2, unknown2) : t) = let
        val () = Clo.MSet.app (fn clo => (Clo.MSet.add (clos1, clo); ())) clos2
        val () = TV.MSet.app (fn tv => (TV.MSet.add (tvs1, tv); ())) tvs2
        val () = DV.MSet.app (fn dv => (DV.MSet.add (dvs1, dv); ())) dvs2
        val () = RV.MSet.app (fn rv => (RV.MSet.add (rvs1, rv); ())) rvs2
        val () = ARRV.MSet.app (fn arrv => (ARRV.MSet.add (arrvs1, arrv); ())) arrvs2
        val () = unknown1 := ((! unknown1) orelse (! unknown2))
    in d1 end


    fun copy (d as (clos, dvs, tvs, rvs, arrvs, unknown)) = let
        val clos' = Clo.MSet.copy clos
        val dvs' = DV.MSet.copy dvs
        val tvs' = TV.MSet.copy tvs
        val rvs' = RV.MSet.copy rvs
        val arrvs' = ARRV.MSet.copy arrvs
        val unknown' = ref (! unknown)
    in (clos', dvs', tvs', rvs', arrvs', unknown') end

    (* most of the time we will be subtracting a large value from a small one,
       so we iterate through d1 (small), not d2 (large) *)
    fun difference (d1 as (clos1, dvs1, tvs1, rvs1, arrvs1, unknown1),
                    (clos2, dvs2, tvs2, rvs2, arrvs2, unknown2)) = let
        val d as (clos, dvs, tvs, rvs, arrvs, unknown) = empty ()
        val () = Clo.MSet.app (fn clo => if Clo.MSet.member (clos2, clo) then () else (Clo.MSet.add (clos, clo); ())) clos1
        val () = TV.MSet.app  (fn tv  => if TV.MSet.member  (tvs2, tv)   then () else (TV.MSet.add  (tvs, tv);   ()))   tvs1
        val () = DV.MSet.app  (fn dv  => if DV.MSet.member  (dvs2, dv)   then () else (DV.MSet.add  (dvs, dv);   ()))   dvs1
        val () = RV.MSet.app  (fn rv  => if RV.MSet.member  (rvs2, rv)   then () else (RV.MSet.add  (rvs, rv);   ()))   rvs1
        val () = ARRV.MSet.app  (fn arrv  => if ARRV.MSet.member  (arrvs2, arrv)   then () else (ARRV.MSet.add  (arrvs, arrv);   ()))   arrvs1
        val () = unknown := ((! unknown1) andalso not (! unknown2))
    in d end

    fun fold_clos f acc (clos, dvs, tvs, rvs, arrvs, unknown) = Clo.MSet.fold f acc clos
    fun fold_dvs f acc (clos, dvs, tvs, rvs, arrvs, unknown) = DV.MSet.fold f acc dvs
    fun fold_tvs f acc (clos, dvs, tvs, rvs, arrvs, unknown) = TV.MSet.fold f acc tvs
    fun fold_refs f acc (clos, dvs, tvs, rvs, arrvs, unknown) = RV.MSet.fold f acc rvs
    fun fold_arrs f acc (clos, dvs, tvs, rvs, arrvs, unknown) = ARRV.MSet.fold f acc arrvs
    fun fold_unknown f acc (clos, dvs, tvs, rvs, arrvs, unknown) = if (! unknown) then f acc else acc

    fun fold f_clo f_dv f_tv f_rv f_arr f_unknown acc (clos, dvs, tvs, rvs, arrvs, unknown) = let
        val acc = if (! unknown) then f_unknown acc else acc
        val acc = ARRV.MSet.fold f_arr acc arrvs
        val acc = RV.MSet.fold f_rv acc rvs
        val acc = TV.MSet.fold f_tv acc tvs
        val acc = DV.MSet.fold f_dv acc dvs
        val acc = Clo.MSet.fold f_clo acc clos
    in acc end

    fun select_offset f acc (offset, (clos, dvs, tvs, rvs, arrvs, un)) = let
        fun handle_tv (tv, acc) = let
            val (_, addrs) = TupleValue.get tv
        in if offset <= List.length addrs
           then let
               val a = List.nth (addrs, offset-1)
           in f (a, acc) end
           else acc
        end
    in TV.MSet.fold handle_tv acc tvs end

    fun match_dcon f acc (dcon, (clos, dvs, tvs, rvs, arrvs, un)) = let
        fun handle_dv (dv, acc) = let
            val (_, dcon', ao) = DataValue.get dv
        in case CPSDataCon.compare (dcon, dcon')
            of EQUAL =>
               (case ao
                 of NONE => raise Fail "DCON expected to be paired with value"
                  | SOME(a) => f (a, acc))
             | _ => acc
        end
    in DV.MSet.fold handle_dv acc dvs end

    (* Returns all the labels of this value *)
    (* so far the only values with labels are closures *)
    fun labels (clos, dvs, tvs, rvs, arrvs, un) =
        Clo.MSet.fold
            (fn (clo, acc) => let
                 val ((_, lab, _, _, _), _, _) = Clo.get clo
             in Label.Set.add (acc, lab) end)
              Label.Set.empty clos

    fun toString d = let
        fun toString_make toString (x, acc) = (toString x) :: acc
        val strs = fold (toString_make Clo.toString) (toString_make DV.toString)
                        (toString_make TV.toString) (toString_make RV.toString)
                        (toString_make ARRV.toString)
                        (fn (acc) => "unknown" :: acc)
                        [] d
    in String.concat["{", String.concatWith " " strs, "}"] end

  end


structure Value (* :> FULL_VALUE_BASE *) = struct

    structure DV = DataValue
    structure TV = TupleValue
    structure RV = RefValue
    structure ARRV = ArrayValue

    datatype base 
      = CLO of Clo.MSet.set
      | DV of DV.MSet.set
      | TV of TV.MSet.set
      | RV of RV.MSet.set
      | ARRV of ARRV.MSet.set
      | REAL of bool (* the bools are for non-emptiness *)
      | INT of bool
      | WORD of bool
      | CHAR of bool
      | STRING of bool
      | UNIT of bool

    type t = base * (bool ref)

    val size = 4

    fun empty ty = let
        val base = 
            case ty
             of CPSTypes.ConTy (_, tycon) =>
                if CPSTyCon.same (tycon, CPSPrimTy.unitTyc)
                then UNIT true
                else if CPSTyCon.same (tycon, CPSPrimTy.intTyc)
                then INT true
                else if CPSTyCon.same (tycon, CPSPrimTy.realTyc)
                then REAL true
                else if CPSTyCon.same (tycon, CPSPrimTy.wordTyc)
                then WORD true
                else if CPSTyCon.same (tycon, CPSPrimTy.charTyc)
                then CHAR true
                else if CPSTyCon.same (tycon, CPSPrimTy.stringTyc)
                then STRING true
                else if CPSTyCon.same (tycon, CPSPrimTy.arrayTyc)
                then ARRV (ARRV.MSet.mkEmpty size)
                else if CPSTyCon.same (tycon, CPSPrimTy.refTyc)
                then RV (RV.MSet.mkEmpty size)
                else DV (DV.MSet.mkEmpty size)
              | CPSTypes.TupleTy _ => TV (TV.MSet.mkEmpty size)
              | CPSTypes.FunTy _ => CLO (Clo.MSet.mkEmpty size)
    in (base, ref false) end
                       
    fun add_unknown (d as (base, unknown)) =
        (unknown := true; d)
    fun add_clo (d as (base, unknown), clo) =
        (case base
          of CLO clos => Clo.MSet.add (clos, clo)
           | _ => raise Fail "Value.add_clo";
         d)
    fun add_dv (d as (base, unknown), dv) =
        (case base
          of DV dvs => DV.MSet.add (dvs, dv)
           | _ => raise Fail "Value.add_dv"; d)
    fun add_tv (d as (base, unknown), tv) =
        (case base
          of TV tvs => TV.MSet.add (tvs, tv)
           | _ => raise Fail "Value.add_tv"; d)
    fun add_ref (d as (base, unknown), a) =
        (case base
          of RV rvs => RV.MSet.add (rvs, a)
           | _ => raise Fail "Value.add_ref"; 
         d)
    fun add_arr (d as (base, unknown), a) =
        (case base
          of ARRV arrvs => ARRV.MSet.add (arrvs, (IntAbsDom.from 0, a))
           | _ => raise Fail "Value.add_ref"; 
         d)

    fun isEmpty (base, unknown) =
        case base
         of CLO clos => Clo.MSet.isEmpty clos
          | DV dvs => DV.MSet.isEmpty dvs
          | TV tvs => TV.MSet.isEmpty tvs
          | ARRV rvs => ARRV.MSet.isEmpty rvs
          | RV rvs => RV.MSet.isEmpty rvs
          | UNIT nonEmpty => not nonEmpty
          | INT nonEmpty => not nonEmpty
          | REAL nonEmpty => not nonEmpty
          | WORD nonEmpty => not nonEmpty
          | CHAR nonEmpty => not nonEmpty
          | STRING nonEmpty => not nonEmpty

    fun join (d1 as (base1, unknown1) : t, (base2, unknown2) : t) = let
        val base1 =
            (case (base1, base2)
              of (CLO clos1, CLO clos2) => (Clo.MSet.app (fn clo => (Clo.MSet.add (clos1, clo); ())) clos2; CLO clos1)
               | (DV dvs1, DV dvs2) => (DV.MSet.app (fn dv => (DV.MSet.add (dvs1, dv); ())) dvs2; DV dvs1)
               | (TV tvs1, TV tvs2) => (TV.MSet.app (fn tv => (TV.MSet.add (tvs1, tv); ())) tvs2; TV tvs1)
               | (ARRV arrvs1, ARRV arrvs2) => (ARRV.MSet.app (fn arrv => (ARRV.MSet.add (arrvs1, arrv); ())) arrvs2; ARRV arrvs1)
               | (RV rvs1, RV rvs2) => (RV.MSet.app (fn rv => (RV.MSet.add (rvs1, rv); ())) rvs2; RV rvs1)
               | (REAL nonEmpty1, REAL nonEmpty2) => REAL (nonEmpty1 orelse nonEmpty2)
               | (INT nonEmpty1, INT nonEmpty2) => INT (nonEmpty1 orelse nonEmpty2)
               | (WORD nonEmpty1, WORD nonEmpty2) => WORD (nonEmpty1 orelse nonEmpty2)
               | (CHAR nonEmpty1, CHAR nonEmpty2) => CHAR (nonEmpty1 orelse nonEmpty2)
               | (STRING nonEmpty1, STRING nonEmpty2) => STRING (nonEmpty1 orelse nonEmpty2)
               | (UNIT nonEmpty1, UNIT nonEmpty2) => UNIT (nonEmpty1 orelse nonEmpty2)
               | _ => raise Fail "Value.join")
    in 
        unknown1 := ((! unknown1) orelse (! unknown2));
        (base1, unknown1)
    end

    fun copy (d as (base, unknown)) = let
        val base = 
            case base
                of CLO clos => CLO (Clo.MSet.copy clos)
                 | DV dvs => DV (DV.MSet.copy dvs)
                 | TV tvs => TV (TV.MSet.copy tvs)
                 | RV rvs => RV (RV.MSet.copy rvs)
                 | ARRV arrvs => ARRV (ARRV.MSet.copy arrvs)
                 | _ => base
    in (base, ref (! unknown)) end

    (* most of the time we will be subtracting a large value from a small one,
       so we iterate through d1 (small), not d2 (large) *)
    fun difference (d1 as (base1, unknown1), (base2, unknown2)) = let
        val base =
            (case (base1, base2)
              of (CLO clos1, CLO clos2) => let
                  val clos = Clo.MSet.copy clos1
              in Clo.MSet.filter (fn clo => not (Clo.MSet.member (clos2, clo))) clos;
                 CLO clos
              end
               | (DV dvs1, DV dvs2) => let
                   val dvs = DV.MSet.copy dvs1
               in DV.MSet.filter (fn dv => not (DV.MSet.member (dvs2, dv))) dvs;
                  DV dvs
               end
               | (TV tvs1, TV tvs2) => let
                   val tvs = TV.MSet.copy tvs1
               in TV.MSet.filter (fn tv => not (TV.MSet.member (tvs2, tv))) tvs;
                  TV tvs
               end
               | (ARRV arrvs1, ARRV arrvs2) => let
                   val arrvs = ARRV.MSet.copy arrvs1
               in ARRV.MSet.filter (fn arrv => not (ARRV.MSet.member (arrvs2, arrv))) arrvs;
                  ARRV arrvs
               end
               | (RV rvs1, RV rvs2) => let
                   val rvs = RV.MSet.copy rvs1
               in RV.MSet.filter (fn rv => not (RV.MSet.member (rvs2, rv))) rvs;
                  RV rvs
               end
               | (REAL nonEmpty1, REAL nonEmpty2) => REAL (nonEmpty1 andalso not nonEmpty2)
               | (INT nonEmpty1, INT nonEmpty2) => INT (nonEmpty1 andalso not nonEmpty2)
               | (WORD nonEmpty1, WORD nonEmpty2) => WORD (nonEmpty1 andalso not nonEmpty2)
               | (CHAR nonEmpty1, CHAR nonEmpty2) => CHAR (nonEmpty1 andalso not nonEmpty2)
               | (STRING nonEmpty1, STRING nonEmpty2) => STRING (nonEmpty1 andalso not nonEmpty2)
               | (UNIT nonEmpty1, UNIT nonEmpty2) => UNIT (nonEmpty1 andalso not nonEmpty2)
               | _ => raise Fail "Value.difference")
        val unknown = ref ((! unknown1) andalso not (! unknown2))
    in 
       (base, unknown)
    end

    fun fold_clos f acc (base, unknown) =
        case base
         of CLO clos => Clo.MSet.fold f acc clos
          | _ => acc
    fun fold_dvs f acc (base, unknown) = 
        case base
         of DV dvs => DV.MSet.fold f acc dvs
          | _ => acc
    fun fold_tvs f acc (base, unknown) = 
        case base
         of TV tvs => TV.MSet.fold f acc tvs
          | _ => acc
    fun fold_refs f acc (base, unknown) = 
        case base
         of RV rvs => RV.MSet.fold f acc rvs
          | _ => acc
    fun fold_arrs f acc (base, unknown) = 
        case base
         of ARRV arrvs => ARRV.MSet.fold f acc arrvs
          | _ => acc
    fun fold_unknown f acc (base, unknown) =
        if (! unknown) then f acc else acc

    fun fold f_clo f_dv f_tv f_rv f_arr f_unknown acc (base, unknown) = let
        val acc = if (! unknown) then f_unknown acc else acc
        val acc = 
            case base
             of CLO clos => Clo.MSet.fold f_clo acc clos
              | DV dvs => DV.MSet.fold f_dv acc dvs
              | TV tvs => TV.MSet.fold f_tv acc tvs
              | RV rvs => RV.MSet.fold f_rv acc rvs
              | ARRV arrvs => ARRV.MSet.fold f_arr acc arrvs
              | _ => acc
    in acc end

    fun select_offset f acc (offset, (base, unknown)) =
        case base
         of TV tvs => let
             fun handle_tv (tv, acc) = let
                 val (_, addrs) = TupleValue.get tv
             in if offset <= List.length addrs
                then let
                    val a = List.nth (addrs, offset-1)
                in f (a, acc) end
                else acc
             end
         in TV.MSet.fold handle_tv acc tvs end
          | _ => raise Fail "Value.select_offset"

    fun match_dcon f acc (dcon, (base, unknown)) =
        case base
         of DV dvs => let
             fun handle_dv (dv, acc) = let
                 val (_, dcon', ao) = DataValue.get dv
             in case CPSDataCon.compare (dcon, dcon')
                 of EQUAL =>
                    (case ao
                      of NONE => raise Fail "DCON expected to be paired with value"
                       | SOME(a) => f (a, acc))
                  | _ => acc
             end
         in DV.MSet.fold handle_dv acc dvs end
          | _ => raise Fail "Value.match_dcon"

    (* Returns all the labels of this value *)
    (* so far the only values with labels are closures *)
    fun labels (base, unknown) =
        case base
         of CLO clos =>
            Clo.MSet.fold
                (fn (clo, acc) => let
                     val ((_, lab, _, _, _), _, _) = Clo.get clo
                 in Label.Set.add (acc, lab) end)
                Label.Set.empty clos
          | _ => Label.Set.empty

    fun toString (base, unknown) = let
        fun toString_make toString (x, acc) = (toString x) :: acc
        val strs = 
            case base
             of CLO clos => Clo.MSet.fold (toString_make Clo.toString) [] clos
              | DV dvs => DV.MSet.fold (toString_make DV.toString) [] dvs
              | TV tvs => TV.MSet.fold (toString_make TV.toString) [] tvs
              | ARRV arrvs => ARRV.MSet.fold (toString_make ARRV.toString) [] arrvs
              | RV rvs => RV.MSet.fold (toString_make RV.toString) [] rvs
              | UNIT nonEmpty => ["unit"]
              | INT nonEmpty => ["int"]
              | REAL nonEmpty => ["real"]
              | WORD nonEmpty => ["word"]
              | CHAR nonEmpty => ["char"]
              | STRING nonEmpty => ["string"]
    in
        String.concat["{", String.concatWith " " (if ! unknown then "unknown" :: strs else strs), "}"] 
    end

end

structure Value4 :> FULL_VALUE_BASE = struct

    structure DV = DataValue
    structure TV = TupleValue
    structure RV = RefValue
    structure ARRV = ArrayValue

    datatype base 
      = CLO of Clo.Set.set
      | DV of DV.Set.set
      | TV of TV.Set.set
      | ARRV of ARRV.Set.set
      | RV of RV.Set.set
      | REAL of bool (* the bools are for non-emptiness *)
      | INT of bool
      | WORD of bool
      | CHAR of bool
      | STRING of bool
      | UNIT of bool

    type t = base * bool

    fun empty ty = let
        val base = 
            case ty
             of CPSTypes.ConTy (_, tycon) =>
                if CPSTyCon.same (tycon, CPSPrimTy.unitTyc)
                then UNIT true
                else if CPSTyCon.same (tycon, CPSPrimTy.intTyc)
                then INT true
                else if CPSTyCon.same (tycon, CPSPrimTy.realTyc)
                then REAL true
                else if CPSTyCon.same (tycon, CPSPrimTy.wordTyc)
                then WORD true
                else if CPSTyCon.same (tycon, CPSPrimTy.charTyc)
                then CHAR true
                else if CPSTyCon.same (tycon, CPSPrimTy.stringTyc)
                then STRING true
                else if CPSTyCon.same (tycon, CPSPrimTy.arrayTyc)
                then ARRV ARRV.Set.empty
                else if CPSTyCon.same (tycon, CPSPrimTy.refTyc)
                then RV RV.Set.empty
                else DV DV.Set.empty
              | CPSTypes.TupleTy _ => TV TV.Set.empty
              | CPSTypes.FunTy _ => CLO Clo.Set.empty
    in (base, false) end
                       
    fun add_unknown (d as (base, unknown)) =
        (base, true)
    fun add_clo (d as (base, unknown), clo) = let
        val base = 
            (case base
              of CLO clos => CLO (Clo.Set.add (clos, clo))
               | _ => raise Fail "Value.add_clo")
    in (base, unknown) end
    fun add_dv (d as (base, unknown), dv) = let
        val base =
            (case base
              of DV dvs => DV (DV.Set.add (dvs, dv))
               | _ => raise Fail "Value.add_dv")
    in (base, unknown) end
    fun add_tv (d as (base, unknown), tv) = let
        val base = 
            (case base
              of TV tvs => TV (TV.Set.add (tvs, tv))
               | _ => raise Fail "Value.add_tv")
    in (base, unknown) end
    fun add_ref (d as (base, unknown), a) = let
        val base = 
            (case base
              of RV rvs => RV (RV.Set.add (rvs, a))
               | _ => raise Fail "Value.add_ref")
    in (base, unknown) end
    fun add_arr (d as (base, unknown), a) = let
        val base = 
            (case base
              of ARRV arrvs => ARRV (ARRV.Set.add (arrvs, (IntAbsDom.from 0, a)))
               | _ => raise Fail "Value.add_ref")
    in (base, unknown) end

    fun isEmpty (base, unknown) =
        case base
         of CLO clos => Clo.Set.isEmpty clos
          | DV dvs => DV.Set.isEmpty dvs
          | TV tvs => TV.Set.isEmpty tvs
          | ARRV arrvs => ARRV.Set.isEmpty arrvs
          | RV rvs => RV.Set.isEmpty rvs
          | UNIT nonEmpty => not nonEmpty
          | INT nonEmpty => not nonEmpty
          | REAL nonEmpty => not nonEmpty
          | WORD nonEmpty => not nonEmpty
          | CHAR nonEmpty => not nonEmpty
          | STRING nonEmpty => not nonEmpty

    fun join (d1 as (base1, unknown1) : t, (base2, unknown2) : t) = let
        val base1 =
            (case (base1, base2)
              of (CLO clos1, CLO clos2) => CLO (Clo.Set.union (clos1, clos2))
               | (DV dvs1, DV dvs2) => DV (DV.Set.union (dvs1, dvs2))
               | (TV tvs1, TV tvs2) => TV (TV.Set.union (tvs1, tvs2))
               | (ARRV arrvs1, ARRV arrvs2) => ARRV (ARRV.Set.union (arrvs1, arrvs2))
               | (RV rvs1, RV rvs2) => RV (RV.Set.union (rvs1, rvs2))
               | (REAL nonEmpty1, REAL nonEmpty2) => REAL (nonEmpty1 orelse nonEmpty2)
               | (INT nonEmpty1, INT nonEmpty2) => INT (nonEmpty1 orelse nonEmpty2)
               | (WORD nonEmpty1, WORD nonEmpty2) => WORD (nonEmpty1 orelse nonEmpty2)
               | (CHAR nonEmpty1, CHAR nonEmpty2) => CHAR (nonEmpty1 orelse nonEmpty2)
               | (STRING nonEmpty1, STRING nonEmpty2) => STRING (nonEmpty1 orelse nonEmpty2)
               | (UNIT nonEmpty1, UNIT nonEmpty2) => UNIT (nonEmpty1 orelse nonEmpty2)
               | _ => raise Fail "Value.join")
        val unknown1 = (unknown1 orelse unknown2)
    in 
        (base1, unknown1)
    end

    fun copy (d as (base, unknown)) = d

    (* most of the time we will be subtracting a large value from a small one,
       so we iterate through d1 (small), not d2 (large) *)
    fun difference (d1 as (base1, unknown1), (base2, unknown2)) = let
        val base =
            (case (base1, base2)
              of (CLO clos1, CLO clos2) => CLO (Clo.Set.difference (clos1, clos2))
               | (DV dvs1, DV dvs2) => DV (DV.Set.difference (dvs1, dvs2))
               | (TV tvs1, TV tvs2) => TV (TV.Set.difference (tvs1, tvs2))
               | (RV rvs1, RV rvs2) => RV (RV.Set.difference (rvs1, rvs2))
               | (ARRV arrvs1, ARRV arrvs2) => ARRV (ARRV.Set.difference (arrvs1, arrvs2))
               | (REAL nonEmpty1, REAL nonEmpty2) => REAL (nonEmpty1 andalso not nonEmpty2)
               | (INT nonEmpty1, INT nonEmpty2) => INT (nonEmpty1 andalso not nonEmpty2)
               | (WORD nonEmpty1, WORD nonEmpty2) => WORD (nonEmpty1 andalso not nonEmpty2)
               | (CHAR nonEmpty1, CHAR nonEmpty2) => CHAR (nonEmpty1 andalso not nonEmpty2)
               | (STRING nonEmpty1, STRING nonEmpty2) => STRING (nonEmpty1 andalso not nonEmpty2)
               | (UNIT nonEmpty1, UNIT nonEmpty2) => UNIT (nonEmpty1 andalso not nonEmpty2)
               | _ => raise Fail "Value.difference")
        val unknown = (unknown1 andalso not unknown2)
    in (base, unknown) end

    fun fold_clos f acc (base, unknown) =
        case base
         of CLO clos => Clo.Set.foldl f acc clos
          | _ => acc (* raise Fail "Value.fold_clos" *)
    fun fold_dvs f acc (base, unknown) = 
        case base
         of DV dvs => DV.Set.foldl f acc dvs
          | _ => acc (* raise Fail "Value.fold_dvs" *)
    fun fold_tvs f acc (base, unknown) = 
        case base
         of TV tvs => TV.Set.foldl f acc tvs
          | _ => acc (* raise Fail "Value.fold_tvs" *)
    fun fold_refs f acc (base, unknown) = 
        case base
         of RV rvs => RV.Set.foldl f acc rvs
          | _ => acc (* raise Fail "Value.fold_refs" *)
    fun fold_arrs f acc (base, unknown) = 
        case base
         of ARRV arrvs => ARRV.Set.foldl f acc arrvs
          | _ => acc (* raise Fail "Value.fold_refs" *)
    fun fold_unknown f acc (base, unknown) =
        if unknown then f acc else acc

    fun fold f_clo f_dv f_tv f_rv f_arr f_unknown acc (base, unknown) = let
        val acc = if unknown then f_unknown acc else acc
        val acc = 
            case base
             of CLO clos => Clo.Set.foldl f_clo acc clos
              | DV dvs => DV.Set.foldl f_dv acc dvs
              | TV tvs => TV.Set.foldl f_tv acc tvs
              | ARRV arrvs => ARRV.Set.foldl f_arr acc arrvs
              | RV rvs => RV.Set.foldl f_rv acc rvs
              | _ => acc
    in acc end

    fun select_offset f acc (offset, (base, unknown)) =
        case base
         of TV tvs => let
             fun handle_tv (tv, acc) = let
                 val (_, addrs) = TupleValue.get tv
             in if offset <= List.length addrs
                then let
                    val a = List.nth (addrs, offset-1)
                in f (a, acc) end
                else acc
             end
         in TV.Set.foldl handle_tv acc tvs end
          | _ => raise Fail "Value.select_offset"

    fun match_dcon f acc (dcon, (base, unknown)) =
        case base
         of DV dvs => let
             fun handle_dv (dv, acc) = let
                 val (_, dcon', ao) = DataValue.get dv
             in case CPSDataCon.compare (dcon, dcon')
                 of EQUAL =>
                    (case ao
                      of NONE => raise Fail "DCON expected to be paired with value"
                       | SOME(a) => f (a, acc))
                  | _ => acc
             end
         in DV.Set.foldl handle_dv acc dvs end
          | _ => raise Fail "Value.match_dcon"

    (* Returns all the labels of this value *)
    (* so far the only values with labels are closures *)
    fun labels (base, unknown) =
        case base
         of CLO clos =>
            Clo.Set.foldl
                (fn (clo, acc) => let
                     val ((_, lab, _, _, _), _, _) = Clo.get clo
                 in Label.Set.add (acc, lab) end)
                Label.Set.empty clos
          | _ => Label.Set.empty

    fun toString (base, unknown) = let
        fun toString_make toString (x, acc) = (toString x) :: acc
        val strs = 
            case base
             of CLO clos => Clo.Set.foldl (toString_make Clo.toString) [] clos
              | DV dvs => DV.Set.foldl (toString_make DV.toString) [] dvs
              | TV tvs => TV.Set.foldl (toString_make TV.toString) [] tvs
              | ARRV rvs => ARRV.Set.foldl (toString_make ARRV.toString) [] rvs
              | RV rvs => RV.Set.foldl (toString_make RV.toString) [] rvs
              | UNIT nonEmpty => ["unit"]
              | INT nonEmpty => ["int"]
              | REAL nonEmpty => ["real"]
              | WORD nonEmpty => ["word"]
              | CHAR nonEmpty => ["char"]
              | STRING nonEmpty => ["string"]
    in
        String.concat["{", String.concatWith " " (if unknown then "unknown" :: strs else strs), "}"] 
    end

end

                                          
