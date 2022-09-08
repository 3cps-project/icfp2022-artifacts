(* live.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Computes liveness information by looking through all reachable values and continuation values.
 *)

structure CLive : sig

  type t

  val make : CPSInformation.t * CStore.t * CStoreK.t -> t

  val add_a : t * CStore.t * (CAddr.t list) -> unit
  val add_aK : t * CStoreK.t * (CAddrK.t list) -> unit
  val reset : t -> unit

  val glb : t
        -> (LVar.Set.set * CVar.Set.set * CEnv.t * CEnvK.t) option
           * (CValue.t list) option * (CValueK.t list) option
        -> CBinding.Set.set list

  val gld : t
        -> (LVar.Set.set * CVar.Set.set * CEnv.t * CEnvK.t) option
           * (CValue.t list) option * (CValueK.t list) option
        -> CValue.Set.set list

end = struct

  structure C = CPS
  structure CU = CPSUtil
  structure LVS = LVar.Set
  structure CVS = CVar.Set

  structure PInfo = CPSInformation

  structure AS = CAddr.Set
  structure AKS = CAddrK.Set
  structure AT = CAddr.Tbl
  structure AKT = CAddrK.Tbl
  structure BS = CBinding.Set
  structure VS = CValue.Set
  structure VKS = CValueK.Set
  structure V = CValue
  structure VK = CValueK
  structure VB = CValueBase
  structure VKB = CValueKBase

  type t = {pinfo : PInfo.t,
            ref_store : CStore.t ref,
            ref_storeK : CStoreK.t ref,
            a_b : BS.set AT.hash_table,
            a_ld : VS.set AT.hash_table,
            aK_b : BS.set AKT.hash_table,
            aK_ld : VS.set AKT.hash_table}

  exception LiveFail

  fun do_liveness () = Controls.get Ctl.checkAnalysisExtentResults

  (* concrete live bindings computation *)
  structure CLiveBindingsWL : sig

    val lb_a : t -> CAddr.t -> BS.set
    val lb_aK : t -> CAddrK.t -> BS.set

  end = struct

    val empty = ([], AS.empty, [], AKS.empty, BS.empty)

    fun add_a_wl (memo : t as {a_b, ...}, a, (wl, seen, wl_K, seen_K, lb)) =
        if AS.member(seen, a)
        then (wl, seen, wl_K, seen_K, lb)
        else case AT.find a_b a
              of NONE => (a::wl, AS.add (seen, a), wl_K, seen_K, lb)
              | SOME bs => (wl, AS.add (seen, a), wl_K, seen_K, BS.union (lb, bs))

    fun add_aK_wl (memo : t as {aK_b, ...}, aK, (wl, seen, wl_K, seen_K, lb)) =
        if AKS.member (seen_K, aK)
        then (wl, seen, wl_K, seen_K, lb)
        else case AKT.find aK_b aK
              of NONE => (wl, seen, aK::wl_K, AKS.add (seen_K, aK), lb)
              | SOME bs => (wl, seen, wl_K, AKS.add (seen_K, aK), BS.union (lb, bs))

    fun add_lv_wl (memo : t, x, env, (wl, seen, wl_K, seen_K, lb)) = let
        val a = CEnv.lookup (env, x)
    in add_a_wl (memo, a, (wl, seen, wl_K, seen_K, BS.add (lb, (x, a)))) end

    fun add_cv_wl (memo : t, k, envK, acc) = let
        val aK = CEnvK.lookup (envK, k)
    in add_aK_wl (memo, aK, acc) end

    fun add_vars_wl (memo : t as {pinfo, ...}, uvars, cvars, env, envK, acc) = let
        val acc = LVS.foldl (fn (x, acc) => add_lv_wl (memo, x, env, acc)) acc uvars
        val acc = CVS.foldl (fn (k, acc) => add_cv_wl (memo, k, envK, acc)) acc cvars
    in acc end

    fun add_value_wl (memo : t as {pinfo, ...}, d, acc) =
        case V.base d
         of VB.UNIT => acc
          | VB.INT _ => acc
          | VB.WORD _ => acc
          | VB.FLOAT _ => acc
          | VB.CHAR _ => acc
          | VB.STRING _ => acc
          | VB.TUPLE (_, addrs) => List.foldl (fn (a, acc) => add_a_wl (memo, a, acc)) acc addrs
          | VB.DATA (_, dcon, SOME a) => add_a_wl (memo, a, acc)
          | VB.DATA (_, dcon, NONE) => acc
          | VB.REF a => add_a_wl (memo, a, acc)
          | VB.ARRAY addrs => List.foldl (fn (a, acc) => add_a_wl (memo, a, acc)) acc addrs
          | VB.CLO (lam, env, _) => let
              val fv_lv = PInfo.fv_lam_lv pinfo (CU.labelOfLambda lam)
          in add_vars_wl (memo, fv_lv, CVS.empty, env, CEnvK.empty, acc) end

    fun add_valueK_wl (memo : t as {pinfo, ...}, dK, acc) =
        case VK.base dK
         of VKB.HALT => acc
          | VKB.CLOK (lamK, env, envK, _) => let
              val fv_lv = PInfo.fv_lamK_lv pinfo (CU.labelOfCLambda lamK)
              val fv_cv = PInfo.fv_lamK_cv pinfo (CU.labelOfCLambda lamK)
          in add_vars_wl (memo, fv_lv, fv_cv, env, envK, acc) end

    fun glb_wl (memo : t as {ref_store, ref_storeK, ...}, acc) = let
        fun loc (wl, seen, wl_K, seen_K, lb) =
            (case wl
              of [] =>
                 (case wl_K
                   of [] => lb
                    | aK::rst_K => let
                        val dK = CStoreK.lookup (! ref_storeK, aK)
                    in loc (add_valueK_wl (memo, dK, ([], seen, rst_K, seen_K, lb))) end)
               | a::rst => let
                   val d = CStore.lookup (! ref_store, a)
               in loc (add_value_wl (memo, d, (rst, seen, wl_K, seen_K, lb))) end)
    in loc acc end

    fun lb_a memo a = 
        glb_wl (memo, add_a_wl (memo, a, empty))

    fun lb_aK memo aK =
        glb_wl (memo, add_aK_wl (memo, aK, empty))

  end


  (* concrete live data computation *)
  structure CLiveDataWL : sig

    val ld_a : t -> CAddr.t -> VS.set
    val ld_aK : t -> CAddrK.t -> VS.set

  end = struct

    val empty = ([], AS.empty, [], AKS.empty, VS.empty)

    fun add_a_wl (memo : t as {a_ld, ref_store, ...}, a, (wl, seen, wl_K, seen_K, ld)) =
        if AS.member(seen, a)
        then (wl, seen, wl_K, seen_K, ld)
        else case AT.find a_ld a
              of NONE => (a::wl, AS.add (seen, a), wl_K, seen_K, VS.add (ld, CStore.lookup (! ref_store, a)))
              | SOME ld' => (wl, AS.add (seen, a), wl_K, seen_K, VS.add (VS.union (ld, ld'), CStore.lookup (! ref_store, a)))

    fun add_aK_wl (memo : t as {aK_ld, ...}, aK, (wl, seen, wl_K, seen_K, ld)) =
        if AKS.member (seen_K, aK)
        then (wl, seen, wl_K, seen_K, ld)
        else case AKT.find aK_ld aK
              of NONE => (wl, seen, aK::wl_K, AKS.add (seen_K, aK), ld)
               | SOME ld' => (wl, seen, wl_K, AKS.add (seen_K, aK), VS.union (ld, ld'))

    fun add_lv_wl (memo, x, env, acc) = let
        val a = CEnv.lookup (env, x)
    in add_a_wl (memo, a, acc) end

    fun add_cv_wl (memo, k, envK, acc) = let
        val aK = CEnvK.lookup (envK, k)
    in add_aK_wl (memo, aK, acc) end

    fun add_vars_wl (memo, uvars, cvars, env, envK, acc) = let
        val acc = LVS.foldl (fn (x, acc) => add_lv_wl (memo, x, env, acc)) acc uvars
        val acc = CVS.foldl (fn (k, acc) => add_cv_wl (memo, k, envK, acc)) acc cvars
    in acc end

    fun add_value_wl (memo : t as {pinfo, ...}, d, acc) =
        case V.base d
         of VB.UNIT => acc
          | VB.INT _ => acc
          | VB.WORD _ => acc
          | VB.FLOAT _ => acc
          | VB.CHAR _ => acc
          | VB.STRING _ => acc
          | VB.TUPLE (_, addrs) => List.foldl (fn (a, acc) => add_a_wl (memo, a, acc)) acc addrs
          | VB.DATA (_, dcon, SOME a) => add_a_wl (memo, a, acc)
          | VB.DATA (_, dcon, NONE) => acc
          | VB.REF a => add_a_wl (memo, a, acc)
          | VB.ARRAY addrs => List.foldl (fn (a, acc) => add_a_wl (memo, a, acc)) acc addrs
          | VB.CLO (lam, env, _) => let
              val fv_lv = PInfo.fv_lam_lv pinfo (CU.labelOfLambda lam)
          in add_vars_wl (memo, fv_lv, CVS.empty, env, CEnvK.empty, acc) end

    fun add_valueK_wl (memo : t as {pinfo, ...}, dK, acc) =
        case VK.base dK
         of VKB.HALT => acc
          | VKB.CLOK (lamK, env, envK, _) => let
              val fv_lv = PInfo.fv_lamK_lv pinfo (CU.labelOfCLambda lamK)
              val fv_cv = PInfo.fv_lamK_cv pinfo (CU.labelOfCLambda lamK)
          in add_vars_wl (memo, fv_lv, fv_cv, env, envK, acc) end

    fun gld_wl (memo : t as {ref_store, ref_storeK, ...}, acc) = let
        fun loc (wl, seen, wl_K, seen_K, ld) =
            (case wl
              of [] =>
                 (case wl_K
                   of [] => ld
                    | aK::rst_K => let
                        val dK = CStoreK.lookup (! ref_storeK, aK)
                    in
                        loc (add_valueK_wl (memo, dK, ([], seen, rst_K, seen_K, ld)))
                    end)
               | a::rst => let
                   val d = CStore.lookup(! ref_store, a)
               in loc (add_value_wl (memo, d, (rst, seen, wl_K, seen_K, ld))) end)
    in
        loc acc
    end

    fun ld_a memo a =
        gld_wl (memo, add_a_wl (memo, a, empty))

    fun ld_aK memo aK =
        gld_wl (memo, add_aK_wl (memo, aK, empty))

  end

  fun make (pinfo, store, storeK) : t = let
      val a_b = AT.mkTable(10000, LiveFail)
      val a_ld = AT.mkTable(10000, LiveFail)
      val aK_b = AKT.mkTable(10000, LiveFail)
      val aK_ld = AKT.mkTable(10000, LiveFail)
      val memo = {pinfo=pinfo,ref_store=ref store,ref_storeK=ref storeK,a_b=a_b,a_ld=a_ld,aK_b=aK_b,aK_ld=aK_ld}
  (* DP
      val _ =
          CStore.appi (fn (a, _) => let
                           val bs = CLiveBindingsWL.lb_a memo a
                       in AT.insert a_b (a, bs) end)
                      store
      val _ =
          CStore.appi (fn (a, _) => let
                           val lds = CLiveDataWL.ld_a memo a
                       in AT.insert a_ld (a, lds) end)
                      store
      val _ =
          CStoreK.appi (fn (aK, _) => let
                            val bs = CLiveBindingsWL.lb_aK memo aK
                        in AKT.insert aK_b (aK, bs) end)
                       storeK
      val _ =
          CStoreK.appi (fn (aK, _) => let
                            val lds = CLiveDataWL.ld_aK memo aK
                        in AKT.insert aK_ld (aK, lds) end)
                      storeK
    *)
  in memo end

  fun add_a (memo : t as {pinfo,ref_store,ref_storeK,a_b,a_ld,aK_b,aK_ld}, store', a_lst) =
      (ref_store := store';
       ()
      (* DP
       List.app (fn a => let
                     val bs = CLiveBindingsWL.lb_a memo a
                 in AT.insert a_b (a, bs) end)
                a_lst;
       List.app (fn a => let
                     val ld = CLiveDataWL.ld_a memo a
                 in AT.insert a_ld (a, ld) end)
                a_lst
      *))

  fun add_aK (memo : t as {pinfo,ref_store,ref_storeK,a_b,a_ld,aK_b,aK_ld}, storeK', aK_lst) =
      (ref_storeK := storeK';
       ()
      (* DP
       List.app (fn aK => let
                     val bs = CLiveBindingsWL.lb_aK memo aK
                 in AKT.insert aK_b (aK, bs) end)
                aK_lst;
       List.app (fn aK => let
                     val ld = CLiveDataWL.ld_aK memo aK
                 in AKT.insert aK_ld (aK, ld) end)
                aK_lst
      *))

  fun reset (memo : t as {a_b, a_ld, aK_b, aK_ld, ...}) =
      (AT.clear a_b; AT.clear a_ld; AKT.clear aK_b; AKT.clear aK_ld)

  fun aux_live_b_a (memo : t as {a_b, ...}, a, (seen, seen_K, bs)) =
      if AS.member (seen, a)
      then (seen, seen_K, bs)
      else let
          val bs' = (case AT.find a_b a of NONE => let val bs' = CLiveBindingsWL.lb_a memo a in AT.insert a_b (a, bs'); bs' end | SOME bs' => bs')
      in (AS.add (seen, a), seen_K, bs' :: bs) end

  and aux_live_b_aK (memo : t as {aK_b, ...}, aK, (seen, seen_K, bs)) =
      if AKS.member (seen_K, aK)
      then (seen, seen_K, bs)
      else let
          val bs' = (case AKT.find aK_b aK of NONE => let val bs' = CLiveBindingsWL.lb_aK memo aK in AKT.insert aK_b (aK, bs'); bs' end | SOME bs' => bs')
      in (seen, AKS.add (seen_K, aK), bs' :: bs) end

  and aux_live_b_vars (memo, lvars, cvars, env, envK, acc) = let
      val acc =
          LVS.foldl (fn (x, (seen, seen_K, bs)) => let
                              val a = CEnv.lookup (env, x)
                          in aux_live_b_a (memo, a, (seen, seen_K, BS.singleton (x, a) :: bs)) end)
                         acc lvars
      val acc =
          CVS.foldl (fn (k, acc) => let
                              val aK = CEnvK.lookup (envK, k)
                          in aux_live_b_aK (memo, aK, acc) end)
                         acc cvars
  in acc end

  and aux_live_b_clo (memo : t as {pinfo, ...}, (lam, env, _), acc) = let
      val fv_lv = PInfo.fv_lam_lv pinfo (CU.labelOfLambda lam)
      in
        aux_live_b_vars (memo, fv_lv, CVS.empty, env, CEnvK.empty, acc)
      end

  and aux_live_b_valueK (memo : t as {pinfo, ...}, dK, acc) =
        case VK.base dK
         of VKB.HALT => acc
          | VKB.CLOK (lamK, env, envK, _) => let
              val fv_lv = PInfo.fv_lamK_lv pinfo (CU.labelOfCLambda lamK)
              val fv_cv = PInfo.fv_lamK_cv pinfo (CU.labelOfCLambda lamK)
          in aux_live_b_vars (memo, fv_lv, fv_cv, env, envK, acc) end

  and aux_live_b_value (memo, d, acc) =
      case V.base d
       of VB.UNIT => acc
        | VB.INT _ => acc
        | VB.WORD _ => acc
        | VB.FLOAT _ => acc
        | VB.CHAR _ => acc
        | VB.STRING _ => acc
        | VB.TUPLE (_, addrs) => List.foldl (fn (a, acc) => aux_live_b_a (memo, a, acc)) acc addrs
        | VB.DATA (_, dcon, SOME a) => aux_live_b_a (memo, a, acc)
        | VB.DATA (_, dcon, NONE) => acc
        | VB.REF a => aux_live_b_a (memo, a, acc)
        | VB.ARRAY addrs => List.foldl (fn (a, acc) => aux_live_b_a (memo, a, acc)) acc addrs
        | VB.CLO clo => aux_live_b_clo (memo, clo, acc)

  fun glb memo (vars_opt, values_opt, valuesK_opt) =
      if do_liveness ()
      then []
      else let
          val acc = (AS.empty, AKS.empty, [])
          val acc = case vars_opt
                     of SOME (uvars, cvars, env, envK) => aux_live_b_vars (memo, uvars, cvars, env, envK, acc)
                      | NONE => acc
          val acc = case values_opt
                     of SOME ds => List.foldl (fn (d, acc) => aux_live_b_value (memo, d, acc)) acc ds
                      | NONE => acc
          val acc = case valuesK_opt
                     of SOME dKs => List.foldl (fn (dK, acc) => aux_live_b_valueK (memo, dK, acc)) acc dKs
                      | NONE => acc
      in #3 acc end

  fun aux_live_ld_a (memo : t as {a_ld, ...}, a, (seen, seen_K, ld)) =
      if AS.member (seen, a)
      then (seen, seen_K, ld)
      else let
          val ld' = (case AT.find a_ld a of NONE => let val ld' = CLiveDataWL.ld_a memo a in AT.insert a_ld (a, ld'); ld' end | SOME ld' => ld')
      in (AS.add (seen, a), seen_K, ld' :: ld) end

  and aux_live_ld_aK (memo : t as {aK_ld, ...}, aK, (seen, seen_K, ld)) =
      if AKS.member (seen_K, aK)
      then (seen, seen_K, ld)
      else let
          val ld' = (case AKT.find aK_ld aK of NONE => let val ld' = CLiveDataWL.ld_aK memo aK in AKT.insert aK_ld (aK, ld'); ld' end | SOME ld' => ld')
      in (seen, AKS.add (seen_K, aK), ld' :: ld) end

  and aux_live_ld_vars (memo, lvars, cvars, env, envK, acc) = let
      val acc = LVS.foldl (fn (x, acc) => let
                                     val a = CEnv.lookup (env, x)
                                in aux_live_ld_a (memo, a, acc) end)
                               acc lvars
      val acc = CVS.foldl (fn (k, acc) => let
                                     val aK = CEnvK.lookup (envK, k)
                                in aux_live_ld_aK (memo, aK, acc) end)
                               acc cvars
  in acc end

  and aux_live_ld_clo (memo : t as {pinfo, ...}, (lam, env, _), acc) = let
      val fv_lv = PInfo.fv_lam_lv pinfo (CU.labelOfLambda lam)
      in
        aux_live_ld_vars (memo, fv_lv, CVS.empty, env, CEnvK.empty, acc)
      end

  and aux_live_ld_valueK (memo : t as {pinfo, ...}, dK, acc) =
        case VK.base dK
         of VKB.HALT => acc
          | VKB.CLOK (lamK, env, envK, _) => let
              val fv_lv = PInfo.fv_lamK_lv pinfo (CU.labelOfCLambda lamK)
              val fv_cv = PInfo.fv_lamK_cv pinfo (CU.labelOfCLambda lamK)
          in aux_live_ld_vars (memo, fv_lv, fv_cv, env, envK, acc) end

  and aux_live_ld_value (memo, d, acc) =
      case V.base d
       of VB.UNIT => acc
        | VB.INT _ => acc
        | VB.WORD _ => acc
        | VB.FLOAT _ => acc
        | VB.CHAR _ => acc
        | VB.STRING _ => acc
        | VB.TUPLE (_, addrs) => List.foldl (fn (a, acc) => aux_live_ld_a (memo, a, acc)) acc addrs
        | VB.DATA (_, dcon, SOME a) => aux_live_ld_a (memo, a, acc)
        | VB.DATA (_, dcon, NONE) => acc
        | VB.REF a => aux_live_ld_a (memo, a, acc)
        | VB.ARRAY addrs => List.foldl (fn (a, acc) => aux_live_ld_a (memo, a, acc)) acc addrs
        | VB.CLO clo => aux_live_ld_clo (memo, clo, acc)

  fun add_initial_values ((seen, seen_K, ld), ds) = (seen, seen_K, (VS.addList (VS.empty, ds))::ld)

  fun gld memo (vars_opt, values_opt, valuesK_opt) =
      if do_liveness ()
      then []
      else let
          val acc = (AS.empty, AKS.empty, [])
          val acc = case vars_opt
                     of SOME (uvars, cvars, env, envK) => aux_live_ld_vars (memo, uvars, cvars, env, envK, acc)
                      | NONE => acc
          val acc = case values_opt
                     of SOME ds => List.foldl (fn (d, acc) => aux_live_ld_value (memo, d, acc)) (add_initial_values (acc, ds)) ds
                      | NONE => acc
          val acc = case valuesK_opt
                     of SOME dKs => List.foldl (fn (dK, acc) => aux_live_ld_valueK (memo, dK, acc)) acc dKs
                      | NONE => acc
      in #3 acc end

end
