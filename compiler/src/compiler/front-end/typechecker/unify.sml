(* unify.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Unification with ranked meta-variables (aka "unification variables) as per
 * the lambda-ranking algorithm in
 *
 *      Efficient ML Type Inference Using Ranked Type Varibles
 *      by George Kuan and David MacQueen,
 *      2007 ACM Workshop on ML
 *
 * We modify the above algorithm to support both destructive and nondistructive
 * unification by using an reconstruction list to undo any desctructive unifications.
 *)

structure Unify : sig

  (* destructively unify two types; return true if successful, false otherwise *)
    val unify : Types.ty * Types.ty -> bool

  (* nondestructively check if two types are unifiable. *)
    val unifiable : Types.ty * Types.ty -> bool

  end = struct

    structure MV = MetaVar
    structure Ty = Types
    structure TU = TypeUtil
    structure TC = TypeClass

    fun debugUnify () = Controls.get Ctl.debugUnify
    fun say s = Log.msg("[UN] " :: s)
    val ty2s = TypeUtil.fmt {long=true}

  (* does a meta-variable occur in a type? *)
    fun occursIn (mv, ty) = let
          fun occurs ty = (case TU.prune ty
                 of Ty.ErrorTy => false
                  | (Ty.MetaTy mv') => MV.same(mv, mv')
                  | (Ty.VarTy _) => false
                  | (Ty.ConTy(args, _)) => List.exists occurs args
                  | (Ty.FunTy(ty1, ty2)) => occurs ty1 orelse occurs ty2
                  | (Ty.TupleTy tys) => List.exists occurs tys
                (* end case *))
          in
            occurs ty
          end

  (* unify two types.  If the `reconstruct` flag is `true`, then we track
   * modifications to the meta variables and undo them after the unification.
   *)
    fun unifyRC (ty1, ty2, reconstruct) = let
          val mv_changes = ref []
          fun assignMV (info, newInfo) = (
                if reconstruct
                  then mv_changes := (info, !info) :: !mv_changes
                  else ();
                info := newInfo)
        (* adjust the depth of any non-instantiated meta-variable that is bound
         * deeper than the given depth.
         *)
          fun adjustDepth (ty, d) = let
                fun adjust Ty.ErrorTy = ()
                  | adjust (Ty.MetaTy(Ty.MVar{info, ...})) = (case !info
                       of Ty.UNIV{depth, eq, cls} => if (d < depth)
                            then assignMV(info, Ty.UNIV{depth=d, eq=eq, cls=cls})
                            else ()
                        | Ty.INSTANCE ty => adjust ty
                      (* end case *))
                  | adjust (Ty.VarTy _) = ()
                  | adjust (Ty.ConTy(args, _)) = List.app adjust args
                  | adjust (Ty.FunTy(ty1, ty2)) = (adjust ty1; adjust ty2)
                  | adjust (Ty.TupleTy tys) = List.app adjust tys
                in
                  adjust ty
                end
        (* destructively unify two types *)
          fun unify (ty1, ty2) = (case (TU.prune ty1, TU.prune ty2)
                 of (Ty.ErrorTy, ty2) => true
                  | (ty1, Ty.ErrorTy) => true
                  | (Ty.MetaTy mv1, Ty.MetaTy mv2) =>
                      MetaVar.same(mv1, mv2) orelse unifyMV (mv1, mv2)
                  | (Ty.MetaTy mv1, ty2) => unifyWithMV (ty2, mv1)
                  | (ty1, Ty.MetaTy mv2) => unifyWithMV (ty1, mv2)
                  | (Ty.VarTy tv1, Ty.VarTy tv2) => TyVar.same(tv1, tv2)
                  | (Ty.ConTy(tys1, tyc1), Ty.ConTy(tys2, tyc2)) =>
                      (TyCon.same(tyc1, tyc2)) andalso ListPair.allEq unify (tys1, tys2)
                  | (Ty.FunTy(ty11, ty12), Ty.FunTy(ty21, ty22)) =>
                      unify(ty11, ty21) andalso unify(ty12, ty22)
                  | (Ty.TupleTy tys1, Ty.TupleTy tys2) =>
                      ListPair.allEq unify (tys1, tys2)
                  | _ => (
                      if debugUnify()
                        then say ["** ", ty2s ty1, " !~ ", ty2s ty2, "\n"]
                        else ();
                      false)
                (* end case *))
        (* unify a type with an uninstantiated meta-variable *)
          and unifyWithMV (ty, mv as Ty.MVar{info, ...}) = (
                case !info
                 of Ty.UNIV{depth, eq=true, cls} =>
                      if occursIn(mv, ty) orelse not(Basis.isClass (ty, cls))
                      orelse not(TU.isEqType ty)
                        then false
                        else (
                          adjustDepth(ty, depth);
                          assignMV(info, Ty.INSTANCE ty);
                          true)
                  | Ty.UNIV{depth, cls, ...} =>
                      if occursIn(mv, ty) orelse not(Basis.isClass (ty, cls))
                        then false
                        else (
                          adjustDepth(ty, depth);
                          assignMV(info, Ty.INSTANCE ty);
                          true)
                  | _ => raise Fail "impossible"
                (* end case *))
        (* unify two universal meta variables *)
          and unifyMV (mv1 as Ty.MVar{info=info1, ...}, mv2 as Ty.MVar{info=info2, ...}) =
                let
                val Ty.UNIV{depth=d1, eq=eq1, cls=cls1} = !info1
                val Ty.UNIV{depth=d2, eq=eq2, cls=cls2} = !info2
                val d = Int.min(d1, d2)
                val eq = eq1 orelse eq2
              (* instantiate meta variable "B" with variable "A" *)
                fun update (mvA, infoA, infoB, cls) = (
                      assignMV(infoA, Ty.UNIV{depth=d, eq=eq, cls=cls});
                      assignMV(infoB, Ty.INSTANCE(Ty.MetaTy mvA));
                      true)
                in
                  case (cls1, cls2)
                   of (TC.Int, TC.Real) => false
                    | (TC.Real, TC.Int) => false
                    | (TC.Int, _) => update (mv1, info1, info2, TC.Int)
                    | (_, TC.Int) => update (mv2, info2, info1, TC.Int)
                    | (TC.Real, _) => update (mv1, info1, info2, TC.Real)
                    | (_, TC.Real) => update (mv2, info2, info1, TC.Real)
                    | (TC.Num, _) => update (mv1, info1, info2, TC.Num)
                    | (_, TC.Num) => update (mv2, info2, info1, TC.Num)
                    | (TC.Order, _) => update (mv1, info1, info2, TC.Order)
                    | (_, TC.Order) => update (mv2, info2, info1, TC.Order)
                    | (TC.Any, TC.Any) => update (mv1, info1, info2, TC.Any)
                  (* end case *)
                end
          val ty = unify (ty1, ty2)
          in
            if reconstruct
              then List.app (op :=) (!mv_changes)
              else ();
            ty
          end

    fun unify (ty1, ty2) = let
          val _ = if debugUnify ()
                    then say ["unify (", ty2s ty1, ", ", ty2s ty2, ")\n"]
                    else ()
          val res = unifyRC (ty1, ty2, false)
          in
            if debugUnify ()
              then if res
                then say ["  = ", ty2s ty1, "\n"]
                else say ["  = FAILURE\n"]
              else ();
            res
          end

    fun unifiable (ty1, ty2) = unifyRC (ty1, ty2, true)

  end
