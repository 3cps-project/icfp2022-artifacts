(* basis-binds.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Definitions of the unique identifiers for the Basis.
 *
 * TODO: it would be much better to extract the definitions in this
 * module, plus the bindings in env/basis.sml from a unified list
 * of primitive type, variables, etc.
 *)

structure BasisBinds : sig

  (* predefined type names *)
    val array_ty : BindTree.tycon
    val bool_ty : BindTree.tycon
    val char_ty : BindTree.tycon
    val exn_ty : BindTree.tycon
    val int_ty : BindTree.tycon
    val list_ty : BindTree.tycon
    val option_ty : BindTree.tycon
    val real_ty : BindTree.tycon
    val ref_ty : BindTree.tycon
    val string_ty : BindTree.tycon
    val unit_ty : BindTree.tycon
    val word_ty : BindTree.tycon

  (* operators *)
    val eq_op : BindTree.varid
    val neq_op : BindTree.varid
    val lte_op : BindTree.varid
    val lt_op : BindTree.varid
    val gte_op : BindTree.varid
    val gt_op : BindTree.varid
    val at_op : BindTree.varid
    val hat_op : BindTree.varid
    val plus_op : BindTree.varid
    val minus_op : BindTree.varid
    val times_op : BindTree.varid
    val div_op : BindTree.varid
    val mod_op : BindTree.varid
    val fdiv_op : BindTree.varid
    val neg_op : BindTree.varid
    val deref_op : BindTree.varid
    val assign_op : BindTree.varid

  (* pre-defined data constructors *)
    val boolTrue : BindTree.conid
    val boolFalse : BindTree.conid
    val listCons : BindTree.conid       (* infix `::` *)
    val listNil : BindTree.conid
    val optionNONE : BindTree.conid
    val optionSOME : BindTree.conid

  (* pre-defined exceptions *)
    val exnBind : BindTree.conid
    val exnChr : BindTree.conid
    val exnDiv : BindTree.conid
    val exnDomain : BindTree.conid
    val exnFail : BindTree.conid
    val exnMatch : BindTree.conid
    val exnOverflow : BindTree.conid
    val exnSize : BindTree.conid
    val exnSubscript : BindTree.conid

  (* predefined variables *)
    val acos_fn : BindTree.varid
    val array0_fn : BindTree.varid
    val array_alloc_fn : BindTree.varid
    val array_length_fn : BindTree.varid
    val array_sub_fn : BindTree.varid
    val array_update_fn : BindTree.varid
    val asin_fn : BindTree.varid
    val atan_fn : BindTree.varid
    val atan2_fn : BindTree.varid
    val cos_fn : BindTree.varid
    val exp_fn : BindTree.varid
    val floor_fn : BindTree.varid
    val implode_fn : BindTree.varid
    val ln_fn : BindTree.varid
    val ord_fn : BindTree.varid
    val pow_fn : BindTree.varid
    val print_fn : BindTree.varid
    val real_fn : BindTree.varid
    val ref_fn : BindTree.varid
    val sin_fn : BindTree.varid
    val size_fn : BindTree.varid
    val sqrt_fn : BindTree.varid
    val str_fn : BindTree.varid
    val sub_fn : BindTree.varid
    val tan_fn : BindTree.varid
    val word_andb_fn : BindTree.varid
    val word_fromInt_fn : BindTree.varid
    val word_lshift_fn : BindTree.varid
    val word_orb_fn : BindTree.varid
    val word_notb_fn : BindTree.varid
    val word_rshift_fn : BindTree.varid
    val word_rshiftl_fn : BindTree.varid
    val word_toInt_fn : BindTree.varid
    val word_toIntX_fn : BindTree.varid
    val word_xorb_fn : BindTree.varid

    val env0 : {
            tcMap : BindTree.tycon AtomMap.map,         (* type constructors *)
            vMap : BindTree.val_bind AtomMap.map        (* values *)
          }

  end = struct

    structure BT = BindTree
    structure N = BasisNames

  (* predefined type names *)
    local
      fun new name = BindTree.TycId.new (name, Error.UNKNOWN)
    in
    val array_ty  = new N.array_ty
    val bool_ty   = new N.bool_ty
    val char_ty   = new N.char_ty
    val exn_ty    = new N.exn_ty
    val int_ty    = new N.int_ty
    val list_ty   = new N.list_ty
    val option_ty = new N.option_ty
    val real_ty   = new N.real_ty
    val ref_ty    = new N.ref_ty
    val string_ty = new N.string_ty
    val unit_ty   = new N.unit_ty
    val word_ty   = new N.word_ty
    end (* local *)

  (* operators *)
    local
      fun new name = BindTree.VarId.new (name, Error.UNKNOWN)
    in
    val eq_op           = new N.eq_op
    val neq_op          = new N.neq_op
    val lte_op          = new N.lte_op
    val lt_op           = new N.lt_op
    val gte_op          = new N.gte_op
    val gt_op           = new N.gt_op
    val at_op           = new N.at_op
    val hat_op          = new N.hat_op
    val plus_op         = new N.plus_op
    val minus_op        = new N.minus_op
    val times_op        = new N.times_op
    val div_op          = new N.div_op
    val mod_op          = new N.mod_op
    val fdiv_op         = new N.fdiv_op
    val neg_op          = new N.neg_op
    val deref_op        = new N.deref_op
    val assign_op       = new N.assign_op
    end (* local *)

    local
      fun new name = BindTree.ConId.new (name, Error.UNKNOWN)
    in
  (* pre-defined data constructors *)
    val boolTrue  = new N.boolTrue
    val boolFalse = new N.boolFalse
    val listCons  = new N.listCons
    val listNil   = new N.listNil
    val optionNONE = new N.optionNONE
    val optionSOME = new N.optionSOME
  (* pre-defined exceptions *)
    val exnBind      = new N.exnBind
    val exnChr       = new N.exnChr
    val exnDiv       = new N.exnDiv
    val exnDomain    = new N.exnDomain
    val exnFail      = new N.exnFail
    val exnMatch     = new N.exnMatch
    val exnOverflow  = new N.exnOverflow
    val exnSize      = new N.exnSize
    val exnSubscript = new N.exnSubscript
    end (* local *)

  (* predefined variables *)
    local
      fun new name = BindTree.VarId.new (name, Error.UNKNOWN)
    in
    val acos_fn =               new N.acos_fn
    val array0_fn =             new N.array0_fn
    val array_alloc_fn =        new N.array_alloc_fn
    val array_length_fn =       new N.array_length_fn
    val array_sub_fn =          new N.array_sub_fn
    val array_update_fn =       new N.array_update_fn
    val asin_fn =               new N.asin_fn
    val atan_fn =               new N.atan_fn
    val atan2_fn =              new N.atan2_fn
    val cos_fn =                new N.cos_fn
    val exp_fn =                new N.exp_fn
    val floor_fn =              new N.floor_fn
    val implode_fn =            new N.implode_fn
    val ln_fn =                 new N.ln_fn
    val ord_fn =                new N.ord_fn
    val pow_fn =                new N.pow_fn
    val print_fn =              new N.print_fn
    val real_fn =               new N.real_fn
    val ref_fn =                new N.ref_fn
    val sin_fn =                new N.sin_fn
    val size_fn =               new N.size_fn
    val sqrt_fn =               new N.sqrt_fn
    val str_fn =                new N.str_fn
    val sub_fn =                new N.sub_fn
    val tan_fn =                new N.tan_fn
    val word_andb_fn =          new N.word_andb_fn
    val word_fromInt_fn =       new N.word_fromInt_fn
    val word_lshift_fn =        new N.word_lshift_fn
    val word_orb_fn =           new N.word_orb_fn
    val word_notb_fn =          new N.word_notb_fn
    val word_rshift_fn =        new N.word_rshift_fn
    val word_rshiftl_fn =       new N.word_rshiftl_fn
    val word_toInt_fn =         new N.word_toInt_fn
    val word_toIntX_fn =        new N.word_toIntX_fn
    val word_xorb_fn =          new N.word_xorb_fn
    end (* local *)

  (* the basis environment *)
    val env0 = let
          fun mapFromList xs =
                List.foldl (fn ((x, x'), m) => AtomMap.insert(m, x, x')) AtomMap.empty xs
        (* the predefined type environment *)
          val tcMap = mapFromList [
                  (N.array_ty,          array_ty),
                  (N.bool_ty,           bool_ty),
                  (N.char_ty,           char_ty),
                  (N.exn_ty,            exn_ty),
                  (N.int_ty,            int_ty),
                  (N.list_ty,           list_ty),
                  (N.option_ty,         option_ty),
                  (N.real_ty,           real_ty),
                  (N.string_ty,         string_ty),
                  (N.ref_ty,            ref_ty),
                  (N.unit_ty,           unit_ty),
                  (N.word_ty,           word_ty)
                ]
        (* the predefined value environment *)
          val vMap = mapFromList [
                (* operators *)
                  (N.eq_op,             BT.Var eq_op),
                  (N.neq_op,            BT.Var neq_op),
                  (N.lte_op,            BT.Var lte_op),
                  (N.lt_op,             BT.Var lt_op),
                  (N.gte_op,            BT.Var gte_op),
                  (N.gt_op,             BT.Var gt_op),
                  (N.at_op,             BT.Var at_op),
                  (N.hat_op,            BT.Var hat_op),
                  (N.plus_op,           BT.Var plus_op),
                  (N.minus_op,          BT.Var minus_op),
                  (N.times_op,          BT.Var times_op),
                  (N.div_op,            BT.Var div_op),
                  (N.mod_op,            BT.Var mod_op),
                  (N.fdiv_op,           BT.Var fdiv_op),
                  (N.assign_op,         BT.Var assign_op),
                  (N.listCons,          BT.Con listCons),
                (* predefine data constructors *)
                  (N.boolTrue,          BT.Con boolTrue),
                  (N.boolFalse,         BT.Con boolFalse),
                  (N.listNil,           BT.Con listNil),
                  (* Note: listCons is an operator *)
                  (N.optionNONE,        BT.Con optionNONE),
                  (N.optionSOME,        BT.Con optionSOME),
                (* predefined exception constructors *)
                  (N.exnBind,           BT.Con exnBind),
                  (N.exnChr,            BT.Con exnChr),
                  (N.exnDiv,            BT.Con exnDiv),
                  (N.exnDomain,         BT.Con exnDomain),
                  (N.exnFail,           BT.Con exnFail),
                  (N.exnMatch,          BT.Con exnMatch),
                  (N.exnOverflow,       BT.Con exnOverflow),
                  (N.exnSize,           BT.Con exnSize),
                  (N.exnSubscript,      BT.Con exnSubscript),
                (* unary operators *)
                  (N.neg_op,            BT.Var neg_op),
                  (N.deref_op,          BT.Var deref_op),
                (* predefined variables *)
                  (N.acos_fn,           BT.Var acos_fn),
                  (N.array0_fn,         BT.Var array0_fn),
                  (N.array_alloc_fn,    BT.Var array_alloc_fn),
                  (N.array_length_fn,   BT.Var array_length_fn),
                  (N.array_sub_fn,      BT.Var array_sub_fn),
                  (N.array_update_fn,   BT.Var array_update_fn),
                  (N.asin_fn,           BT.Var asin_fn),
                  (N.atan_fn,           BT.Var atan_fn),
                  (N.atan2_fn,          BT.Var atan2_fn),
                  (N.cos_fn,            BT.Var cos_fn),
                  (N.exp_fn,            BT.Var exp_fn),
                  (N.floor_fn,          BT.Var floor_fn),
                  (N.implode_fn,        BT.Var implode_fn),
                  (N.ln_fn,             BT.Var ln_fn),
                  (N.ord_fn,            BT.Var ord_fn),
                  (N.pow_fn,            BT.Var pow_fn),
                  (N.print_fn,          BT.Var print_fn),
                  (N.real_fn,           BT.Var real_fn),
                  (N.ref_fn,            BT.Var ref_fn),
                  (N.sin_fn,            BT.Var sin_fn),
                  (N.size_fn,           BT.Var size_fn),
                  (N.sqrt_fn,           BT.Var sqrt_fn),
                  (N.str_fn,            BT.Var str_fn),
                  (N.sub_fn,            BT.Var sub_fn),
                  (N.tan_fn,            BT.Var tan_fn),
                  (N.word_andb_fn,      BT.Var word_andb_fn),
                  (N.word_fromInt_fn,   BT.Var word_fromInt_fn),
                  (N.word_lshift_fn,    BT.Var word_lshift_fn),
                  (N.word_orb_fn,       BT.Var word_orb_fn),
                  (N.word_notb_fn,      BT.Var word_notb_fn),
                  (N.word_rshift_fn,    BT.Var word_rshift_fn),
                  (N.word_rshiftl_fn,   BT.Var word_rshiftl_fn),
                  (N.word_toInt_fn,     BT.Var word_toInt_fn),
                  (N.word_toIntX_fn,    BT.Var word_toIntX_fn),
                  (N.word_xorb_fn,      BT.Var word_xorb_fn)
                ]
          in
            {tcMap = tcMap, vMap = vMap}
          end

  end
