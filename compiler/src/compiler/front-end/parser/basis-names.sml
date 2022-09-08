(* basis-names.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Names of identifiers and operators bound in the MinML basis.
 *)

structure BasisNames =
  struct

  (* predefined type names *)
    val array_ty =      Atom.atom "array"
    val bool_ty =       Atom.atom "bool"
    val char_ty =       Atom.atom "char"
    val exn_ty =        Atom.atom "exn"
    val int_ty =        Atom.atom "int"
    val list_ty =       Atom.atom "list"
    val option_ty =     Atom.atom "option"
    val real_ty =       Atom.atom "real"
    val ref_ty =        Atom.atom "ref"
    val string_ty =     Atom.atom "string"
    val unit_ty =       Atom.atom "unit"
    val word_ty =       Atom.atom "word"

  (* operators *)
    val eq_op =         Atom.atom "="
    val neq_op =        Atom.atom "<>"
    val lte_op =        Atom.atom "<="
    val lt_op =         Atom.atom "<"
    val gte_op =        Atom.atom ">="
    val gt_op =         Atom.atom ">"
    val at_op =         Atom.atom "@"
    val hat_op =        Atom.atom "^"
    val plus_op =       Atom.atom "+"
    val minus_op =      Atom.atom "-"
    val times_op =      Atom.atom "*"
    val div_op =        Atom.atom "div"
    val mod_op =        Atom.atom "mod"
    val fdiv_op =       Atom.atom "/"
    val neg_op =        Atom.atom "~"
    val deref_op =      Atom.atom "!"
    val assign_op =     Atom.atom ":="

  (* pre-defined data constructors *)
    val boolTrue =      Atom.atom "true"
    val boolFalse =     Atom.atom "false"
    val listCons =      Atom.atom "::"
    val listNil =       Atom.atom "nil"
    val optionNONE =    Atom.atom "NONE"
    val optionSOME =    Atom.atom "SOME"

  (* pre-defined exceptions *)
    val exnBind =       Atom.atom "Bind"
    val exnChr =        Atom.atom "Chr"
    val exnDiv =        Atom.atom "Div"
    val exnDomain =     Atom.atom "Domain"
    val exnFail =       Atom.atom "Fail"
    val exnMatch =      Atom.atom "Match"
    val exnOverflow =   Atom.atom "Overflow"
    val exnSize =       Atom.atom "Size"
    val exnSubscript =  Atom.atom "Subscript"

  (* predefined variables *)
    val acos_fn =               Atom.atom "acos"
    val array0_fn =             Atom.atom "array0"
    val array_alloc_fn =        Atom.atom "array_alloc"
    val array_length_fn =       Atom.atom "array_length"
    val array_sub_fn =          Atom.atom "array_sub"
    val array_update_fn =       Atom.atom "array_update"
    val asin_fn =               Atom.atom "asin"
    val atan_fn =               Atom.atom "atan"
    val atan2_fn =              Atom.atom "atan2"
    val cos_fn =                Atom.atom "cos"
    val exp_fn =                Atom.atom "exp"
    val floor_fn =              Atom.atom "floor"
    val implode_fn =            Atom.atom "implode"
    val ln_fn =                 Atom.atom "ln"
    val ord_fn =                Atom.atom "ord"
    val pow_fn =                Atom.atom "pow"
    val print_fn =              Atom.atom "print"
    val real_fn =               real_ty
    val ref_fn =                Atom.atom "ref"
    val sin_fn =                Atom.atom "sin"
    val size_fn =               Atom.atom "size"
    val sqrt_fn =               Atom.atom "sqrt"
    val str_fn =                Atom.atom "str"
    val sub_fn =                Atom.atom "string_sub"
    val tan_fn =                Atom.atom "tan"
    val word_andb_fn =          Atom.atom "word_andb"
    val word_fromInt_fn =       Atom.atom "word_fromInt"
    val word_lshift_fn =        Atom.atom "word_lshift"
    val word_orb_fn =           Atom.atom "word_orb"
    val word_notb_fn =          Atom.atom "word_notb"
    val word_rshift_fn =        Atom.atom "word_rshift"
    val word_rshiftl_fn =       Atom.atom "word_rshiftl"
    val word_toInt_fn =         Atom.atom "word_toInt"
    val word_toIntX_fn =        Atom.atom "word_toIntX"
    val word_xorb_fn =          Atom.atom "word_xorb"

  end
