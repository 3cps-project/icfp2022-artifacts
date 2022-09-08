(* call-webs.sml
 *
 * The data structure for managing call web information 
 * Both [continuation call / continuation lambda] and [user call / user lambda] data is tracked. *)

structure CallWebs : sig

  type web = {calls : Label.Set.set,
              lams : Label.Set.set,
              unknown_call : bool,
              unknown_lam : bool}
  type t

  (* initializes singleton webs for each given lam and call *)
  val initial : {lams : Label.t list, calls : Label.t list} -> t

  (* indicates that a call site calls an unknown lambda *)
  val add_unknown_lam :  t * {call : Label.t} -> t

  (* indicates that a lambda is called at an unknown call site *)
  val add_unknown_call :  t * {lam : Label.t} -> t

  (* call label, lambda label (user or continuation) *)
  val add : t * {call : Label.t, lambda : Label.t} -> t

  (* All lambdas associated with a call *)
  (* call site label -> lambda label set *)
  val allFuns : t * {call : Label.t} -> Label.Set.set 

  (* All calls associated with a lambda *)
  (* lambda label -> call site label set *)
  val allCalls : t * {lambda : Label.t} -> Label.Set.set 

  (* All call webs *)
  (* unknown tells whether an unknown lambda may appear at one of the call sites or
     whether an unknown call site may call one of the lambdas *)
  val all : t -> web list

  val create_map : t -> web Label.Map.map

end = struct

  structure LS = Label.Set
  structure LM = Label.Map

  type web = {calls : Label.Set.set,
              lams : Label.Set.set,
              unknown_call : bool,
              unknown_lam : bool}
  type t = web list

  val empty_web = {calls = LS.empty,
                   lams = LS.empty,
                   unknown_call = false,
                   unknown_lam = false}

  fun initial {lams, calls} = let
      val initial_webs = []
      val initial_webs =
          List.foldl (fn (lam, acc) =>
                         {calls=LS.empty, lams=LS.singleton lam, 
                          unknown_call=false, unknown_lam=false} :: acc)
                     initial_webs lams
      val initial_webs =
          List.foldl (fn (call, acc) =>
                         {calls=LS.singleton call, lams=LS.empty, 
                          unknown_call=false, unknown_lam=false} :: acc)
                     initial_webs calls
  in initial_webs end

  fun with_calls ({calls, lams, unknown_call, unknown_lam}, calls') =
      {calls=calls', lams=lams, unknown_call=unknown_call, unknown_lam=unknown_lam}
  fun with_lams ({calls, lams, unknown_call, unknown_lam}, lams') =
      {calls=calls, lams=lams', unknown_call=unknown_call, unknown_lam=unknown_lam}
  fun with_unknown_call ({calls, lams, unknown_call, unknown_lam}, unknown_call') =
      {calls=calls, lams=lams, unknown_call=unknown_call', unknown_lam=unknown_lam}
  fun with_unknown_lam ({calls, lams, unknown_call, unknown_lam}, unknown_lam') =
      {calls=calls, lams=lams, unknown_call=unknown_call, unknown_lam=unknown_lam'}

  fun add_unknown_lam (webs : t, {call=call}) = let
      fun search webs =
          case webs
           of [] => [{calls=LS.singleton call, lams=LS.empty, unknown_call=false, unknown_lam=true}]
            | (web : web) :: rst =>
              if LS.member (#calls web, call)
              then let
                  val web = with_unknown_lam (web, true)
              in web :: rst end
              else web :: (search rst)
  in search webs end

  fun add_unknown_call (webs : t, {lam=lam}) = let
      fun search webs =
          case webs
           of [] => [{calls=LS.empty, lams=LS.singleton lam, unknown_call=true, unknown_lam=false}]
            | (web : web) :: rst =>
              if LS.member (#lams web, lam)
              then let
                  val web = with_unknown_call (web, true)
              in web :: rst end
              else web :: (search rst)
  in search webs end

  fun add (lst, {call=call, lambda=lam}) = let
      fun aux (lst, call_web_opt, lam_web_opt, acc) =
          case lst 
           of [] => let
               val acc = List.rev acc
           in case (call_web_opt, lam_web_opt)
               of (SOME call_web, SOME lam_web) => let
                   val calls = LS.union (#calls call_web, #calls lam_web)
                   val lams = LS.union (#lams call_web, #lams lam_web)
                   val unknown_call = (#unknown_call call_web) orelse (#unknown_call lam_web)
                   val unknown_lam = (#unknown_lam call_web) orelse (#unknown_lam lam_web)
                   val web = {calls=calls,
                              lams=lams,
                              unknown_call=unknown_call,
                              unknown_lam=unknown_lam}
               in web :: acc end
                | (NONE, SOME lam_web) => let
                    val web = with_calls (lam_web, LS.add (#calls lam_web, call))
                in web :: acc end
                | (SOME call_web, NONE) => let
                    val web = with_lams (call_web, LS.add (#lams call_web, lam))
                in web :: acc end
                | (NONE, NONE) => let
                    val web = {calls=LS.singleton call,
                               lams=LS.singleton lam,
                               unknown_call=false,
                               unknown_lam=false}
                in web :: acc end
           end
            | web :: rst =>
              case (LS.member (#calls web, call), LS.member (#lams web, lam))
               of (true, true) => lst @ (List.rev acc) (* call, lam is already in the same web *)
                | (false, true) => aux (rst, call_web_opt, SOME web, acc) (* assert: call_set_opt = NONE *)
                | (true, false) => aux (rst, SOME web, lam_web_opt, acc) (* assert: lam_set_opt = NONE *)
                | (false, false) => aux (rst, call_web_opt, lam_web_opt, web :: acc)
  in aux (lst, NONE, NONE, []) end

  fun allFuns (webs : t, {call=call}) =
      case webs
       of [] => LS.empty
        | web :: rst =>
          if LS.member (#calls web, call)
          then #lams web
          else allFuns (rst, {call=call})
                       
  fun allCalls (webs : t, {lambda=lam}) =
      case webs
       of [] => LS.empty
        | web :: rst =>
          if LS.member (#lams web, lam)
          then #calls web
          else allCalls (rst, {lambda=lam})

  fun all (webs) =
      webs

  fun create_map (webs0 : t) = let
      fun create (webs, map) =
          case webs of
              [] => map
            | (web : web) :: rst => let
                val calls = #calls web
                val lams = #lams web
                val map = LS.foldl (fn (call, map) => LM.insert (map, call, web)) map calls
                val map = LS.foldl (fn (lam, map) => LM.insert (map, lam, web)) map lams
            in create (rst, map) end
      val map = create (webs0, LM.empty)
  in map end

end
