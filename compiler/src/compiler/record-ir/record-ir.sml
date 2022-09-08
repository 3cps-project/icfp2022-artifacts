
(* My idea for the record IR *)

structure RecordIR = struct

  type lvar = ...
  type cvar = ...
  type label = ...

  type display = label list
  datatype pop = NO_POP | RELATIVE_POP | UNKNOWN

  datatype func = FUNKNOWN of lvar (* unknown code pointer *)
                | CODEPOINTER of label (* known code pointer *)

  datatype alloc_loc = Heap | Stack of label | Reg

  datatype atom = LIT of Literal.t
                | LVAR of lvar
                | LABEL of label 

  (* Continuation annotations. These help us know what a continuation needs to package *)
  (* There are two types of data continuations can package
     - a code pointer (pointing to the code to execute)
     - a stack pointer (pointing to where the stack needs to be popped to)
     Through program analysis we can sometimes determine these at compile time; 
     these annotations make those determinations explicit. 
     In these cases we can make program optimizations:
     - jump KNOWN_CODE_POINTER
     - sp = sp - offset

     We represent known code pointers by the label of the continuation
     lambda that corresponds and we represent known stack pointers by
     the ordered list of frames that are popped when calling this
     continuation (including the frame of the current binding lambda).
     A frame is represented by the label of the lambda / continuation lambda of the frame.
     This can be used to determine the actual offset later.
  *)
  datatype cont_ann = Heavyweight                  (* package: code pointer and stack pointer *)
                    | StackPointer of label        (* package: no code pointer, just stack pointer *)
                    | CodePointer of (label list)  (* package: just code pointer, no stack pointer *)
                    | Zero of label * (label list) (* package: no code pointer and no stack pointer *) 

  (* Continuation parameters: a continuation variable along with an annotation*)
  type cpar = cvar * cont_ann

  (* Continuations *)
  datatype cont = ContHeavyweight (* code pointer * stack pointer *)
                | ContStackPointer (* no code pointer, just stack pointer *)
                | ContCodePointer (* just code pointer, no stack pointer *)
                | ContZero (* no code pointer or stack pointer *) 

  type apply_ann = {lambdas : label list}
  type throw_ann = {clambdas : label list}

  datatype exp = label * term

  and term = (* Load (y, offset, x, e) means let x = load y + offset in e *)
             Load of (lvar * int * lvar * exp)
             (* let x = allocate (tuple a_1 ... a_n) in e *)
           | Alloc of (label * atom list * lvar * exp)
           | Closures of (lambda list * exp)
           | ContClosures of (clambda list * exp)
           | Apply of (lvar * atom list * cvar list * pop * display * apply_ann)
           | Throw of (cvar * atom list * pop * display * throw_ann)
           | Switch of (dcon * exp) list * (exp option) (* wild, if needed *)
           (* prims *)

  and lambda = {f : lvar, lab : label, xs : lvar list, ks : cpar list,
                (* packaged frames, display-passed frames *)
                packaged : label list, display : label list,
                (* annotations *)
                call_sites : label list}
  and lambdaK = {k : cvar, lab : label, xs : lvar list,
                 (* packaged frames, display-passed frames *)
                 load_from_sp : label list, display : label list,
                 (* annotations *)
                 call_sites : label list}

end
