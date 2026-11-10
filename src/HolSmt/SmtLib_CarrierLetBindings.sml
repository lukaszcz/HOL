(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_CarrierLetBindings :> SmtLib_CarrierLetBindings =
struct
  type 'term pabs_operations =
    {dest_abs : 'term -> 'term * 'term,
     dest_uncurry : 'term -> 'term,
     mk_pair : 'term * 'term -> 'term,
     is_syntax_error : exn -> bool}

  fun dest_pabs (operations : 'term pabs_operations) term =
    (#dest_abs operations) term handle failure =>
      if (#is_syntax_error operations) failure then
        let
          val argument = (#dest_uncurry operations) term
          val (left,body) = dest_pabs operations argument
          val (right,body) = dest_pabs operations body
        in ((#mk_pair operations) (left,right),body) end
      else raise failure

  fun strip_pabs (operations : 'term pabs_operations) term =
    let
      val first = SOME (dest_pabs operations term) handle failure =>
        if (#is_syntax_error operations) failure then NONE
        else raise failure
    in case first of
        NONE => ([],term)
      | SOME (variable,body) =>
          let val (variables,body) = strip_pabs operations body
          in (variable :: variables,body) end
    end

  type 'term operations =
    {dest_abs : 'term -> 'term * 'term,
     dest_let : 'term -> 'term * 'term,
     dest_plet : 'term -> 'term * 'term * 'term,
     strip_pabs : 'term -> 'term list * 'term,
     list_mk_comb : 'term * 'term list -> 'term,
     is_let : 'term -> bool,
     is_syntax_error : exn -> bool,
     not_a_let : unit -> exn}

  fun dest_anylet (operations : 'term operations) term =
    let
      fun fallback action next = action () handle failure =>
        if (#is_syntax_error operations) failure then next ()
        else raise failure
      fun zip [] [] = []
        | zip (left :: lefts) (right :: rights) =
            (left,right) :: zip lefts rights
        | zip _ _ = raise (#not_a_let operations) ()
      fun simple current =
        let val (function,value) = (#dest_let operations) current
            val (variable,body) = (#dest_abs operations) function
        in ([(variable,value)],body) end
      fun paired current =
        let val (variable,value,body) = (#dest_plet operations) current
        in ([(variable,value)],body) end
      fun parallel current values =
        let val (function,value) = (#dest_let operations) current
        in if (#is_let operations) function then
            parallel function (value :: values)
          else
            let val (variables,body) = (#strip_pabs operations) function
            in (zip variables (value :: values),body) end
        end
      fun fixup (variable,value) =
        let val (variables,body) = (#strip_pabs operations) value
        in ((#list_mk_comb operations) (variable,variables),body) end
    in
      (let
         val (bindings,body) = fallback (fn () => simple term)
           (fn () => fallback (fn () => paired term)
             (fn () => parallel term []))
       in (List.map fixup bindings,body) end)
      handle failure =>
        if (#is_syntax_error operations) failure then
          raise (#not_a_let operations) ()
        else raise failure
    end
end
