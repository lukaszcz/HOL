structure SmtLib_GraphCarrierBeta :> SmtLib_GraphCarrierBeta =
struct
  structure Q = SmtLib_GraphQueryAnalysis

  fun compare_key ((ls,ln),(rs,rn)) =
    case Int.compare (ls,rs) of
      EQUAL => Int.compare (ln,rn)
    | order => order

  fun reduce (context : Q.outbound_context) input =
    let
      val reduced = ref (Redblackmap.mkDict compare_key)
      fun same left right = (#same context) (left,right)
      fun member variable variables = List.exists (same variable) variables
      fun checked current = (ignore ((#key context) current);current)
      fun remember table index current =
        let
          val _ = checked current
          val _ = table := Redblackmap.insert (!table,index,current)
        in current end

      (* Each substitution owns its memo: the fixed target and replacement
         form its environment. A capture-avoiding rename gets a separate
         memo, so results cannot cross substitution environments. *)
      fun substitute target replacement body =
        let
          val _ = checked target
          val _ = checked replacement
          val replacement_free = (#free_variables context) replacement
          val substituted = ref (Redblackmap.mkDict compare_key)
          fun visit current =
            let val index = (#key context) current in
              case Redblackmap.peek (!substituted,index) of
                SOME result => checked result
              | NONE =>
                  let
                    val _ = (#step context) ()
                    val result =
                      if not (member target
                          ((#free_variables context) current)) then current
                      else case (#view context) current of
                          Q.VariableView _ =>
                            if same current target then replacement
                            else current
                        | Q.ConstantView _ => current
                        | Q.ApplicationView (function,argument) =>
                            let
                              val function' = visit function
                              val argument' = visit argument
                            in
                              if (#key context) function =
                                    (#key context) function' andalso
                                  (#key context) argument =
                                    (#key context) argument' then current
                              else (#mk_comb context) (function',argument')
                            end
                        | Q.AbstractionView (binder,inner) =>
                            if same binder target then current
                            else
                              let
                                val (binder',inner') =
                                  if member binder replacement_free then
                                    let
                                      val fresh = (#genvar context)
                                        ((#type_of context) binder)
                                    in
                                      (fresh,substitute binder fresh inner)
                                    end
                                  else (binder,inner)
                                val result = visit inner'
                              in
                                if (#key context) binder =
                                      (#key context) binder' andalso
                                    (#key context) inner =
                                      (#key context) result then current
                                else (#list_mk_abs context)
                                  ([binder'],result)
                              end
                  in remember substituted index result end
            end
        in visit body end

      fun spine current =
        let val index = (#key context) current in
          case Redblackmap.peek (!reduced,index) of
            SOME result => checked result
          | NONE =>
              let
                val _ = (#step context) ()
                val result = case (#view context) current of
                    Q.ApplicationView (function,argument) =>
                      (case (#view context) (spine function) of
                         Q.AbstractionView (binder,body) =>
                           substitute binder argument body
                       | _ => current)
                  | _ => current
              in remember reduced index result end
        end
    in spine input end
end
