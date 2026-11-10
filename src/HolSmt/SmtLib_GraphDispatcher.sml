structure SmtLib_GraphDispatcher :> SmtLib_GraphDispatcher =
struct
  structure Q = SmtLib_GraphQueryAnalysis
  structure S = SmtLib_GraphCarrierStore
  structure F = SmtLib_OutputFragments

  type root =
    {occurrence:int,syntax:Q.carrier,declarations:F.doc list,
     expression:F.doc}
  type result =
    {types:(Type.hol_type,string) Redblackmap.dict,
     symbols:S.symbol list,encodings:S.encoding list,roots:root list}

  fun emit (context:Q.outbound_context)
      {operations,regime,apply_operator,prefix,roots} : result =
    let
      val store = S.create context {prefix=prefix}
      val access = #operations store
      val output : F.doc SmtLib.outbound_output_operations =
        {text=F.text,concat=F.concat,join=F.join}
      fun guard current = ignore ((#key context) current)
      fun environment bounds = List.map
        (fn (variable,name) => ((#semantic_key context) variable,name))
        ((#bound_items access) bounds)

      fun emit_root (acc,(occurrence,syntax)) =
        let
          fun translate path region (acc as (_,terms),(bounds,current)) =
            let val _ = guard current in
              case (#find_document store) (terms,region,current) of
                SOME reference => (acc,([],reference))
              | NONE =>
                  let
                    val incoming = environment bounds
                    fun child (acc,(child_bounds,child)) =
                      if environment child_bounds = incoming then
                        translate path region (acc,(child_bounds,child))
                      else
                        let
                          val local_region = (#region_at store)
                            (occurrence,path,child_bounds)
                          val (acc as (_,terms),(declarations,body)) =
                            translate path local_region
                              (acc,(child_bounds,child))
                          val closed = (#wrap_document store)
                            (terms,local_region,body)
                        in (acc,(declarations,closed)) end
                    fun body (acc,(body_bounds,body)) =
                      let
                        val body_path = (#key context) current :: path
                        val body_region = (#region_at store)
                          (occurrence,body_path,body_bounds)
                        val (acc as (_,terms),(declarations,expression)) =
                          translate body_path body_region
                            (acc,(body_bounds,body))
                        val closed = (#wrap_document store)
                          (terms,body_region,expression)
                      in (acc,(declarations,closed)) end
                    fun seal (terms,body) =
                      (#wrap_document store) (terms,region,body)
                    val ((types,terms),(declarations,expression)) =
                      SmtLib.outbound_translate_term_step_with_lexical_output
                        output seal operations access child body regime
                        apply_operator (acc,(bounds,current))
                    (* An assertion root has no enclosing reference, and
                       an atom has no subtree to duplicate. Keep their
                       actual translation/store effects, but name only
                       compound descendants that can share expansion. *)
                    val direct = (#key context) current=
                        (#key context) syntax orelse
                      (case (#view context) current of
                         Q.ConstantView _ => true
                       | Q.VariableView _ => true | _ => false)
                    val (terms,reference) = if direct then (terms,expression)
                      else (#bind_document store)
                        (terms,region,current,expression)
                    val _ = guard current
                  in ((types,terms),(declarations,reference)) end
            end
          val bounds = #empty_bounds store
          val region = (#region store) (occurrence,bounds)
          val (acc as (_,terms),(declarations,body)) =
            translate [] region (acc,(bounds,syntax))
          val expression = (#wrap_document store) (terms,region,body)
        in (acc,{occurrence=occurrence,syntax=syntax,
          declarations=declarations,expression=expression}:root) end

      val initial = (Redblackmap.mkDict Type.compare,#empty_terms store)
      val ((types,terms),roots) = Lib.foldl_map emit_root (initial,roots)
    in {types=types,symbols=(#symbols store) terms,
      encodings=(#encodings store) terms,roots=roots} end
end
