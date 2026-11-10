structure SmtLib_GraphScopedMap :> SmtLib_GraphScopedMap =
struct
  open SmtReplayGraph SmtReplayBinder SmtLib_GraphBackend
    SmtLib_GraphFrontend SmtLib_GraphScopedRecipe SmtLib_Parser
  structure G = SmtReplayGraph
  structure B = SmtLib_GraphBackend
  structure C = SmtLib_GraphScopedRecipe
  structure P = SmtLib_Parser
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphScopedMap"
  type options =
    {graph : G.graph, admission : SmtReplayBinder.admission,
     template_limit : int,scope_opened : G.scope -> unit,
     record : G.node * G.node * Thm.thm -> unit}
  val maximum = case Int.maxInt of SOME value => value
    | NONE => 1073741823
  fun ids nodes = Listsort.sort Int.compare (List.map G.node_id nodes)
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem) in
      null (Thm.hyp theorem) andalso
      List.all (fn tag => tag = "DISK_THM") tags andalso
      null (Tag.axioms_of (Thm.tag theorem)) end
  fun install ({graph,admission,template_limit,scope_opened,record} : options)
      (session : SmtLib_GraphFrontend.session) =
    let
      val backend = #backend (#reader session)
      val {metric,input_limit,output_limit,check_type,refuse} = admission
      fun fail reason = (refuse reason;raise ERR "map" reason)
      val _ = if input_limit > 0 andalso output_limit > 0 andalso
          input_limit < maximum andalso output_limit < maximum then ()
        else fail "invalid Z3 map admission"
      fun bounded label limit term =
        case (case metric of G.RawNodes =>
            SmtReplayImport.bounded_raw_size limit term
          | G.BinderInclusiveNodes =>
            SmtReplayImport.bounded_binder_size limit term) of
          SOME _ => () | NONE => fail label
      val entries = [("and",boolSyntax.conjunction,Type.bool,2),
        ("or",boolSyntax.disjunction,Type.bool,2),
        ("not",boolSyntax.negation,Type.bool,1),
        ("+",intSyntax.plus_tm,intSyntax.int_ty,2)]
      fun compile (token,function,range,count) =
        let val domain = Type.mk_vartype "'map_domain"
            val index = Term.mk_var ("array_map_x",domain)
            val holes = List.tabulate (count,fn i => Term.mk_var
              ("map_hole_" ^ Int.toString i,Type.--> (domain,range)))
            val template = Term.mk_abs (index,Term.list_mk_comb
              (function,List.map (fn hole => Term.mk_comb (hole,index)) holes))
            val recipe = C.compile {template = template,holes = holes,
              template_limit = template_limit,check_type = check_type}
        in (token,function,range,count,recipe) end
      val recipes = List.map compile entries
      fun size scope node =
        let val owner = G.node_scope graph node
            val _ = if G.scope_visible graph scope owner then () else
              fail "Z3 map operand escapes scope"
        in case G.unfolded_nodes graph metric input_limit node of
            SOME size => if size <= input_limit then size else
              fail "Z3 map operand input"
          | NONE => fail "unknown Z3 map operand input" end
      fun free scope node = case G.free_variable_nodes graph node of
          NONE => fail "unknown Z3 map operand free IDs"
        | SOME variables =>
            (List.app (fn variable =>
              if G.scope_visible graph scope (G.node_scope graph variable)
              then case G.view graph variable of G.Variable _ => ()
                | _ => fail "invalid Z3 map free ID"
              else fail "Z3 map free ID escapes scope") variables;variables)
      (* The ordinary predicate recognizes UPDATE applied to index, value
         and array. Match that exact graph shape under admitted binders. *)
      fun update node = case G.view graph node of
          G.Application (partial,_) =>
            (case G.view graph partial of
               G.Application (partial,_) =>
                 (case G.view graph partial of
                    G.Application (operator,_) =>
                      (case G.view graph operator of G.Constant _ =>
                         Term.same_const (G.representative graph operator)
                           combinSyntax.update_tm
                       | _ => false)
                  | _ => false)
             | _ => false)
        | _ => false
      fun contracts array = case G.view graph array of
          G.AdmittedBinder _ =>
            not (List.exists update (G.reachable graph [array]))
        | _ => false
      fun plus a b = if a > output_limit orelse b > output_limit orelse
          a > output_limit-b then fail "Z3 map whole output" else a+b
      fun map frame token indices arrays =
        if token <> "map" then
          SmtLib_Theories.decline "graph map" "not an indexed map"
        else
          let
            val indexed = case indices of [P.SymbolIndex operator] => operator
              | _ => SmtLib_Theories.decline "graph map"
                  "one registered operator index expected"
            val (_,function,range,count,recipe) = case List.find
                (fn (name,_,_,_,_) => name = indexed) recipes of
                SOME entry => entry
              | NONE => SmtLib_Theories.decline "graph map"
                  "unsupported indexed map operator"
            val _ = if List.length arrays = count then () else
              SmtLib_Theories.decline "graph map" "wrong array count"
            val scope = valOf (B.frame_scope backend frame)
            (* All input sizes precede any FV, type or UPDATE body scan. *)
            val sizes = List.map (size scope) arrays
            val _ = List.app (fn node => ignore (free scope node)) arrays
            val _ = List.app (check_type o G.type_of graph)
              (G.reachable graph arrays)
            val domains = List.map (Type.dom_rng o G.type_of graph) arrays
            val domain = #1 (hd domains)
            val _ = if List.all (fn (d,r) =>
                Type.compare (d,domain) = EQUAL andalso
                Type.compare (r,range) = EQUAL) domains then () else
              SmtLib_Theories.decline "graph map" "array sort mismatch"
            val contracting = List.map contracts arrays
            val changes = List.exists (fn flag => flag) contracting
            val overhead = case metric of G.RawNodes => 1
              | G.BinderInclusiveNodes => 2
            val staged_size = List.foldl (fn (size,total) =>
              plus total (plus size 3)) (plus 1 overhead) sizes
            (* Variable-only beta operands cannot grow the admitted map.
               Admit the complete prospective conversion law before any
               ScopedRecipe scope or actual HOL binder is constructed. *)
            val _ = ignore (plus 3 (plus staged_size staged_size))
            val staged = #node (C.construct graph scope recipe
              {operands = arrays,expected_result_type =
                 SOME (Type.--> (domain,range)),admission = admission,
               scope_opened = scope_opened})
            fun normalize () =
              let
                val original = G.representative graph staged
                val _ = bounded "Z3 map staged output" output_limit original
                val (index,_) = Term.dest_abs original
                fun select (array,contract) =
                  let val application = Term.mk_comb
                        (G.representative graph array,index)
                  in if contract then Thm.BETA_CONV application
                    else Thm.REFL application end
                val selections = ListPair.mapEq select (arrays,contracting)
                val body = List.foldl (fn (selection,proof) =>
                  Thm.MK_COMB (proof,selection)) (Thm.REFL function) selections
                val conversion = Thm.ABS index body
                val _ = bounded "Z3 map conversion law" output_limit
                  (Thm.concl conversion)
                val (left,normalized) = boolSyntax.dest_eq
                  (Thm.concl conversion)
                val _ = if Term.aconv left original then () else
                  fail "Z3 map staged conversion endpoint"
                val _ = bounded "Z3 map normalized output" output_limit
                  normalized
                val variables = free scope staged
                val bindings = List.map (fn variable =>
                  (G.representative graph variable,variable)) variables
                val temporary = G.new_scope graph scope bindings
                fun work () =
                  let
                    val _ = scope_opened temporary
                    val admitted = G.admit_binder graph temporary output_limit
                      normalized
                    val actual = case G.free_variable_nodes graph
                        (#node admitted) of SOME values => values
                      | NONE => fail "unknown normalized Z3 map free IDs"
                    val _ = if ids actual = ids variables then () else
                      fail "normalized Z3 map free IDs changed"
                    val returned = G.rehome graph scope (#node admitted)
                    val bridge = Thm.TRANS conversion
                      (Thm.TRANS (#bridge admitted) (#bridge returned))
                    val _ = bounded "Z3 map returned conversion law"
                      output_limit (Thm.concl bridge)
                    val exact = boolSyntax.mk_eq
                      (G.representative graph staged,
                       G.representative graph (#node returned))
                    val _ = bounded "Z3 map exact conversion law"
                      output_limit exact
                    val bridge = Thm.EQ_MP
                      (Thm.ALPHA (Thm.concl bridge) exact) bridge
                    val _ = if clean bridge andalso
                        G.type_id graph staged =
                          G.type_id graph (#node returned) then () else
                      fail "invalid normalized Z3 map bridge"
                  in (#node returned,bridge) end
                val result = work () handle error =>
                  (G.close_scope graph temporary;raise error)
                val _ = G.close_scope graph temporary
              in result end
            val (result,bridge) = if changes then normalize ()
              else (staged,Thm.REFL (G.representative graph staged))
            val _ = record (staged,result,bridge)
          in result end
      val _ = List.app (fn (operator,_,_,_) =>
        (#add_symbolic_index session) ("map",operator)) entries
    in (#add_constructor_parser session) ("map",map) end
end
