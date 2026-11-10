structure SmtLib_GraphGuardedBagCarrier
  :> SmtLib_GraphGuardedBagCarrier =
struct
  open SmtReplayGraph SmtReplayImport SmtLib_GraphNativeBinderConversion
    SmtLib HolSmtTheory
  structure G = SmtReplayGraph
  structure B = SmtLib_GraphNativeBinderConversion
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphGuardedBagCarrier"
  exception Incomplete
  type options =
    {graph : G.graph,admission : SmtReplayBinder.admission,
     template_limit : int,scope_opened : G.scope -> unit}
  fun local_witness
      ({graph,admission,template_limit,scope_opened} : options) scope source =
    let
      val {metric,input_limit,output_limit,check_type,...} = admission
      val _ = G.validate_scope graph scope
      val _ = ignore (G.type_of graph source)
      val _ = if G.scope_visible graph scope (G.node_scope graph source) then ()
        else raise ERR "local_witness" "source escapes active owner"
      val _ = if input_limit > 0 andalso output_limit > 0 andalso
          template_limit > 0 then () else
        raise ERR "local_witness" "nonpositive carrier contract"
      fun count limit term = case metric of G.RawNodes =>
          SmtReplayImport.bounded_raw_size limit term
        | G.BinderInclusiveNodes =>
            SmtReplayImport.bounded_binder_size limit term
      fun bounded limit term = case count limit term of SOME size => size
        | NONE => raise Incomplete
      fun types [] = ()
        | types (term :: pending) =
            (check_type (Term.type_of term);
             if Term.is_comb term then
               let val (left,right) = Term.dest_comb term in
                 types (left :: right :: pending) end
             else if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term in
                 types (variable :: body :: pending) end
             else types pending)
      fun equation left right =
        let val operator = G.constant graph scope (Term.inst
              (Type.match_type (Term.type_of boolSyntax.equality)
                (boolSyntax.list_mk_fun
                  ([G.type_of graph left,G.type_of graph left],Type.bool)))
              boolSyntax.equality)
        in G.application graph scope
          (G.application graph scope (operator,left),right) end
      fun run universal predicate =
        let
          val actual = G.representative graph source
          val size = bounded input_limit actual
          val fixed = if universal then HolSmtTheory.BAG_FORALL_TO_INT
            else HolSmtTheory.BAG_EXISTS_TO_INT
          val fixed_size = bounded template_limit (Thm.concl fixed)
          val _ = case SmtReplayImport.bounded_raw_size template_limit
              (Thm.concl fixed) of SOME _ => () | NONE => raise Incomplete
          (* In this restricted syntax each old bag-variable occurrence is
             replaced by at most eight nodes. The fixed whole law covers
             the generated outer binder and Boolean pointwise guard. This
             upper bound admits complete specialization, output, rehome,
             source-to-target equality and equality-of-propositions ALPHA
             BEFORE actual type/FV/binder/kernel conversion work. It is a
             conservative compatibility bound, not a performance claim. *)
          val budget = Int.min (output_limit,template_limit)
          val _ = if budget > 9 andalso fixed_size <= (budget-9) div 2 andalso
              size <= (budget-9-2*fixed_size) div 18 then () else
            raise Incomplete
          val actual_predicate = G.representative graph predicate
          val _ = if Term.is_abs actual_predicate then () else raise Incomplete
          val _ = types [actual,Thm.concl fixed]
          val (_,body) = Term.dest_abs actual_predicate
          fun restricted [] = ()
            | restricted (term :: pending) =
                if Term.is_comb term then
                  let val (operator,operand) = Term.dest_comb term
                  in if Term.is_abs operator orelse
                      (Term.is_const operator andalso
                       (Term.same_const operator boolSyntax.universal orelse
                        Term.same_const operator boolSyntax.existential))
                    then raise Incomplete
                    else restricted (operator :: operand :: pending) end
                else if Term.is_abs term then
                  let val (variable,body) = Term.dest_abs term
                      val ty = Term.type_of variable
                  in if Type.compare (ty,numSyntax.num) = EQUAL orelse
                      (case Lib.total Type.dom_rng ty of SOME (_,range) =>
                         Type.compare (range,numSyntax.num) = EQUAL
                       | NONE => false) then raise Incomplete
                    else restricted (body :: pending) end
                else restricted pending
          val _ = restricted [body]
          val free = Term.free_vars actual
          val known = G.free_variable_nodes graph source
          fun owned variable = case known of SOME variables =>
              (case List.find (fn node => Term.aconv variable
                  (G.representative graph node)) variables of SOME node => node
               | NONE => raise ERR "local_witness" "missing source free ID")
            | NONE => if scope = G.root_scope graph andalso
                  G.origin graph source = G.ImportedSource then
                G.variable graph scope G.RigidSource variable
              else raise Incomplete
          val bindings = List.map (fn variable => (variable,owned variable))
            free
          val _ = List.app (fn (variable,node) =>
            (case G.view graph node of G.Variable (G.RigidSource,_) => ()
               | G.Variable (G.Bound,_) => ()
               | _ => raise ERR "local_witness" "unapproved source free kind";
             if G.resolve_reference graph scope variable node = node then ()
             else raise ERR "local_witness" "source lexical ID changed";
             if G.scope_visible graph scope (G.node_scope graph node) then ()
             else raise ERR "local_witness" "ancestor free ID escapes"))
            bindings
          val _ = case known of NONE => () | SOME variables =>
            if Listsort.sort Int.compare (List.map G.node_id variables) =
                Listsort.sort Int.compare
                  (List.map (G.node_id o #2) bindings) then () else
              raise ERR "local_witness" "inexact whole source free-ID set"
          val temporary = G.new_scope graph scope bindings
          fun close () = G.close_scope graph temporary
          fun work () =
            let
              val _ = scope_opened temporary
              (* The public ordinary conversion runs only on the admitted
                 complete local binder, with the restricted linear output
                 model above. No outer DAG operand enters this conversion. *)
              val law = SmtLib.NUM_BINDERS_TO_INT_CONV actual
              val _ = ignore (bounded output_limit (Thm.concl law))
              val (left,right) = boolSyntax.dest_eq (Thm.concl law)
              val _ = ignore (bounded output_limit right)
              val _ = types [right]
              val actual_free = Term.free_vars right
              val _ = if List.length actual_free = List.length free andalso
                  List.all (fn variable =>
                    List.exists (Term.aconv variable) free) actual_free then ()
                else raise ERR "local_witness" "carrier changed source FV set"
              val target_binder = G.admit_binder graph temporary output_limit
                (Term.rand right)
              val operator = G.constant graph temporary (Term.rator right)
              val candidate = G.application graph temporary
                (operator,#node target_binder)
              val rehomed = G.rehome graph scope candidate
              val candidate_bridge = Thm.AP_TERM (Term.rator right)
                (#bridge target_binder)
              val to_left = Thm.ALPHA actual left
              val theorem = Thm.TRANS to_left
                (Thm.TRANS law
                  (Thm.TRANS candidate_bridge (#bridge rehomed)))
              val equality = equation source (#node rehomed)
              val expected = G.representative graph equality
              val _ = ignore (bounded output_limit expected)
              val _ = ignore (bounded output_limit (Thm.concl theorem))
              val _ = ignore (bounded output_limit
                (boolSyntax.mk_eq (Thm.concl theorem,expected)))
              val theorem = Thm.EQ_MP
                (Thm.ALPHA (Thm.concl theorem) expected) theorem
              val _ = Library.check_oracle_tags
                "GraphGuardedBagCarrier" "local_witness" theorem
              val _ = if null (Thm.hyp theorem) then () else
                raise ERR "local_witness" "carrier law retained hypotheses"
              val _ = case G.free_variable_nodes graph (#node rehomed) of
                  SOME variables => if Listsort.sort Int.compare
                      (List.map G.node_id variables) =
                      Listsort.sort Int.compare
                        (List.map (G.node_id o #2) bindings) then () else
                    raise ERR "local_witness" "target free IDs changed"
                | NONE => raise ERR "local_witness" "unknown target free IDs"
            in B.Checked {target = #node rehomed,theorem = theorem,
              continuation = false} end
        in work () before close ()
          handle error => (close ();raise error) end
      fun dispatch () = case G.view graph source of
          G.Application (operator,predicate) =>
            (case G.view graph operator of G.Constant _ =>
               let val head = G.representative graph operator
                   val universal = Term.same_const head boolSyntax.universal
                   val existential =
                     Term.same_const head boolSyntax.existential
               in if not (universal orelse existential) then B.Unhandled
                 else case Lib.total Type.dom_rng
                     (G.type_of graph predicate) of
                   SOME (domain,_) =>
                     (case Lib.total Type.dom_rng domain of
                        SOME (element,range) =>
                          if Type.compare (range,numSyntax.num) <> EQUAL then
                            B.Unhandled
                          else if Type.compare (element,Type.bool) <> EQUAL
                            then B.Gap else run universal predicate
                      | NONE => B.Unhandled)
                 | NONE => B.Unhandled end
             | _ => B.Unhandled)
        | _ => B.Unhandled
    in dispatch () handle Incomplete => B.Gap end
end
