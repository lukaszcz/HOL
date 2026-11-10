structure SmtLib_GraphFloatCarrier :> SmtLib_GraphFloatCarrier =
struct
  open SmtReplayGraph SmtReplayImport SmtReplayBinder
    SmtLib_GraphScopedRecipe smtfloatTheory
  structure G = SmtReplayGraph
  structure R = SmtLib_GraphScopedRecipe
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphFloatCarrier"
  exception NotFactored
  type options =
    {graph : G.graph,scope : G.scope,admission : SmtReplayBinder.admission,
     template_limit : int,source_variables : G.node list option,
     allow_bound : bool,scope_opened : G.scope -> unit}
  datatype transfer = Transfer of
    {source : G.node,target : G.node,equality : G.node,theorem : Thm.thm}
  fun source (Transfer {source,...}) = source
  fun target (Transfer {target,...}) = target
  fun equality (Transfer {equality,...}) = equality
  fun theorem (Transfer {theorem,...}) = theorem
  fun equation graph scope left right =
    let val operator = G.constant graph scope (Term.inst
          (Type.match_type (Term.type_of boolSyntax.equality)
            (boolSyntax.list_mk_fun
              ([G.type_of graph left,G.type_of graph left],Type.bool)))
          boolSyntax.equality)
    in G.application graph scope
      (G.application graph scope (operator,left),right) end
  fun discover
      ({graph,scope,admission,template_limit,source_variables,allow_bound,
        scope_opened} : options) source =
    let
      val {metric,input_limit,output_limit,check_type,refuse} = admission
      fun refusal text =
        (refuse text;raise ERR "discover" ("float carrier admission: " ^ text))
      val _ = G.validate_scope graph scope
      val _ = ignore (G.type_of graph source)
      val _ = if G.scope_visible graph scope (G.node_scope graph source) then ()
        else raise ERR "discover" "source escapes its owner"
      val maximum = case Int.maxInt of SOME limit => limit
        | NONE => 1073741823
      val _ = if input_limit > 0 andalso output_limit > 0 andalso
          input_limit < maximum andalso output_limit < maximum andalso
          template_limit > 0 then () else refusal "invalid contract"
      fun count limit term = case metric of G.RawNodes =>
          SmtReplayImport.bounded_raw_size limit term
        | G.BinderInclusiveNodes =>
            SmtReplayImport.bounded_binder_size limit term
      fun admit label limit term = case count limit term of SOME size =>
          if size <= limit then size else
            (refusal label;raise Fail "unreachable")
        | NONE => (refusal label;raise Fail "unreachable")
      fun add label pieces =
        let fun loop [] total = total
              | loop (piece :: rest) total =
                  if piece < 0 orelse piece > output_limit-total then
                    (refusal label;raise Fail "unreachable")
                  else loop rest (total+piece)
        in loop pieces 0 end
      fun types [] = ()
        | types (term :: pending) =
            (check_type (Term.type_of term);
             if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term in
                 types (operator :: operand :: pending) end
             else if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term in
                 types (variable :: body :: pending) end
             else types pending)
      fun run universal predicate domain =
        let
          val actual = G.representative graph source
          val source_count = admit "whole local input" input_limit actual
          val actual_predicate = G.representative graph predicate
          val predicate_count = admit "whole predicate input" input_limit
            actual_predicate
        in if not (Term.is_abs actual_predicate) then NONE else
        let
          val _ = add "complete predicate admission law"
            [3,predicate_count,predicate_count]
          val slot = case metric of G.RawNodes => 1
            | G.BinderInclusiveNodes => 2
          val minimum_slots = 3+2+slot+1
          val alpha_budget = (output_limit-3) div 2
          val _ = if output_limit >= 3 andalso alpha_budget >= minimum_slots
              andalso source_count <= alpha_budget-minimum_slots then () else
            refusal "minimum whole proposition ALPHA law"
          val _ = types [actual]
          val free = Term.free_vars actual
          val metadata = G.free_variable_nodes graph source
          val known = case source_variables of NONE => metadata
            | SOME supplied =>
                (case metadata of NONE => SOME supplied | SOME recorded =>
                   if Listsort.sort Int.compare (List.map G.node_id recorded) =
                       Listsort.sort Int.compare (List.map G.node_id supplied)
                   then SOME supplied else
                     raise ERR "discover" "supplied IDs contradict metadata")
          val _ = Option.app (List.app (fn node =>
            (ignore (G.type_of graph node);
             if G.scope_visible graph scope (G.node_scope graph node) then ()
             else raise ERR "discover" "source free ID escapes"))) known
          fun owned variable = case known of SOME nodes =>
              (case List.find (fn node => Term.aconv variable
                  (G.representative graph node)) nodes of SOME node => node
               | NONE => raise ERR "discover" "incomplete source free IDs")
            | NONE => if scope = G.root_scope graph andalso
                  G.origin graph predicate = G.ImportedSource then
                G.variable graph scope G.RigidSource variable
              else raise ERR "discover" "unknown scoped source free IDs"
          val bindings = List.map (fn variable => (variable,owned variable))
            free
          val _ = List.app (fn (variable,node) =>
            (case G.view graph node of G.Variable (G.RigidSource,_) => ()
               | G.Variable (G.Bound,_) => if allow_bound then () else
                   raise ERR "discover" "unapproved Bound ancestor"
               | _ => raise ERR "discover" "non-source variable kind";
             if G.resolve_reference graph scope variable node = node then ()
             else raise ERR "discover" "source ID contradicts lexical owner"))
            bindings
          val _ = case known of NONE => () | SOME nodes =>
            if Listsort.sort Int.compare (List.map G.node_id nodes) =
                Listsort.sort Int.compare
                  (List.map (G.node_id o #2) bindings) then () else
              raise ERR "discover" "inexact whole source free-ID set"
          val fixed = if universal then
              smtfloatTheory.native_float_forall_transfer
            else smtfloatTheory.native_float_exists_transfer
          val _ = admit "fixed generic law" template_limit (Thm.concl fixed)
          val (generic_left,_) = boolSyntax.dest_eq (Thm.concl fixed)
          val generic_variable = #1 (Term.dest_abs (Term.rand generic_left))
          val typed = Thm.INST_TYPE
            (Type.match_type (Term.type_of generic_variable) domain) fixed
          val _ = admit "typed fixed law" template_limit (Thm.concl typed)
          val _ = types [Thm.concl typed]
          val holes = Term.free_vars (Thm.concl typed)
          val hole = case holes of [hole] => hole
            | _ => raise ERR "discover" "unexpected fixed predicate holes"
          val (left,right) = boolSyntax.dest_eq (Thm.concl typed)
          val carrier_type = #1 (Type.dom_rng (Term.type_of hole))
          val _ = check_type carrier_type
          val generalized_size = 2 +
            (case metric of G.RawNodes => 1 | G.BinderInclusiveNodes => 2)
          val _ = if template_limit >= generalized_size then
              ignore (admit "whole generalized fixed law"
                (template_limit-generalized_size) (Thm.concl typed))
            else refusal "whole generalized fixed law"
          val generalized = Thm.GEN hole typed
          val left_count = admit "fixed left schema" template_limit left
          val right_count = admit "fixed right schema" template_limit right
          val fixed_count = admit "fixed whole schema" template_limit
            (Thm.concl typed)
          val temporary = G.new_scope graph scope bindings
          fun close () = G.close_scope graph temporary
          fun work () =
            let
              val _ = scope_opened temporary
              val admitted = G.admit_binder graph temporary input_limit
                actual_predicate
              val (bound,body) = case G.view graph (#node admitted) of
                  G.AdmittedBinder {binder,body,...} => (binder,body)
                | _ => raise ERR "discover" "source predicate not admitted"
              val intro = Term.prim_mk_const
                {Thy = "smtfloat",Name = "smtfp_intro"}
              fun image node = case G.view graph node of
                  G.Application (operator,operand) => operand = bound andalso
                    (case G.view graph operator of G.Constant _ =>
                       Term.same_const (G.representative graph operator) intro
                     | _ => false)
                | _ => false
              val counted = ref (Redblackmap.mkDict Int.compare)
              fun uses node = case Redblackmap.peek (!counted,G.node_id node) of
                  SOME total => total
                | NONE =>
                    let val total = if image node then 1 else
                          if node = bound then raise NotFactored else
                          case G.view graph node of
                            G.Application (left,right) => uses left + uses right
                          | G.AdmittedBinder {body,...} => uses body
                          | G.OpaqueRetained => raise NotFactored
                          | _ => 0
                        val _ = counted := Redblackmap.insert
                          (!counted,G.node_id node,total)
                    in total end
              val occurrences = uses body
              val factored_count = predicate_count-2*occurrences
              val target_count = factored_count+2
              val uncontracted_left = add "specialized source target"
                [left_count-1,factored_count]
              val uncontracted_right = add "specialized carrier target"
                [right_count-1,factored_count]
              val _ = add "complete specialized law"
                [fixed_count-2,factored_count,factored_count]
              val _ = add "complete source beta law"
                [3,uncontracted_left,source_count]
              val _ = add "complete RHS recipe alignment law"
                [3,uncontracted_right,uncontracted_right]
              val _ = add "complete target beta law"
                [3,uncontracted_right,target_count]
              val _ = add "complete source endpoint alignment law"
                [3,source_count,source_count]
              val _ = add "complete target admission/rehome law"
                [3,target_count,target_count]
              val final_count = add "complete source-to-carrier law"
                [3,source_count,target_count]
              val _ = add "complete final proposition ALPHA law"
                [3,final_count,final_count]
              val factored_scope = G.new_scope graph temporary []
              val _ = scope_opened factored_scope
              val new_bound = G.fresh_bound_variable graph factored_scope
                (Term.mk_var ("float_carrier",carrier_type))
              fun copied current substitutions node =
                if image node then new_bound else
                if node = bound then raise NotFactored else
                case G.view graph node of
                  G.Variable _ =>
                    (case List.find (fn (old,_) => old = node) substitutions of
                       SOME (_,replacement) => replacement
                     | NONE => if G.scope_visible graph current
                         (G.node_scope graph node) then node
                       else raise NotFactored)
                | G.Constant _ => G.constant graph current
                    (G.representative graph node)
                | G.Application (operator,operand) =>
                    G.application graph current
                    (copied current substitutions operator,
                     copied current substitutions operand)
                | G.AdmittedBinder {binder,body,...} =>
                    let
                      val child = G.new_scope graph current []
                      fun close_child () = G.close_scope graph child
                      fun build () =
                        let val _ = scope_opened child
                            val variable = G.fresh_bound_variable graph child
                              (G.representative graph binder)
                            val body = copied child
                              ((binder,variable) :: substitutions) body
                        in G.abstraction graph current output_limit
                          (variable,body) end
                    in build () before close_child ()
                       handle error => (close_child ();raise error) end
                | G.OpaqueRetained => raise NotFactored
              val factored_body = copied factored_scope [] body
              val factored = G.abstraction graph temporary output_limit
                (new_bound,factored_body)
              val _ = case G.unfolded_nodes graph metric output_limit
                  factored of
                  SOME size => if size = factored_count then () else
                    raise ERR "discover" "factored metric disagreement"
                | NONE => raise ERR "discover" "unknown factored predicate"
              val recipe = R.compile {template = right,holes = [hole],
                template_limit = template_limit,check_type = check_type}
              val constructed = R.construct graph temporary recipe
                {operands = [factored],expected_result_type = SOME Type.bool,
                 admission = admission,scope_opened = scope_opened}
              val specialized = Thm.SPEC (G.representative graph factored)
                generalized
              val _ = admit "actual specialized law" output_limit
                (Thm.concl specialized)
              val (left,right) = boolSyntax.dest_eq (Thm.concl specialized)
              val constructed_term = G.representative graph (#node constructed)
              val _ = admit "actual scoped carrier target" output_limit
                constructed_term
              val recipe_bridge = Thm.ALPHA right constructed_term
              fun beta term = if Term.is_comb term andalso
                  Term.is_abs (Term.rator term) then Thm.BETA_CONV term
                else Thm.REFL term
              val left_beta = Conv.RAND_CONV (Conv.ABS_CONV beta) left
              val original_left = #2 (boolSyntax.dest_eq (Thm.concl left_beta))
              val source_bridge = Thm.ALPHA actual original_left
              val right_beta = Conv.RAND_CONV (Conv.ABS_CONV beta)
                constructed_term
              val result = #2 (boolSyntax.dest_eq (Thm.concl right_beta))
              val _ = if count output_limit result = SOME target_count then ()
                else refusal "actual carrier target count disagreement"
              val _ = types [result]
              val target_free = Term.free_vars result
              val _ = if List.length target_free = List.length free andalso
                  List.all (fn variable => List.exists (Term.aconv variable)
                    free) target_free then () else
                raise ERR "discover" "carrier changed original free variables"
              val target_predicate = G.admit_binder graph temporary output_limit
                (Term.rand result)
              val operator = G.constant graph temporary (Term.rator result)
              val candidate = G.application graph temporary
                (operator,#node target_predicate)
              val rehomed = G.rehome graph scope candidate
              val candidate_bridge = Thm.AP_TERM (Term.rator result)
                (#bridge target_predicate)
              val theorem = Thm.TRANS source_bridge
                (Thm.TRANS (Thm.SYM left_beta)
                  (Thm.TRANS specialized
                    (Thm.TRANS recipe_bridge
                      (Thm.TRANS right_beta
                        (Thm.TRANS candidate_bridge (#bridge rehomed))))))
              val equality = equation graph scope source (#node rehomed)
              val expected = G.representative graph equality
              val _ = admit "actual complete source carrier law" output_limit
                expected
              val _ = admit "actual complete proof conclusion" output_limit
                (Thm.concl theorem)
              val theorem = Thm.EQ_MP
                (Thm.ALPHA (Thm.concl theorem) expected) theorem
              val (tags,_) = Tag.dest_tag (Thm.tag theorem)
              val _ = if null (Thm.hyp theorem) andalso
                  List.all (fn tag => tag = "DISK_THM") tags andalso
                  null (Tag.axioms_of (Thm.tag theorem)) then () else
                raise ERR "discover" "carrier law has hypotheses or bad tags"
            in Transfer {source = source,target = #node rehomed,
              equality = equality,theorem = theorem} end
        in SOME (work () before close ())
           handle NotFactored => (close ();NONE)
                | error => (close ();raise error) end end
    in case G.view graph source of G.Application (operator,predicate) =>
        (case G.view graph operator of G.Constant _ =>
           let
             val term = G.representative graph operator
             val universal = Term.same_const term boolSyntax.universal
             val existential = Term.same_const term boolSyntax.existential
           in if not (universal orelse existential) then NONE else
               let val domain = #1 (Type.dom_rng (G.type_of graph predicate)) in
                 if Type.is_vartype domain then NONE else
                   let val {Thy,Tyop,...} = Type.dest_thy_type domain in
                     if Thy = "binary_ieee" andalso Tyop = "float" then
                       run universal predicate domain else NONE
                   end
               end
           end
         | _ => NONE)
      | _ => NONE end
end
