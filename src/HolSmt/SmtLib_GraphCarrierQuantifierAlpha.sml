structure SmtLib_GraphCarrierQuantifierAlpha
  :> SmtLib_GraphCarrierQuantifierAlpha =
struct
  open SmtReplayGraph SmtReplayImport SmtReplayBinder
    SmtLib_GraphScopedRecipe HolSmtTheory
  structure G = SmtReplayGraph
  structure R = SmtLib_GraphScopedRecipe
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphCarrierQuantifierAlpha"
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
  fun natural
      ({graph,scope,admission,template_limit,source_variables,allow_bound,
        scope_opened} : options) source =
    let
      val {metric,input_limit,output_limit,check_type,refuse} = admission
      fun refusal text =
        (refuse text;raise ERR "natural" ("carrier admission: " ^ text))
      val _ = G.validate_scope graph scope
      val _ = ignore (G.type_of graph source)
      val _ = if G.scope_visible graph scope (G.node_scope graph source)
        then () else raise ERR "natural" "source escapes its owner"
      val maximum = case Int.maxInt of SOME limit => limit
        | NONE => 1073741823
      val _ = if input_limit > 0 andalso output_limit > 0 andalso
          input_limit < maximum andalso output_limit < maximum andalso
          template_limit > 0 then () else refusal "invalid admission contract"
      fun count limit term = case metric of G.RawNodes =>
          SmtReplayImport.bounded_raw_size limit term
        | G.BinderInclusiveNodes =>
            SmtReplayImport.bounded_binder_size limit term
      fun admitted label limit term = case count limit term of
          SOME size => if size <= limit then size else
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
      fun run universal predicate =
        let
          val actual = G.representative graph source
          (* Complete actual endpoint admission precedes every actual term
             destructor, FV/type traversal, frame and theorem specialization. *)
          val old_count = admitted "whole local input" input_limit actual
          val original_predicate = G.representative graph predicate
          val predicate_count = admitted "whole predicate input" input_limit
            original_predicate
        in if not (Term.is_abs original_predicate) then NONE else
        let
          val _ = add "complete predicate admission law"
            [3,predicate_count,predicate_count]
          val _ = types [actual]
          val (variable,body) = Term.dest_abs original_predicate
          val _ = if Type.compare (Term.type_of variable,numSyntax.num) = EQUAL
            then () else raise ERR "natural" "predicate binder type changed"
          val free = Term.free_vars actual
          val metadata = G.free_variable_nodes graph source
          val known = case source_variables of NONE => metadata
            | SOME variables =>
                (case metadata of NONE => SOME variables | SOME actual =>
                   if Listsort.sort Int.compare (List.map G.node_id actual) =
                       Listsort.sort Int.compare
                         (List.map G.node_id variables) then SOME variables
                   else raise ERR "natural" "supplied IDs contradict metadata")
          fun owned variable = case known of SOME variables =>
              (case List.find (fn node => Term.aconv variable
                  (G.representative graph node)) variables of SOME node => node
               | NONE => raise ERR "natural" "incomplete original free IDs")
            | NONE => if scope = G.root_scope graph andalso
                  G.origin graph predicate = G.ImportedSource then
                G.variable graph scope G.RigidSource variable
              else raise ERR "natural" "unknown scoped original free IDs"
          val _ = Option.app (List.app (fn node =>
            (ignore (G.type_of graph node);
             if G.scope_visible graph scope (G.node_scope graph node) then ()
             else raise ERR "natural" "supplied source ID escapes"))) known
          val bindings = List.map (fn variable => (variable,owned variable))
            free
          val _ = List.app (fn (_,node) =>
            (case G.view graph node of G.Variable (G.RigidSource,_) => ()
               | G.Variable (G.Bound,_) => if allow_bound then () else
                   raise ERR "natural" "unapproved original Bound ancestor"
               | _ => raise ERR "natural" "non-source free variable kind";
             if G.scope_visible graph scope (G.node_scope graph node) then ()
             else raise ERR "natural" "original ancestor ID escapes")) bindings
          val _ = List.app (fn (variable,node) =>
            if G.resolve_reference graph scope variable node = node then ()
            else raise ERR "natural" "supplied ID contradicts lexical owner")
            bindings
          val _ = case known of NONE => () | SOME variables =>
            if Listsort.sort Int.compare (List.map G.node_id variables) =
                Listsort.sort Int.compare
                  (List.map (G.node_id o #2) bindings) then () else
              raise ERR "natural" "inexact original free-ID set"
          val fixed = if universal then HolSmtTheory.NUM_FORALL_TO_INT
            else HolSmtTheory.NUM_EXISTS_TO_INT
          val _ = admitted "fixed source law" template_limit (Thm.concl fixed)
          val _ = types [Thm.concl fixed]
          val schematic = Drule.SPEC_ALL fixed
          val schematic_count = admitted "schematic whole law" template_limit
            (Thm.concl schematic)
          val (left,right) = boolSyntax.dest_eq (Thm.concl schematic)
          val hole = hd (Term.free_vars (Thm.concl schematic))
          val _ = if List.length (Term.free_vars (Thm.concl schematic)) = 1
            then () else raise ERR "natural" "unexpected fixed schema holes"
          val left_count = admitted "fixed source schema" template_limit left
          val right_count = admitted "fixed target schema" template_limit right
          fun occurrences [] total = total
            | occurrences (term :: pending) total =
                if Term.is_var term then
                  occurrences pending (if Term.aconv variable term then
                    total+1 else total)
                else if Term.is_comb term then
                  let val (operator,operand) = Term.dest_comb term in
                    occurrences (operator :: operand :: pending) total end
                else if Term.is_abs term then
                  let val (binder,body) = Term.dest_abs term in
                    if Term.aconv variable binder then
                      occurrences pending total
                    else occurrences (body :: pending) total end
                else occurrences pending total
          val uses = occurrences [body] 0
          val slot = case metric of G.RawNodes => 1
            | G.BinderInclusiveNodes => 2
          (* P occurs exactly twice in the checked fixed whole equality.
             The target P(Num i) is five nodes; its one introduced beta
             replaces each original bound variable by the three-node Num i.
             This exact prospective count avoids normalizing old redexes. *)
          val _ = add "complete specialized law"
            [schematic_count-2,predicate_count,predicate_count]
          val uncontracted_count = add "complete scoped recipe target"
            [right_count-1,predicate_count]
          val _ = add "complete specialized-to-recipe bridge"
            [3,uncontracted_count,uncontracted_count]
          val target_count = add "complete beta target"
            [right_count-5,predicate_count-slot,uses,uses]
          val _ = add "complete source introduced-beta law"
            [3,left_count-1,predicate_count,old_count]
          val _ = add "complete target introduced-beta law"
            [3,uncontracted_count,target_count]
          val _ = add "complete target admission/rehome law"
            [3,target_count,target_count]
          val final_count = add "complete source-to-carrier law"
            [3,old_count,target_count]
          val _ = add "complete final proposition ALPHA law"
            [3,final_count,final_count]
          val recipe = R.compile {template = right,holes = [hole],
            template_limit = template_limit,check_type = check_type}
          val temporary = G.new_scope graph scope bindings
          fun close () = G.close_scope graph temporary
          fun work () =
            let
              val _ = scope_opened temporary
              val admitted_predicate = G.admit_binder graph temporary
                input_limit original_predicate
              val constructed = R.construct graph temporary recipe
                {operands = [#node admitted_predicate],
                 expected_result_type = SOME Type.bool,admission = admission,
                 scope_opened = scope_opened}
              (* Specialize only the admitted local predicate, after complete
                 prospective laws and graph output have been admitted.
                 No INST of actual operands/residues is performed. *)
              val specialized = Thm.SPEC original_predicate fixed
              val _ = admitted "actual specialized law" output_limit
                (Thm.concl specialized)
              val (left,right) = boolSyntax.dest_eq (Thm.concl specialized)
              val constructed_term = G.representative graph
                (#node constructed)
              val _ = admitted "actual scoped target" output_limit
                constructed_term
              val recipe_bridge = Thm.ALPHA right constructed_term
              fun beta term = if Term.is_comb term andalso
                  Term.is_abs (Term.rator term) then Thm.BETA_CONV term
                else Thm.REFL term
              val left_beta = Conv.RAND_CONV (Conv.ABS_CONV beta) left
              val right_beta = Conv.RAND_CONV
                (Conv.ABS_CONV (Conv.RAND_CONV beta)) constructed_term
              val result = #2 (boolSyntax.dest_eq (Thm.concl right_beta))
              val _ = admitted "actual beta target" output_limit result
              val _ = types [result]
              val _ = if count output_limit result = SOME target_count then ()
                else raise ERR "natural" "prospective target metric mismatch"
              val actual_free = Term.free_vars result
              val _ = if List.length actual_free = List.length free andalso
                  List.all (fn variable =>
                    List.exists (Term.aconv variable) free) actual_free then ()
                else raise ERR "natural" "carrier changed original free set"
              val target_predicate = G.admit_binder graph temporary output_limit
                (Term.rand result)
              val operator = G.constant graph temporary (Term.rator result)
              val candidate = G.application graph temporary
                (operator,#node target_predicate)
              val rehomed = G.rehome graph scope candidate
              val to_candidate = Thm.AP_TERM (Term.rator result)
                (#bridge target_predicate)
              val theorem = Thm.TRANS (Thm.SYM left_beta)
                (Thm.TRANS specialized
                  (Thm.TRANS recipe_bridge
                    (Thm.TRANS right_beta
                      (Thm.TRANS to_candidate (#bridge rehomed)))))
              val equality = equation graph scope source (#node rehomed)
              val expected = G.representative graph equality
              val _ = admitted "actual complete carrier law" output_limit
                expected
              val _ = admitted "actual complete proof conclusion" output_limit
                (Thm.concl theorem)
              val theorem = Thm.EQ_MP
                (Thm.ALPHA (Thm.concl theorem) expected) theorem
              val _ = if null (Thm.hyp theorem) then () else
                raise ERR "natural" "carrier bridge has hypotheses"
              val (oracles,_) = Tag.dest_tag (Thm.tag theorem)
              val _ = if List.all (fn oracle => oracle = "DISK_THM") oracles
                  andalso null (Tag.axioms_of (Thm.tag theorem)) then () else
                raise ERR "natural" "carrier bridge has unexpected proof tags"
            in Transfer {source = source,target = #node rehomed,
              equality = equality,theorem = theorem} end
        in SOME (work () before close ())
           handle error => (close ();raise error) end end
    in case G.view graph source of G.Application (operator,predicate) =>
        (case G.view graph operator of G.Constant _ =>
           let val term = G.representative graph operator
               val universal = Term.same_const term boolSyntax.universal
               val existential = Term.same_const term boolSyntax.existential
           in if (universal orelse existential) andalso
               Type.compare (#1 (Type.dom_rng (G.type_of graph predicate)),
                 numSyntax.num) = EQUAL then run universal predicate else NONE
           end
         | _ => NONE)
      | _ => NONE end
end
