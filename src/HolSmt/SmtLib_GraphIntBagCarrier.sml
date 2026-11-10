(* Fixed int bag-binder connector: UNCOMPILED Source proposal only. *)
structure SmtLib_GraphIntBagCarrier :> SmtLib_GraphIntBagCarrier =
struct
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure R = SmtLib_GraphScopedRecipe
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphIntBagCarrier"
  val maximum = case Int.maxInt of SOME n => n | NONE => 1073741823
  type options =
    {graph : G.graph,scope : G.scope,admission : SmtReplayBinder.admission,
     template_limit : int,original : G.node,view : G.source,
     law : P.closed_fact,scope_opened : G.scope -> unit}
  fun convert
      ({graph,scope,admission,template_limit,original,view,law,
        scope_opened} : options) =
    let
      val {metric,input_limit,output_limit,check_type,refuse} = admission
      fun active () = G.validate_scope graph scope
      fun reject text = (refuse text;raise ERR "convert" text)
      val _ = active ()
      val _ = if input_limit > 0 andalso input_limit < maximum andalso
          output_limit > 0 andalso output_limit < maximum andalso
          template_limit > 0 andalso template_limit < maximum then () else
        reject "invalid original cap"
      (* Validate genuine original/view registration BEFORE old inspection. *)
      val _ = G.validate_opened_view graph scope original view
      val source = #node view
      val _ = P.validate_closed_fact graph scope template_limit law
      fun node_size limit node metric =
        case G.unfolded_nodes graph metric limit node of
          SOME n => if n <= limit then n else reject "recorded size exceeds cap"
        | NONE => reject "missing recorded original binder metadata"
      val old_raw = Int.max (node_size input_limit source G.RawNodes,
        node_size input_limit source G.BinderInclusiveNodes)
      val fixed_node = P.closed_node law
      val fixed_raw = Int.max (node_size template_limit fixed_node G.RawNodes,
        node_size template_limit fixed_node G.BinderInclusiveNodes)
      (* One upfront bound covers complete local laws, generated terms and
         this restricted beta/congruence traversal. It is deliberately a
         conservative finite fallback, not legacy cap/whole-DAG parity. *)
      val budget = Int.min (output_limit,template_limit)
      val _ = if budget > 200 andalso fixed_raw <= (budget-200) div 20
          andalso old_raw+1 <= ((budget-200-20*fixed_raw) div 20)
            div (old_raw+1) then () else reject "whole local work portfolio"
      val reserved = 200+20*fixed_raw+20*(old_raw+1)*(old_raw+1)
      fun inspect getter value = (active ();getter value)
      (* Record original annotation incidences before any supplied policy or
         INST_TYPE. For this alpha->int leaf map annotations cannot grow.
         Reserve future compile/construct/template/operand repetitions here;
         later callback metering consumes that reservation, never new quota. *)
      val type_inventory = ref 0
      fun inventory_type ty =
        let
          val _ = active ()
          val _ = if !type_inventory < budget-reserved then
              type_inventory := !type_inventory+1
            else reject "same local type/work portfolio exhausted"
        in if Type.is_vartype ty then () else
          List.app inventory_type (#2 (Type.dest_type ty)) end
      val type_nodes = G.reachable graph [source,fixed_node]
      val _ = List.app (fn node =>
        inventory_type (inspect (G.type_of graph) node)) type_nodes
      val _ = if !type_inventory <= (budget-reserved) div 64 then () else
        reject "prospective fixed-map type annotation portfolio"
      val type_fuel = ref (63 * !type_inventory)
      fun admit_type ty =
        let
          val _ = active ()
          val _ = if !type_fuel > 0 then type_fuel := !type_fuel-1 else
            reject "reserved local type annotation visits exceeded"
        in if Type.is_vartype ty then () else
          List.app admit_type (#2 (Type.dest_type ty)) end
      fun checked_type ty =
        (active ();admit_type ty;active ();check_type ty;active ())
      fun type_node node =
        let val ty = inspect (G.type_of graph) node
        in checked_type ty end
      val (operator,predicate) = case G.view graph source of
          G.Application pair => pair
        | _ => reject "not an owned local quantifier"
      val head = inspect (G.representative graph) operator
      val universal = inspect (Term.same_const head) boolSyntax.universal
      val existential = inspect (Term.same_const head) boolSyntax.existential
      val _ = if universal orelse existential then () else
        reject "not forall or exists"
      val fixed = if universal then HolSmtTheory.BAG_FORALL_TO_INT
        else HolSmtTheory.BAG_EXISTS_TO_INT
      val _ = if Portable.pointer_eq (P.closed_original law,fixed) then () else
        reject "not the exact original fixed BAG theorem"
      val predicate_type = inspect (G.type_of graph) predicate
      val (bag_type,result_type) = inspect Type.dom_rng predicate_type
      val (element,count_type) = inspect Type.dom_rng bag_type
      val _ = if Type.compare (element,intSyntax.int_ty) = EQUAL andalso
          Type.compare (count_type,numSyntax.num) = EQUAL andalso
          Type.compare (result_type,Type.bool) = EQUAL then () else
        reject "only original int->num bag predicates"
      val _ = List.app type_node type_nodes
      val actual = inspect (G.representative graph) source
      val actual_predicate = inspect (G.representative graph) predicate
      val (bag,body) = inspect Term.dest_abs actual_predicate
      fun restricted term =
        if inspect Term.is_abs term then
          reject "old body binder needs traversal"
        else if inspect Term.is_comb term then
          let val (f,x) = inspect Term.dest_comb term in
            if inspect Term.is_abs f then reject "old beta needs separate stage"
            else if Term.is_const f andalso
                (Term.same_const f boolSyntax.universal orelse
                 Term.same_const f boolSyntax.existential) then
              reject "nested quantifier needs carrier traversal"
            else (restricted f;restricted x)
          end
        else ()
      val _ = restricted body
      val free = inspect Term.free_vars actual
      val known = case G.free_variable_nodes graph source of SOME nodes => nodes
        | NONE => reject "missing original rigid free IDs"
      val _ = List.app (fn node =>
        case G.view graph node of G.Variable (G.RigidSource,_) => type_node node
          | G.Variable (G.Bound,_) => type_node node
          | _ => reject "unapproved original variable kind") known
      fun owned term = case List.find (fn node =>
          Term.aconv term (G.representative graph node)) known of
          SOME node => node | NONE => reject "original free ID missing"
      val bindings = List.map (fn term => (term,owned term)) free
      val _ = if length bindings = length known then () else
        reject "inexact original free-ID portfolio"
      val _ = List.app (fn (term,node) =>
        if G.scope_visible graph scope (G.node_scope graph node) andalso
            G.resolve_reference graph scope term node = node then () else
          reject "original variable ownership changed") bindings
      (* ONLY this fixed law's one alpha->int leaf map. No head-wide ISPEC,
         occurrence check, general unification or actual operand type INST. *)
      val proposition = inspect Thm.concl fixed
      val (p,_) = inspect boolSyntax.dest_forall proposition
      val (generic_bag,_) = inspect Type.dom_rng (inspect Term.type_of p)
      val (alpha,_) = inspect Type.dom_rng generic_bag
      val _ = if Type.is_vartype alpha then () else
        reject "fixed BAG theorem lost its one schematic carrier"
      val _ = checked_type alpha
      val _ = checked_type intSyntax.int_ty
      fun invoke work = (active ();let val answer = work () in
        active ();answer end)
      val typed = invoke (fn () => Thm.INST_TYPE
        [{redex = alpha,residue = intSyntax.int_ty}] fixed)
      val hole = Term.mk_var ("local_int_bag_predicate",predicate_type)
      val schematic = invoke (fn () => Thm.SPEC hole typed)
      val (_,right) = inspect boolSyntax.dest_eq (inspect Thm.concl schematic)
      val recipe = SmtLib_GraphScopedRecipe.compile
        {template = right,holes = [hole],
        template_limit = template_limit,check_type = checked_type}
      val temporary = G.new_scope graph scope bindings
      fun close () = G.close_scope graph temporary
      fun local_active () =
        (active ();G.validate_scope graph temporary)
      fun local_type ty =
        (local_active ();checked_type ty;local_active ())
      fun opened child =
        (local_active ();G.validate_scope graph child;scope_opened child;
         G.validate_scope graph child;local_active ())
      fun work () =
        let
          val _ = opened temporary
          val construction = R.construct graph temporary recipe
            {operands = [predicate],expected_result_type = SOME Type.bool,
             admission = {metric = metric,input_limit = input_limit,
               output_limit = output_limit,check_type = local_type,
               refuse = refuse},scope_opened = opened}
          val constructed = G.representative graph (#node construction)
          val specialized = invoke (fn () => Thm.SPEC actual_predicate typed)
          val (left,right) = inspect boolSyntax.dest_eq
            (inspect Thm.concl specialized)
          (* No old body redex/binder was admitted. The beta redexes here are
             the introduced predicate and Num(count-function) lambdas only.
             This bounded local tree traversal is not a DAG-wide optimizer. *)
          val fuel = ref reserved
          fun beta term =
            let
              val _ = if !fuel > 0 then fuel := !fuel-1 else
                reject "planned local beta work exhausted"
              fun equation proof = inspect boolSyntax.dest_eq
                (inspect Thm.concl proof)
            in if inspect Term.is_comb term then
              let
                val (f,x) = inspect Term.dest_comb term
                val combined = invoke (fn () => Thm.MK_COMB (beta f,beta x))
                val (_,current) = equation combined
              in if inspect Term.is_abs (inspect Term.rator current) then
                let val reduced = invoke (fn () => Thm.BETA_CONV current)
                    val (_,result) = equation reduced
                in invoke (fn () => Thm.TRANS combined
                  (Thm.TRANS reduced (beta result))) end
              else combined end
            else if inspect Term.is_abs term then
              let val (variable,body) = inspect Term.dest_abs term
              in invoke (fn () => Thm.ABS variable (beta body)) end
            else invoke (fn () => Thm.REFL term) end
          val source_beta = beta left
          val target_beta = beta constructed
          val (_,contracted_source) = inspect boolSyntax.dest_eq
            (inspect Thm.concl source_beta)
          val source_alignment = invoke
            (fn () => Thm.ALPHA actual contracted_source)
          val (_,result) = inspect boolSyntax.dest_eq
            (inspect Thm.concl target_beta)
          val target_binder = invoke (fn () => G.admit_binder graph temporary
            output_limit (inspect Term.rand result))
          val target_operator = G.constant graph temporary
            (inspect Term.rator result)
          val candidate = G.application graph temporary
            (target_operator,#node target_binder)
          val rehomed = invoke (fn () => G.rehome graph scope candidate)
          val _ = ignore (node_size output_limit (#node rehomed) metric)
          val theorem = invoke (fn () => Thm.TRANS (#bridge view)
            (Thm.TRANS source_alignment
              (Thm.TRANS (Thm.SYM source_beta)
                (Thm.TRANS specialized
                  (Thm.TRANS (Thm.ALPHA right constructed)
                    (Thm.TRANS target_beta
                      (Thm.TRANS (Thm.AP_TERM (Term.rator result)
                        (#bridge target_binder)) (#bridge rehomed))))))))
          val _ = Library.check_oracle_tags "GraphIntBagCarrier" "convert"
            theorem
          val _ = if null (Thm.hyp theorem) then () else
            reject "carrier equality retained hypotheses"
          val (from,to) = inspect boolSyntax.dest_eq (inspect Thm.concl theorem)
          val _ = if Portable.pointer_eq (from,G.representative graph original)
              andalso Portable.pointer_eq
                (to,G.representative graph (#node rehomed)) then () else
            reject "original/result endpoint identity changed"
          val _ = if Listsort.sort Int.compare
              (List.map G.node_id (Option.valOf
                (G.free_variable_nodes graph (#node rehomed)))) =
              Listsort.sort Int.compare (List.map G.node_id known) then () else
            reject "target changed original free IDs"
          val _ = active ()
        in {source = original,target = #node rehomed,theorem = theorem} end
    in work () before close ()
      handle error => ((close () handle _ => ());raise error) end
end
