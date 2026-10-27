(* Task39: structured operators must survive bounded variable naming. *)
structure SmtReplayStructuredTests =
struct
  open HolKernel Parse boolLib bossLib
  structure H = SmtReplayArithmeticTests
  structure G = SmtReplayGraph
  structure A = SmtReplayArithmetic
  structure W = SmtReplayInvocationWork
  structure ZR = Z3_GraphProofReplay
  val limit = H.limit
  val require = H.require
  fun exact term hypotheses theorem =
    (H.exact term hypotheses theorem;
     require "structured theorem acquired axiom tags"
       (null (Tag.axioms_of (Thm.tag theorem))))
  val with_graph = H.with_graph
  val import = H.import

  (* A rejection must not be an accidental quota failure or missing dispatch.
     Every negative below has a positive through the same producer. *)
  fun declines action =
    (case action () of NONE => true | SOME _ => false)
    handle Conv.UNCHANGED => true
      | HolSatLib.SAT_cex _ => true
      | Feedback.HOL_ERR detail =>
          if SmtResource.is_resource_gate detail then
            raise Feedback.HOL_ERR detail
          else true

  val option_ty = ``:bool option``
  val some = ``SOME : bool -> bool option``
  val none = ``NONE : bool option``
  fun tester constructor value =
    SmtDatatypeProve.datatype_tester_term option_ty constructor value

  fun schemas () = with_graph (fn graph => fn scope =>
    let
      val arrays =
        [``((i:bool) =+ (p:bool)) a i = p``,
         ``~((i:bool) = j) ==> (i =+ (p:bool)) a j = a j``,
         ``((i:bool) =+ (q:bool)) ((i =+ p) a) = (i =+ q) a``,
         ``((i:bool) =+ (a i:bool)) a = a``]
      val datatypes =
        [``(SOME (p:bool) = SOME q) = (p = q)``,
         ``(SOME (p:bool) = NONE) = F``,
         ``THE (SOME (p:bool)) = p``,
         ``THE (SOME (I (p:bool))) = p``,
         ``THE (SOME ((n:num) + 0)) = n``,
         ``(SOME T = SOME F) = F``,
         ``THE (SOME T) = T``,
         ``FST ((p:bool),(q:bool)) = p``,
         ``HD ((p:bool)::ps) = p``,
         tester some ``SOME (p:bool)``,
         boolSyntax.mk_neg (tester none ``SOME (p:bool)``),
         tester none none]
      fun check prove original =
        let
          val calls = ref 0
          fun procedure [named] =
                let val _ = calls := !calls+1
                    val (substitution,types) =
                      Term.match_term original named
                    val _ = require "structured source variable reached worker"
                      (H.disjoint [original] [named])
                    val _ = require "structured operator/literal was hidden"
                      (null types andalso List.all
                        (fn {residue,...} => Term.is_var residue) substitution)
                in prove named end
            | procedure _ = raise Fail "structured schema arity"
          val result = A.prove graph scope
            {inputs=[import graph scope original],template_limit=limit,
             observe=fn _ => (),procedure=procedure}
          val _ = require "structured worker retried or bypassed" (!calls=1)
          val expected = prove original
          val _ = require "structured transport changed full oracle/axiom tags"
            (Tag.dest_tag (Thm.tag (#theorem result)) =
             Tag.dest_tag (Thm.tag expected))
        in exact original [] (#theorem result) end
      val _ = List.app (check SmtArrayProve.array_prove) arrays
      val _ = List.app (check SmtDatatypeProve.datatype_prove) datatypes
      fun rejects prove term = require "false structured schema accepted"
        (declines (fn () =>
          (check prove term;SOME ())))
      val _ = rejects SmtArrayProve.array_prove
        ``((i:bool) =+ (p:bool)) a i = ~p``
      val _ = rejects SmtDatatypeProve.datatype_prove
        ``SOME (p:bool) = NONE``
      val _ = rejects SmtDatatypeProve.datatype_prove
        ``SOME (p:bool) = SOME (~p)``
    in () end)

  fun tester_validation () =
    let
      val value = ``d:bool option``
      val _ = List.app (fn constructor =>
        let val result = tester constructor value
        in require "tester lost scrutinee or Boolean result"
          (Term.type_of result = Type.bool andalso
           HOLset.equal (Term.FVL [result] Term.empty_tmset,
             Term.FVL [value] Term.empty_tmset)) end) [some,none]
      (* Compare the actual canonical case syntax as well as its truth. *)
      val _ = require "SOME tester changed its canonical case encoding"
        (tester some value ~~ ``case (d:bool option) of
                                    NONE => F | SOME p => T``)
      val _ = require "NONE tester changed its canonical case encoding"
        (tester none value ~~ ``case (d:bool option) of
                                    NONE => T | SOME p => F``)
      val _ = List.app (fn (constructor,scrutinee) =>
        let val term = tester constructor scrutinee
        in exact term [] (SmtDatatypeProve.datatype_prove term) end)
        [(some,``SOME (p:bool)``),(none,none)]
      fun rejects constructor scrutinee =
        require "malformed datatype tester admitted"
          (declines (fn () => SOME (tester constructor scrutinee)))
    in
      rejects ``CONS : bool -> bool list -> bool list`` value;
      rejects ``SOME : num -> num option`` value;
      rejects ``NONE : num option`` value;
      rejects some ``d:num option``;
      rejects none ``d:bool list``
    end

  fun graph_operators () = with_graph (fn graph => fn scope =>
    let
      fun app f x = G.application graph scope (f,x)
      fun constant t = G.constant graph scope t
      fun binary t x y = app (app (constant t) x) y
      val iff = binary (Term.rator (Term.rator ``(p:bool) = q``))
      val eq = binary (Term.rator (Term.rator
        ``(x:bool option) = y``))
      val p = ``structured_field:bool``
      val i = ``structured_index:bool``
      val rigid = G.variable graph scope G.RigidSource p
      val other = G.variable graph scope G.Generated p
      val index = G.variable graph scope G.RigidSource i
      val other_index = G.variable graph scope G.Generated i
      val _ = require "structured identity fixture is not same-native"
        (rigid <> other andalso index <> other_index andalso
         G.representative graph rigid ~~ G.representative graph other
         andalso G.representative graph index ~~
           G.representative graph other_index)
      val array = import graph scope ``a:bool -> bool``
      val update = Term.rator (Term.rator (Term.rator
        ``((i:bool) =+ (p:bool)) a``))
      val stored = app (binary update index rigid) array
      val select = app stored index
      val constructor = constant some
      val good_dt = iff (eq (app constructor rigid) (app constructor other))
        (iff rigid other)
      val bad_dt = eq (app constructor rigid) (app constructor other)
      val proof : Z3_GraphProofParser.proof =
        {steps=Redblackmap.mkDict Z3_GraphProofParser.compare_id,
         root=Z3_GraphProofParser.Anonymous 0,vars=[],
         z3_version="4.15.3",close=fn () => ()}
      fun request name theory target : ZR.local_request =
        {rule=valOf (Z3_Proof.lookup_rule "4.15.3" name),
         metadata=Option.map (fn theory =>
           Z3_Proof.mk_th_lemma_metadata (theory,NONE,[])) theory,
         target=target,premises=[],arguments=[],law=target}
      fun compatibility request = Option.map
        (fn theorem => {definitions=[],theorem=theorem})
        (Z3_ProofReplay.graph_bounded_local_law graph [] proof request)
      fun recorded request =
        Z3_ProofReplay.graph_bounded_recorded_local_law
          graph scope limit [] proof request
      fun check produce (name,theory,good,bads) =
        (case produce (request name theory good) of
           NONE => raise Fail ("valid structured Z3 law declined: " ^ name)
         | SOME {definitions,theorem} =>
             (require "structured law invented definitions" (null definitions);
              exact (G.representative graph good) [] theorem);
         List.app (fn bad => require
           ("structured Z3 merged same-native IDs: " ^ name)
           (declines (fn () => produce (request name theory bad)))) bads)
      val cases =
        [("th-lemma-array",SOME "array",iff select rigid,
          [iff select other,iff (app stored other_index) rigid]),
         ("th-lemma-datatype",SOME "datatype",good_dt,[bad_dt]),
         ("rewrite",NONE,iff select rigid,[iff select other]),
         ("rewrite",NONE,good_dt,[bad_dt])]
    in List.app (fn produce => List.app (check produce) cases)
         [compatibility,recorded] end)

  (* This existing paired harness also checks recorded definition endpoints,
     flexible/rigid authority and both orders of same-native declarations. *)
  fun generic_authority () = List.app H.z3_generic_identity_type
    [(``structured_array:bool -> bool``,``(K F):bool -> bool``),
     (``structured_option:bool option``,none)]

  fun cpc_cases () =
    let
      val select = ``((i:bool) =+ (p:bool)) a i``
      val read = boolSyntax.mk_eq (select,``p:bool``)
      val injectivity = ``(SOME (p:bool) = SOME q) = (p = q)``
      fun both goal assumptions rule args = List.app (fn declared =>
        H.cpc goal assumptions rule args declared
        handle error => raise Fail ("structured CPC " ^ rule ^ " " ^
          Bool.toString declared ^ ": " ^ General.exnMessage error))
        [true,false]
      val _ = both read [] "arrays_read_over_write_1" [select]
      val _ = both ``((i:bool) =+ (p:bool)) a j = a j``
        [``~((i:bool) = j)``] "arrays_read_over_write"
        [``((i:bool) =+ (p:bool)) a j``]
      val _ = both injectivity [] "dt-cons-eq" [injectivity]
      val _ = both ``(SOME (p:bool) = NONE) = F`` [] "dt-cons-eq"
        [``(SOME (p:bool) = NONE) = F``]
      val _ = both ``THE (SOME (p:bool)) = p`` []
        "dt-collapse-selector" [``THE (SOME (p:bool)) = p``]
      val _ = both ``THE (SOME T) = T`` [] "evaluate" [``THE (SOME T)``]
      val _ = both ``((a:bool -> bool) = a) = T`` [] "eq-refl"
        [``a:bool -> bool``]
      (* Selector normalization forces generic trans off exact IDs. *)
      val _ = H.cpc ``(d:bool option) = e``
        [``(d:bool option) = SOME (THE (SOME p))``,
         ``SOME (p:bool) = e``] "trans" [] true
      val _ = require "false CPC store result accepted"
        (declines (fn () => (H.cpc
          ``((i:bool) =+ (p:bool)) a i = ~p`` []
          "arrays_read_over_write_1" [select] true;SOME ())))
      val _ = require "false CPC constructor result accepted"
        (declines (fn () => (H.cpc ``SOME (p:bool) = NONE`` []
          "dt-cons-eq" [``SOME (p:bool) = NONE``] true;SOME ())))
    in () end

  (* Use the real local worker inside A, not a Boolean stand-in. Distinct
     graph declarations deliberately have identical native representatives. *)
  fun cpc_identities () = with_graph (fn graph => fn scope =>
    let
      val native = ``structured_cpc:bool``
      val left = G.variable graph scope G.RigidSource native
      val right = G.variable graph scope G.Generated native
      fun app f x = G.application graph scope (f,x)
      val constructor = G.constant graph scope some
      val equality = G.constant graph scope
        (Term.rator (Term.rator ``(x:bool option) = y``))
      fun goal right = app (app equality (app constructor left))
        (app constructor right)
      fun run rule original argument =
        let val result = A.prove graph scope
              {inputs=[original,argument],template_limit=limit,
               observe=fn _ => (),
               procedure=fn [term,arg] =>
                 let
                   val located = {term=term,
                     provenance=CPC_Proof.UnavailableProvenance "schema"}
                   val step:CPC_Proof.step =
                     {id="@structured",rule=valOf
                        (CPC_Proof.lookup_rule "1.3.4" rule),
                      premises=[],conclusion=SOME located,
                      args=[{term=arg,provenance=
                        CPC_Proof.UnavailableProvenance "schema argument"}]}
                 in #1 (CPC_ProofReplay.graph_bounded_worker [] (step,[])) end
                 | _ => raise Fail "CPC structured arity"}
        in exact (G.representative graph original) [] (#theorem result) end
      val _ = run "dt-cons-eq" (goal left) (goal left)
      val _ = require "CPC local datatype worker merged graph declarations"
        (declines (fn () =>
          (run "dt-cons-eq" (goal right) (goal right);SOME ())))
      val index = import graph scope ``i:bool``
      val array = import graph scope ``a:bool -> bool``
      val update = G.constant graph scope (Term.rator (Term.rator
        (Term.rator ``((i:bool) =+ (p:bool)) a``)))
      val selected = app (app (app (app update index) left) array) index
      val bool_eq = G.constant graph scope
        (Term.rator (Term.rator ``(p:bool) = q``))
      fun read value = app (app bool_eq selected) value
      val _ = run "arrays_read_over_write_1" (read left) selected
    in require "CPC local array worker merged graph declarations"
         (declines (fn () =>
           (run "arrays_read_over_write_1" (read right) selected;SOME ())))
    end)

  fun cpc_splits () =
    let
      fun check value =
        let val ty = Term.type_of value
            val testers = List.map (fn constructor =>
              SmtDatatypeProve.datatype_tester_term ty constructor value)
              (SmtDatatypeProve.constructors_of ty)
            val goal = boolSyntax.list_mk_disj testers
            val _ = H.cpc goal [] "dt_split" [value] true
            (* Retain a direct binder-result control as well as the complete
               inferred enumeration certificate below. *)
            val _ = with_graph (fn graph => fn scope =>
              let val calls = ref 0
                  val result = A.prove_admitted graph scope
                    {inputs=[import graph scope value],template_limit=limit,
                     observe=fn _ => (),procedure=fn admit => fn [term] =>
                       (calls := !calls+1;
                        #1 (CPC_ProofReplay.graph_bounded_worker_with_admission
                          admit []
                          ({id="@split",rule=valOf (CPC_Proof.lookup_rule
                              "1.3.4" "dt_split"),premises=[],conclusion=NONE,
                            args=[{term=term,provenance=
                              CPC_Proof.AtomicProvenance}]},[])))
                       | _ => raise Fail "dt_split input arity"}
              in require "inferred split retried its worker" (!calls=1);
                 exact goal [] (#theorem result) end)
        in () end
    in List.app check [``d:bool option``,``ds:bool list``] end

  (* A valid inferred split through graph assembly and final Source closure.
     Its canonical tester disjunction is one atomic literal, as returned by
     the actual worker, on BOTH sides of the final resolution. *)
  fun inferred_split_graph () =
    let
      val value = ``structured_split:smt_light``
      val goal = SmtDatatypeProve.datatype_split_target (fn _ => ()) value
      fun worker (step:CPC_Proof.step,inputs) =
        let
          val _ = require "split conclusion was supplied"
            (not (Option.isSome (#conclusion step)))
          val _ = require "split acquired premises" (null inputs)
          val argument = #term (hd (#args step))
          val result as (theorem,located) =
            CPC_ProofReplay.graph_bounded_worker [] (step,inputs)
          val _ = exact (SmtDatatypeProve.datatype_split_target
            (fn _ => ()) argument) [] theorem
          val _ = require "inferred split lost atomic provenance"
            (case #provenance located of
               CPC_Proof.AtomicProvenance => true | _ => false)
        in result end
    in H.cpc_arguments_using limit worker goal [] "dt_split"
      [H.Object value] false end

  fun split_admission () =
    let
      fun check cap nodes value =
        let
          val completed = ref false
          val reached_worker = ref false
          val expected = SmtDatatypeProve.datatype_split_target
            (fn _ => ()) value
          val _ = require "split admission fixture metric changed"
            (Term.term_size expected = nodes andalso nodes > cap)
          fun refused action =
            ((action ();false) handle Feedback.HOL_ERR detail =>
              String.isSubstring "operator schema exceeds local admission"
                (Feedback.message_of detail))
          val _ = with_graph (fn graph => fn scope =>
            require "inferred split was proved before target admission"
              (refused (fn () => ignore (A.prove_admitted graph scope
                {inputs=[import graph scope value],template_limit=cap,
                 observe=fn _ => (),procedure=fn admit => fn [term] =>
                   let val result = #1
                         (CPC_ProofReplay.graph_bounded_worker_with_admission
                           admit []
                           ({id="@admission",rule=valOf
                              (CPC_Proof.lookup_rule "1.3.4" "dt_split"),
                             premises=[],conclusion=NONE,
                             args=[{term=term,provenance=
                               CPC_Proof.AtomicProvenance}]},[]))
                   in completed := true;result end
                   | _ => raise Fail "split admission arity"}))))
          val _ = require "over-limit split worker completed" (not (!completed))
          (* The graph engine must protect even a supplied ordinary worker;
             do not rely on that worker adopting a particular prover API. *)
          val _ = require "graph split admission happened after callback"
            (refused (fn () => H.cpc_arguments_using cap
              (fn _ => (reached_worker := true;
                raise Fail "unadmitted split reached ordinary worker"))
              boolSyntax.T [] "dt_split" [H.Object value] false))
        in require "unadmitted split entered ordinary worker"
             (not (!reached_worker)) end
      val _ = check 16 19 ``d:bool option``
      val _ = Datatype [QUOTE ("structured_admission_enum = " ^
        String.concatWith " | " (List.tabulate (64,fn i =>
          "StructuredAdmission" ^ Int.toString i)))]
      val ty = Type.mk_type ("structured_admission_enum",[])
      val value = Term.mk_var ("d",ty)
      val _ = check 8192 8573 value
      (* A large declaration bundle is NOT a reason to refuse small laws. *)
      val constructor = hd (SmtDatatypeProve.constructors_of ty)
      val goal = boolSyntax.mk_eq (constructor,constructor)
      val theorem = SmtDatatypeProve.datatype_prove_with_admission
        (A.new_term_check {limit=32,observe=fn () => ()}) goal
      val _ = exact goal [] theorem
      val _ = H.cpc_arguments_using_admitted 256
        (fn admit => CPC_ProofReplay.graph_bounded_worker_with_admission
          admit []) goal [] "dt-cons-eq" [H.Object goal] true
      (* Larger existing caller allowances must still work; never turn the
         8192 regression into a blanket refusal of this datatype. *)
      val split = SmtDatatypeProve.datatype_split_target (fn _ => ()) value
      val cap = Term.term_size split
      val theorem = #1 (CPC_ProofReplay.graph_bounded_worker_with_admission
        (A.new_term_check {limit=cap,observe=fn () => ()}) []
        ({id="@fitting",rule=valOf
           (CPC_Proof.lookup_rule "1.3.4" "dt_split"),
          premises=[],conclusion=NONE,
          args=[{term=value,provenance=CPC_Proof.AtomicProvenance}]},[]))
    in exact split [] theorem end

  fun admission_first_error () =
    let
      val goal = ``~((xs:bool list) = T::xs)``
      val (size_fn,_) = TypeBase.size_of ``:bool list``
      val genuine = A.new_term_check {limit=limit,observe=fn () => ()}
      val stopped = ref false
      fun check term =
        if !stopped then raise Fail "datatype retried after admission failure"
        else if term ~~ size_fn then
          (stopped := true;
           raise Feedback.mk_HOL_ERR "Task39" "size-pattern" "first error")
        else genuine term
      val preserved =
        ((ignore (#acyclicity (SmtDatatypeProve.checked_procedures check)
            goal);false)
         handle Feedback.HOL_ERR detail =>
           Feedback.top_structure_of detail = "Task39" andalso
           Feedback.message_of detail = "first error")
    in require "datatype swallowed its first pattern admission exception"
         (!stopped andalso preserved) end

  fun admission_factories () = with_graph (fn graph => fn scope =>
    let
      val sources = SmtReplaySource.new graph scope limit
        {goal=boolSyntax.T,assumptions=[]}
      val work = W.begin graph scope sources
        {limits={input_limit=limit,output_limit=limit,template_limit=limit},
         work_limit=10000000}
      val calls = ref 0
      fun forbidden _ = (calls := !calls+1;raise Fail "premature worker factory")
      val charged_before = #charged (W.audit work)
      val rejected = with_graph (fn other => fn root =>
        let val foreign = SmtReplaySource.new other root limit
              {goal=boolSyntax.T,assumptions=[]}
        in
          ((ignore (CPC_GraphProofReplay.prove_admitted_using
             {graph=other,scope=root,sources=foreign,preprocessing=NONE,
              work=SOME work,proof={cvc_version="1.3.4",commands=[]},
              ordinary_limit=limit,template_limit=limit,worker=forbidden,
              clause_worker=SOME forbidden,force_worker=NONE});false)
           handle Feedback.HOL_ERR detail =>
             Feedback.message_of detail = "different original Sources")
        end)
      val after = W.audit work
    in require "admission factory ran before owned frame validation"
         (rejected andalso !calls=0 andalso #retired after andalso
          #charged after = charged_before) end)

  fun cpc_annotations () =
    let
      fun shared 0 = Type.bool
        | shared n = let val ty = shared (n-1)
                     in Type.mk_type ("fun",[ty,ty]) end
      fun operand depth = Term.mk_var ("structured_typed_array",
        Type.mk_type ("fun",[Type.bool,shared depth]))
      fun goal term = boolSyntax.mk_eq
        (boolSyntax.mk_eq (term,term),boolSyntax.T)
      val small = operand 10
      val _ = H.cpc (goal small) [] "eq-refl" [small] false
      val intermediate = operand 12
      (* The old caller gate bounds root Types, not every annotation. Keep
         both that refusal AND the formerly admitted buried-Type case. *)
      val root_refused =
        ((H.cpc_arguments_using limit
           (fn _ => raise Fail "oversized root Type reached callback")
           (goal intermediate) [] "eq-refl" [H.Object intermediate] false;
          false)
         handle Feedback.HOL_ERR detail =>
           Feedback.message_of detail = "ordinary type exceeds caller limit")
      val _ = require "structured naming increased the old root Type cap"
        root_refused
      val _ = H.cpc (goal intermediate) [] "evaluate"
        [boolSyntax.mk_eq (intermediate,intermediate)] false
      val large = operand 20
      val refused =
        ((H.cpc_arguments_using limit
           (fn _ => raise Fail "unadmitted structured Type reached callback")
           (goal large) [] "evaluate"
           [H.Object (boolSyntax.mk_eq (large,large))] false;false)
         handle Feedback.HOL_ERR detail =>
           SmtResource.is_resource_gate detail)
      val _ = require "structured CPC Type admission did not precede callback"
        refused
      fun datatype_operand depth = Term.mk_var ("structured_typed_option",
        optionSyntax.mk_option (shared depth))
      val small_option = datatype_operand 10
      val _ = H.cpc (goal small_option) [] "eq-refl" [small_option] false
      val large_option = datatype_operand 20
      val datatype_refused =
        ((H.cpc_arguments_using limit
           (fn _ => raise Fail "unadmitted datatype Type reached callback")
           (goal large_option) [] "evaluate"
           [H.Object (boolSyntax.mk_eq (large_option,large_option))] false;
          false)
         handle Feedback.HOL_ERR detail =>
           SmtResource.is_resource_gate detail)
    in require "datatype classification expanded an unadmitted annotation"
         datatype_refused end

  (* Registered by Unittest; its testutils runner owns reporting. *)
  fun run () =
    (schemas ();tester_validation ();graph_operators ();
     generic_authority ();cpc_cases ();cpc_identities ();
     cpc_splits ();inferred_split_graph ();split_admission ();
     admission_first_error ();admission_factories ();cpc_annotations ())
end
