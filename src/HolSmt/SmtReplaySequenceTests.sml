(* Task40: genuine Seq syntax, declaration identity and local admission. *)
structure SmtReplaySequenceTests =
struct
  open HolKernel Parse boolLib bossLib
  open HolSmtTheory
  structure H = SmtReplayArithmeticTests
  structure G = SmtReplayGraph
  structure A = SmtReplayArithmetic
  structure R = SmtReplayRules
  structure ZR = Z3_GraphProofReplay
  val limit = SmtReplayArithmeticTests.limit
  val require = H.require
  val with_graph = H.with_graph
  val import = H.import

  fun exact term hypotheses theorem =
    (H.exact term hypotheses theorem;
     require "sequence theorem acquired axiom tags"
       (null (Tag.axioms_of (Thm.tag theorem))))
  fun same_tags expected actual = require "sequence full tags changed"
    (Tag.dest_tag (Thm.tag expected) = Tag.dest_tag (Thm.tag actual))
  fun declines action =
    (case action () of NONE => true | SOME _ => false)
    handle Conv.UNCHANGED => true
      | HolSatLib.SAT_cex _ => true
      | Feedback.HOL_ERR detail =>
          if SmtResource.is_resource_gate detail then
            raise Feedback.HOL_ERR detail
          else true

  (* Each original operator, numeral and compound shared operand survives;
     only free variables may change. Check the native positive FIRST: this
     suite tests transport, not an enlargement of the Seq proof fragment. *)
  val schemas =
    [(``(&(LENGTH ((xs:bool list) ++ ys)):int) =
          &(LENGTH xs) + &(LENGTH ys)``, ``(xs:bool list) ++ ys``),
     (``smt_seq_nth ([p]:bool list) 0 = p``, ``[p]:bool list``),
     (``smt_seq_indexof (xs:bool list) ys (-1) = -1``,
       ``xs:bool list``),
     (``smt_seq_update ([p]:bool list) 0 [q] = [q]``,
       ``[q]:bool list``),
     (``smt_seq_extract ([p]:bool list) 0 1 = [p]``,
       ``[p]:bool list``)]

  fun schemas_and_sharing () = with_graph (fn graph => fn scope =>
    let
      fun check (original,operand) =
        let
          val native = SmtSeqProve.seq_prove original
          val _ = exact original [] native
          val goal = import graph scope original
          val shared = import graph scope operand
          val calls = ref 0
          fun shape source named =
            let val (substitution,types) = Term.match_term source named
            in require "sequence operator, literal or Type was hidden"
              (null types andalso List.all
                (fn {residue,...} => Term.is_var residue) substitution)
            end
          val result = A.prove_admitted graph scope
            {inputs=[goal,goal,shared,shared],template_limit=limit,
             observe=fn _ => (),procedure=fn admit => fn terms =>
               case terms of [left,right,child,again] =>
                 (calls := !calls+1;
                  require "shared sequence roots were rebuilt separately"
                    (Portable.pointer_eq (left,right) andalso
                     Portable.pointer_eq (child,again));
                  shape original left;shape operand child;
                  require "source variables reached sequence worker"
                    (H.disjoint [original,operand] terms);
                  require "shared child lost its worker identity"
                    (Portable.pointer_eq
                      (HolKernel.find_term (fn tm => tm ~~ child) left,
                       child));
                  SmtSeqProve.seq_prove_with_admission admit left)
               | _ => raise Fail "sequence schema arity"}
          val theorem = #theorem result
        in require "sequence worker was retried or bypassed" (!calls=1);
           exact original [] theorem;same_tags native theorem end
    in List.app check schemas end)

  fun false_obligations () = with_graph (fn graph => fn scope =>
    let
      val bads =
        [``([]:bool list) ++ xs = T::xs``,
         ``smt_seq_nth ([p]:bool list) 0 = ~p``,
         ``smt_seq_indexof (xs:bool list) ys (-1) = 0``,
         ``smt_seq_update ([p]:bool list) 0 [q] = [~q]``,
         ``smt_seq_extract ([p]:bool list) 0 1 = [~p]``]
      fun check goal = require "false named sequence obligation accepted"
        (declines (fn () => SOME (A.prove_admitted graph scope
          {inputs=[import graph scope goal],template_limit=limit,
           observe=fn _ => (),procedure=fn admit => fn [term] =>
             SmtSeqProve.seq_prove_with_admission admit term
             | _ => raise Fail "false sequence arity"})))
    in List.app check bads end)

  fun contextual () = with_graph (fn graph => fn scope =>
    let
      val premise = ``(p:bool) = q``
      val goal = ``smt_seq_nth ([p]:bool list) 0 = q``
      val native = SmtSeqProve.seq_contextual_prove [premise] goal
      val _ = exact goal [premise] native
      val admitted = SmtSeqProve.seq_contextual_prove_with_admission
        (A.new_term_check {limit=limit,observe=fn () => ()}) [premise] goal
      val _ = exact goal [premise] admitted
      val _ = same_tags native admitted
      val result = A.prove_admitted graph scope
        {inputs=map (import graph scope) [goal,premise],template_limit=limit,
         observe=fn _ => (),procedure=fn admit => fn [target,assumption] =>
           (require "context source variables reached sequence worker"
              (H.disjoint [goal,premise] [target,assumption]);
            let val theorem =
                  SmtSeqProve.seq_contextual_prove_with_admission
                    admit [assumption] target
                val _ = exact target [assumption] theorem
            (* A exports closed laws; contextual Hyp must be discharged. *)
            in Thm.DISCH assumption theorem end)
           | _ => raise Fail "sequence context arity"}
      val theorem = #theorem result
    in exact (boolSyntax.mk_imp (premise,goal)) [] theorem;
       same_tags native theorem end)

  (* Actual Z3 local producers AND the native CPC named worker, with
     same-native/different-ID controls. No native representative comparison
     can distinguish the good endpoint from the corresponding bad one. *)
  fun graph_handlers () = with_graph (fn graph => fn scope =>
    let
      fun app f x = G.application graph scope (f,x)
      fun constant tm = G.constant graph scope tm
      fun apply tm args = List.foldl (fn (x,f) => app f x)
        (constant tm) args
      val p = ``sequence_identity:bool``
      val left = G.variable graph scope G.RigidSource p
      val right = G.variable graph scope G.Generated p
      val xs = ``sequence_identity_xs:bool list``
      val source = G.variable graph scope G.RigidSource xs
      val other = G.variable graph scope G.Generated xs
      val _ = require "sequence identity controls need distinct IDs"
        (left <> right andalso source <> other andalso
         G.representative graph left ~~ G.representative graph right andalso
         G.representative graph source ~~ G.representative graph other)
      val empty = import graph scope ``[]:bool list``
      val zero = import graph scope ``0:int``
      val one = import graph scope ``1:int``
      val cons = Term.rator (Term.rator ``(p:bool)::ps``)
      fun unit x = apply cons [x,empty]
      fun eq x y = apply (Term.rator (Term.rator
        (boolSyntax.mk_eq (G.representative graph x,
                          G.representative graph y)))) [x,y]
      val append = Term.rator (Term.rator ``(xs:bool list) ++ ys``)
      val nth = Term.rator (Term.rator
        ``smt_seq_nth (xs:bool list) i``)
      val indexof = Term.rator (Term.rator (Term.rator
        ``smt_seq_indexof (xs:bool list) ys i``))
      val update = Term.rator (Term.rator (Term.rator
        ``smt_seq_update (xs:bool list) i ys``))
      val extract = Term.rator (Term.rator (Term.rator
        ``smt_seq_extract (xs:bool list) i n``))
      val joined = apply append [empty,source]
      val selected = apply nth [unit left,zero]
      val updated = apply update [unit left,zero,unit left]
      val extracted = apply extract [unit left,zero,one]
      val cases =
        [(eq joined source,eq joined other),
         (eq selected left,eq selected right),
         (eq (apply indexof [unit left,unit left,zero]) zero,
          eq (apply indexof [unit left,unit right,zero]) zero),
         (eq updated (unit left),eq updated (unit right)),
         (eq extracted (unit left),eq extracted (unit right))]
      val proof:Z3_GraphProofParser.proof =
        {steps=Redblackmap.mkDict Z3_GraphProofParser.compare_id,
         root=Z3_GraphProofParser.Anonymous 0,vars=[],
         z3_version="4.15.3",close=fn () => ()}
      fun request name target : ZR.local_request =
        {rule=valOf (Z3_Proof.lookup_rule "4.15.3" name),
         metadata=if name="th-lemma-seq" then SOME
           (Z3_Proof.mk_th_lemma_metadata ("seq",NONE,[])) else NONE,
         target=target,premises=[],arguments=[],law=target}
      fun compatibility request = Option.map
        (fn theorem => {definitions=[],theorem=theorem})
        (Z3_ProofReplay.graph_bounded_local_law graph [] proof request)
      fun recorded request =
        Z3_ProofReplay.graph_bounded_recorded_local_law
          graph scope limit [] proof request
      fun z3 produce name (good,bad) =
        let
          val original = G.representative graph good
          val native = SmtSeqProve.seq_prove original
          val _ = exact original [] native
          val _ = case produce (request name good) of
              NONE => raise Fail ("valid sequence Z3 law declined: " ^ name)
            | SOME {definitions,theorem} =>
                (require "sequence Z3 law invented definitions"
                   (null definitions);
                 exact original [] theorem;same_tags native theorem)
        in require ("sequence Z3 merged declaration IDs: " ^ name)
          (declines (fn () => produce (request name bad))) end
      fun cpc target =
        let val result = A.prove_admitted graph scope
              {inputs=[target,target],template_limit=limit,
               observe=fn _ => (),procedure=fn admit => fn [term,arg] =>
                 let
                   val _ = require "CPC sequence target/argument lost sharing"
                     (Portable.pointer_eq (term,arg))
                   val located = {term=term,provenance=
                     CPC_Proof.UnavailableProvenance "sequence identity"}
                   val step:CPC_Proof.step =
                     {id="@seq",rule=valOf (CPC_Proof.lookup_rule
                        "1.3.4" "seq-eval-op"),premises=[],
                      conclusion=SOME located,args=[located]}
                 in #1
                   (CPC_ProofReplay.graph_bounded_worker_with_admission
                     admit [] (step,[])) end
                 | _ => raise Fail "sequence CPC identity arity"}
            val original = G.representative graph target
            val theorem = #theorem result
        in exact original [] theorem;
           same_tags (SmtSeqProve.seq_prove original) theorem end
      val _ = List.app (fn produce => List.app (fn name =>
        List.app (z3 produce name) cases) ["th-lemma-seq","rewrite"])
        [compatibility,recorded]
    in List.app (fn (good,bad) =>
      (cpc good;require "CPC sequence worker merged declaration IDs"
        (declines (fn () => (cpc bad;SOME ()))))) cases end)

  (* Parsed Z3 assembly retains the original hypotheses, not just a local
     implication. The symbolic singleton also rules out ground-only replay. *)
  fun parsed_z3 () =
    let
      val goal = ``smt_seq_nth ([p]:bool list) 0 = q``
      val assumptions = [``(p:bool) = q``]
      val native = SmtSeqProve.seq_contextual_prove assumptions goal
    in Z3_CompactReplayTests.with_proof
      [("p",``p:bool``),("q",``q:bool``)]
      "((proof ((_ th-lemma seq) (asserted (= p q)) \
      \(= (seq.nth (seq.unit p) 0) q))))"
      (fn graph => fn scope => fn proof =>
        let val theorem = Z3_CompactReplayTests.replay graph scope proof
              limit (Z3_CompactReplayTests.fixed graph proof)
        in exact goal assumptions theorem;same_tags native theorem end)
    end

  (* Complete CPC graph assembly: exact Source Goal/Hyp and both omitted and
     declared endpoints. The helper additionally checks variable-only shape,
     argument roles, source disjointness and exactly one selected callback. *)
  fun cpc_cases () =
    let
      fun check native goal assumptions rule arguments declared =
        H.cpc_arguments_using_admitted limit
          (fn admit => fn input =>
            let val result as (theorem,_) =
                  CPC_ProofReplay.graph_bounded_worker_with_admission
                    admit [] input
            in same_tags native theorem;
               require "CPC sequence worker acquired axioms"
                 (null (Tag.axioms_of (Thm.tag theorem)));result end)
          goal assumptions rule arguments declared
      fun both goal rule args =
        let val native = SmtSeqProve.seq_prove goal
            val _ = exact goal [] native
        in List.app (check native goal [] rule (map H.Object args))
          [true,false] end
      val _ = List.app (fn (goal,_) =>
        both goal "seq-eval-op" [goal]) schemas
      val _ = both ``smt_seq_at ([p]:bool list) 0 =
                       smt_seq_extract [p] 0 1``
        "str-at-elim" [``[p]:bool list``,``0:int``]
      val full =
        ``smt_seq_extract (xs:bool list) 0 (&(LENGTH xs)) = xs``
      val full_premise =
        ``(&(LENGTH (xs:bool list)):int) = &(LENGTH xs)``
      val _ = List.app (check (SmtSeqProve.seq_prove full) full
        [full_premise] "str-substr-full-eq"
        [H.Object ``xs:bool list``,
         H.Object ``&(LENGTH (xs:bool list)):int``]) [true,false]
      val assoc = ``((xs:bool list) ++ ys) ++ zs = xs ++ (ys ++ zs)``
      val _ = both assoc "aci_norm" [assoc]
      val _ = List.app (fn declared =>
        check (SmtSeqProve.seq_prove assoc) assoc [] "str"
          [H.Object assoc] declared) [true,false]
      val context = [``(p:bool) = q``]
      val contextual_goal = ``smt_seq_nth ([p]:bool list) 0 = q``
      val contextual_native =
        SmtSeqProve.seq_contextual_prove context contextual_goal
      val _ = exact contextual_goal context contextual_native
      val _ = List.app (check contextual_native contextual_goal context
        "str" [H.Object contextual_goal]) [true,false]
      (* Reverse involution has its OWN native producer. Do not assume the
         generic Seq ladder proves this variable-list theorem. *)
      val reverse = ``REVERSE (REVERSE (xs:bool list)) = xs``
      val reverse_native = Drule.ISPEC ``xs:bool list``
        listTheory.REVERSE_REVERSE
      val _ = List.app (check reverse_native reverse [] "seq-rev-rev"
        [H.Object ``xs:bool list``]) [true,false]
      val symmetry = ``((xs:bool list) = ys) = (ys = xs)``
      val symmetry_native = CPC_ProofReplay.replay_rare_rewrite_for_test
        "eq-symm" [``xs:bool list``,``ys:bool list``]
      val _ = List.app (check symmetry_native symmetry [] "eq-symm"
        [H.Object ``xs:bool list``,H.Object ``ys:bool list``]) [true,false]
      val bad = ``smt_seq_nth ([p]:bool list) 0 = ~p``
    in require "CPC accepted a false declared sequence obligation"
      (declines (fn () =>
        (H.cpc_arguments_using_admitted limit
          (fn admit => CPC_ProofReplay.graph_bounded_worker_with_admission
            admit []) bad [] "seq-eval-op" [H.Object bad] true;SOME ())))
    end

  fun admission_first_error () =
    let
      val goal = ``([]:bool list) ++ xs = xs``
      val fact = Thm.concl listTheory.APPEND
      val genuine = A.new_term_check {limit=limit,observe=fn () => ()}
      fun check contextual =
        let
          val stopped = ref false
          fun admit tm =
            if !stopped then
              raise Fail "sequence retried after admission error"
            else if tm ~~ fact then
              (stopped := true;raise Feedback.mk_HOL_ERR
                "Task40Sequence" "rewrite" "first error")
            else genuine tm
          val preserved =
            ((ignore (if contextual then
                SmtSeqProve.seq_contextual_prove_with_admission
                  admit [``sequence_assumption:bool``] goal
              else SmtSeqProve.seq_prove_with_admission admit goal);false)
             handle Feedback.HOL_ERR detail =>
               Feedback.top_structure_of detail = "Task40Sequence" andalso
               Feedback.top_function_of detail = "rewrite" andalso
               Feedback.message_of detail = "first error")
        in require "sequence swallowed its first admission exception"
          (!stopped andalso preserved) end
    in check false;check true end

  fun intermediate_admission () =
    let
      fun elements prefix = List.tabulate (16,fn i =>
        Term.mk_var (prefix ^ Int.toString i,Type.bool))
      val source = listSyntax.mk_list (elements "seq_input_",Type.bool)
      val replacement = listSyntax.mk_list (elements "seq_output_",Type.bool)
      val update = Term.rator (Term.rator (Term.rator
        ``smt_seq_update (xs:bool list) i ys``))
      val goal = boolSyntax.mk_eq
        (Term.list_mk_comb (update,[source,``0:int``,replacement]),replacement)
      val cap = Int.max (256,Term.term_size goal+4)
      val _ = require "sequence intermediate fixture input does not fit"
        (Term.term_size goal <= cap)
      val stopped = ref false
      val genuine = A.new_term_check {limit=cap,observe=fn () => ()}
      val originals = Term.FVL [goal] Term.empty_tmset
      fun admit tm =
        if !stopped then raise Fail "sequence retried oversized intermediate"
        else if Term.term_size tm > cap andalso
          List.exists (fn v => HOLset.member (originals,v))
            (HOLset.listItems (Term.FVL [tm] Term.empty_tmset)) then
          (stopped := true;genuine tm)
        (* Oversized generic exports may be skipped during discovery; the
           failing source intermediate must not be skipped or retried. *)
        else genuine tm
      val rejected =
        ((ignore (SmtSeqProve.seq_prove_with_admission admit goal);false)
         handle Feedback.HOL_ERR detail => String.isSubstring
           "operator schema exceeds local admission"
           (Feedback.message_of detail))
      val _ = require "fitting sequence input bypassed intermediate admission"
        (rejected andalso !stopped)
      val generous = A.new_term_check {limit=limit,observe=fn () => ()}
      val native = SmtSeqProve.seq_prove goal
      val theorem = SmtSeqProve.seq_prove_with_admission generous goal
    in exact goal [] theorem;same_tags native theorem end

  (* A shallow, physically shared DAG, NOT an exponentially deep append
     normalisation. Its unfolded input is >131000 but <200000 nodes, near
     the existing Sequence callsite cap, not a reduced adapter allowance. *)
  fun large_input () = with_graph (fn graph => fn scope =>
    let
      val combine = ``sequence_combine:bool -> bool -> bool``
      fun shared 0 = ``sequence_leaf:bool``
        | shared n = let val child = shared (n-1)
                     in Term.list_mk_comb (combine,[child,child]) end
      val singleton = listSyntax.mk_list ([shared 14],Type.bool)
      val goal = boolSyntax.mk_eq
        (listSyntax.mk_append (``[]:bool list``,singleton),singleton)
      val size = Term.term_size goal
      val cap = 200000
      val _ = require "large sequence fixture size changed"
        (size > 131000 andalso size < cap)
      val node = #node (G.import graph scope cap goal)
      val calls = ref 0
      val result = A.prove_admitted graph scope
        {inputs=[node,node],template_limit=cap,observe=fn _ => (),
         procedure=fn admit => fn [left,right] =>
           (calls := !calls+1;
            require "large sequence shared root was copied"
              (Portable.pointer_eq (left,right));
            require "large source variables reached sequence worker"
              (H.disjoint [goal] [left,right]);
            SmtSeqProve.seq_prove_with_admission admit left)
           | _ => raise Fail "large sequence arity"}
      val native = SmtSeqProve.seq_prove_with_admission
        (A.new_term_check {limit=cap,observe=fn () => ()}) goal
      val theorem = #theorem result
    in require "large supported sequence worker was retried" (!calls=1);
       exact goal [] theorem;same_tags native theorem end)

  fun ground_replacement () =
    let
      val goals =
        [``smt_seq_replace_all ([1;2;1]:int list) [1] [3] = [3;2;3]``,
         ``smt_seq_replace_all ([1;1;1]:int list) [1;1] [2] = [2;1]``,
         ``smt_seq_replace_all ([1;2]:int list) [] [3] = [1;2]``,
         ``smt_seq_replace_all ([(1w+2w);3w]:8 word list) [3w] [4w] =
             [4w;4w]``]
      val check = A.new_term_check {limit=limit,observe=fn () => ()}
      val _ = List.app (fn goal =>
        let val theorem = SmtSeqProve.seq_prove_with_admission check goal
        in exact goal [] theorem;
           same_tags (SmtSeqProve.seq_prove goal) theorem end) goals
    in require "false closed replacement was accepted"
      (declines (fn () => SOME (SmtSeqProve.seq_prove_with_admission check
        ``smt_seq_replace_all ([1;2;1]:int list) [1] [3] = [3;3;2]``)))
    end

  fun run () =
    (schemas_and_sharing ();false_obligations ();contextual ();
     graph_handlers ();parsed_z3 ();cpc_cases ();admission_first_error ();
     intermediate_admission ();ground_replacement ();large_input ())
end
