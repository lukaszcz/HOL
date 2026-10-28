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
      fun cpc rule_name target =
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
                        "1.3.4" rule_name),premises=[],
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
    in List.app (fn name => List.app (fn (good,bad) =>
      (cpc name good;require ("CPC sequence worker merged IDs: " ^ name)
        (declines (fn () => (cpc name bad;SOME ()))))) cases)
      ["seq-eval-op","trust"] end)

  (* Public compact dispatch, not a manufactured TRUST theorem. The bad
     certificate has the very same native endpoint but a different graph
     declaration on the right. Neither native spelling nor tags admit it. *)
  fun compact_trust_identity () =
    let
      fun check different = with_graph (fn graph => fn scope =>
        let
          val goal = ``smt_seq_nth ([sequence_compact_identity:bool]) 0 =
                       sequence_compact_identity``
          val sources = SmtReplaySource.new graph scope limit
            {goal=goal,assumptions=[``sequence_unused:bool``]}
          val good = #node (SmtReplaySource.goal_source sources)
          val operands = valOf (R.operands graph boolSyntax.equality 2 good)
          val other = G.variable graph scope G.Generated
            ``sequence_compact_identity:bool``
          val equality = G.constant graph scope
            (Term.rator (Term.rator goal))
          val bad = G.application graph scope
            (G.application graph scope (equality,hd operands),other)
          val _ = require "compact TRUST needs same-native distinct IDs"
            (good <> bad andalso G.representative graph bad ~~ goal)
          val target = if different then bad else good
          fun located node:SmtLib_GraphFrontend.term =
            {node=node,scope=scope,binder_blocks=[],source_syntax=NONE,
             occurrence=SmtLib_Parser.ConstructionOccurrence
               {value=node,role=SmtLib_Parser.ConstructionAtom,
                token="sequence-trust",children=[]}}
          fun registered name = valOf (CPC_Proof.lookup_rule "1.3.4" name)
          val proof:CPC_ProofParser.graph_proof =
            {cvc_version="1.3.4",commands=
              [CPC_ProofParser.GraphAssume ("@denied",located
                 (SmtReplaySource.denied_goal_node sources)),
               CPC_ProofParser.GraphStep {pop=false,step=
                 {id="@seq",rule=registered "trust",premises=[],
                  conclusion=SOME (located target),
                  args=[CPC_ProofParser.GraphTerm (located target)],
                  raw_conclusion=NONE,raw_args=[]}},
               CPC_ProofParser.GraphStep {pop=false,step=
                 {id="@done",rule=registered "resolution",
                  premises=["@seq","@denied"],
                  conclusion=SOME (located
                    (G.constant graph scope boolSyntax.F)),
                  args=[],raw_conclusion=NONE,raw_args=[]}}]}
          fun replay () = CPC_ProofReplay.prove_graph_proof
            {graph=graph,scope=scope,sources=sources,proof=proof}
        in if different then
             require "compact Seq TRUST merged distinct declaration IDs"
               (declines (fn () => SOME (replay ())))
           else let val theorem = replay ()
                in exact goal [``sequence_unused:bool``] theorem;
                   same_tags (SmtSeqProve.seq_prove goal) theorem end
        end)
    in check false;check true end

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
      val _ = List.app (fn (goal,_) => List.app (fn name =>
        both goal name [goal]) ["seq-eval-op","trust"]) schemas
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
      val _ = List.app (fn name => List.app
        (check contextual_native contextual_goal context name
          [H.Object contextual_goal]) [true,false]) ["str","trust"]
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

  val nested_scalar_goal =
    ``([word_from_bin_list
          (smt_seq_replace_all ([1;0;1]:num list) [0] [1])]:
         8 word list) ++ [] = [7w]``

  (* Durable review coverage: scalar evaluation may bear words or lists,
     but must not recursively CBV-evaluate the surrounding Seq operation. *)
  fun closed_scalars () = with_graph (fn graph => fn scope =>
    let
      val goals =
        [``([1w+2w]:8 word list) ++ [] = [3w]``,
         ``smt_seq_nth ([1w+2w]:8 word list) 0 = 3w``,
         ``smt_seq_update ([1w+2w]:8 word list) 0 [3w] = [3w]``,
         ``smt_seq_replace_all ([1w+2w]:8 word list) [3w] [4w] = [4w]``,
         ``([1w && 2w]:8 word list) ++ [] = [0w]``,
         ``smt_seq_nth ([1w && 2w]:8 word list) 0 = 0w``,
         ``([1w << 2]:8 word list) ++ [] = [4w]``,
         ``([w2n (3w:8 word)]:num list) ++ [] = [3]``,
         ``smt_seq_replace_all ([REVERSE [T;F]]:bool list list)
             [[F;T]] [[T]] = [[T]]``,
         ``smt_seq_replace_all ([MAP ($+ (1:int)) [1;2]]:int list list)
             [[2;3]] [[]] = [[]]``,
         ``smt_seq_replace_all ([word_from_bin_list [1;0;1]]:8 word list)
             [5w] [4w] = [4w]``,
         ``([word_from_bin_list [1;0;1]]:8 word list) ++ [] = [5w]``,
         nested_scalar_goal]
      fun check goal =
        let
          val native = SmtSeqProve.seq_prove goal
          val _ = exact goal [] native
          val calls = ref 0
          val result = A.prove_admitted graph scope
            {inputs=[import graph scope goal],template_limit=limit,
             observe=fn _ => (),procedure=fn admit => fn [term] =>
               (calls := !calls+1;
                SmtSeqProve.seq_prove_with_admission admit term)
               | _ => raise Fail "closed scalar arity"}
          val theorem = #theorem result
        in require "closed scalar worker was retried or bypassed" (!calls=1);
           exact goal [] theorem;same_tags native theorem end
    in List.app check goals end)

  fun opaque_scalar_cancellation () =
    let
      val cap = 512
      val scalar = ``2 EXP 1024``
      val computed = boolSyntax.rhs
        (Thm.concl (computeLib.EVAL_CONV scalar))
      val _ = require "opaque scalar fixture result unexpectedly fits"
        (Term.term_size computed > cap)
      val admit = A.new_term_check {limit=cap,observe=fn () => ()}
      val goals =
        [``([2 EXP 1024]:num list) ++ [] = [2 EXP 1024]``,
         ``smt_seq_nth ([2 EXP 1024]:num list) 0 = 2 EXP 1024``]
      fun check goal =
        case Exn.capture (SmtSeqProve.seq_prove_with_admission admit) goal of
          Exn.Res theorem => exact goal [] theorem
        | Exn.Exn error => raise Fail ("opaque scalar cancellation: " ^
            Library.term_to_string goal ^ ": " ^ General.exnMessage error)
    in List.app check goals end

  val replacement_goal =
    ``smt_seq_replace_all ([1;2;1]:int list) [1] [3] = [3;2;3]``

  (* Reject the GENERATED numeral-fuel equality, not the source goal or
     generic recursive definition. This is the review's swallowed-error
     reproducer: the callback must never be visited again after rejection. *)
  fun replacement_fuel_equality tm =
    boolSyntax.is_eq tm andalso
    let
      val (head,args) = boolSyntax.strip_comb (boolSyntax.lhs tm)
    in Term.is_const head andalso
       let val {Thy,Name,...} = Term.dest_thy_const head
       in Thy="HolSmt" andalso Name="smt_seq_replace_all_aux" andalso
          length args=4 andalso numSyntax.is_numeral (hd args) andalso
          not (hd args ~~ numSyntax.zero_tm)
       end
    end

  val admission_primary = Feedback.mk_HOL_ERR
    "Task40Sequence" "generated" "primary admission error"

  fun primary_preserved result =
    case result of Exn.Exn (Feedback.HOL_ERR detail) =>
        not (SmtResource.is_resource_gate detail) andalso
        Feedback.top_structure_of detail = "Task40Sequence" andalso
        Feedback.top_function_of detail = "generated" andalso
        Feedback.message_of detail = "primary admission error"
      | _ => false

  fun first_generated_error label matches action =
    let
      val stopped = ref false
      val after = ref 0
      val genuine = A.new_term_check {limit=limit,observe=fn () => ()}
      fun admit tm =
        if !stopped then after := !after+1
        else (genuine tm;
          if matches tm then
            (stopped := true;raise admission_primary)
          else ())
      val result = Exn.capture (fn () => action admit) ()
    in require (label ^ ": generated admission was bypassed") (!stopped);
       require (label ^ ": primary HOL_ERR was swallowed/replaced")
         (primary_preserved result);
       require (label ^ ": admission continued after primary error") (!after=0)
    end

  fun first_replacement_error label action =
    first_generated_error label replacement_fuel_equality action

  fun replacement_first_error () =
    first_replacement_error "direct replacement" (fn admit =>
      ignore (SmtSeqProve.seq_prove_with_admission admit replacement_goal))

  (* The existential is made inside prove_split, unlike the generic
     IS_SUBLIST_APPEND fact. Symbolic leaves force the append-witness path;
     its candidate search must not treat this rejection as a failed split. *)
  fun witness_first_error () =
    let
      val goal =
        ``IS_SUBLIST ((xs:bool list) ++ middle ++ zs) middle``
      val native = SmtSeqProve.seq_prove goal
      val _ = exact goal [] native
      val generated = boolSyntax.rhs (Thm.concl
        (Conv.REWR_CONV rich_listTheory.IS_SUBLIST_APPEND goal))
      val _ = require "witness fixture lost its generated existential"
        (boolSyntax.is_exists generated andalso
         not (null (Term.free_vars generated)) andalso
         not (generated ~~ Thm.concl rich_listTheory.IS_SUBLIST_APPEND))
    in first_generated_error "append witness" (fn tm => tm ~~ generated)
      (fn admit => ignore
        (SmtSeqProve.seq_prove_with_admission admit goal)) end

  (* Reuse the SAME checked_procedures closure. A fuel conversion uses
     Traverse's interrupt escape; restore must clear that saved exception
     before the next invocation, not merely rethrow it. *)
  fun replacement_closure_reset () =
    let
      val reject = ref true
      val stopped = ref false
      val after = ref 0
      val genuine = A.new_term_check {limit=limit,observe=fn () => ()}
      fun admit tm =
        if !stopped then after := !after+1
        else (genuine tm;
          if !reject andalso replacement_fuel_equality tm then
            (stopped := true;raise admission_primary)
          else ())
      val prove = SmtSeqProve.seq_prove_with_admission admit
      val result = Exn.capture prove replacement_goal
      val _ = require "reusable sequence closure lost its conversion error"
        (!stopped andalso primary_preserved result andalso !after=0)
      val _ = (reject := false;stopped := false)
      val theorem = prove replacement_goal
    in exact replacement_goal [] theorem end

  (* closed_scalars checks the exact native and admitted positive first. *)
  fun nested_scalar_first_error () =
    first_replacement_error "replacement under scalar" (fn admit =>
      ignore (SmtSeqProve.seq_prove_with_admission admit nested_scalar_goal))

  (* API composition, deliberately nested in consumer scopes. Only the
     ACTUAL Arithmetic observer rejects: the Seq callback arms it on a
     generated fuel equality, then calls Arithmetic's own admit function.
     Arithmetic must unwrap its private AdmissionCallback without exposing
     the primary HOL_ERR to the inner consumer's fallback ladder. *)
  fun arithmetic_observer_first_error () =
    with_graph (fn graph => fn scope =>
    let
      val node = import graph scope replacement_goal
      val armed = ref false
      val stopped = ref false
      val after = ref 0
      fun observe _ =
        if !stopped then after := !after+1
        else if !armed then
          (stopped := true;raise admission_primary)
        else ()
      fun procedure admit [term] =
            SmtSeqProve.seq_prove_with_admission (fn tm =>
              (if !stopped then after := !after+1 else ();
               if replacement_fuel_equality tm then armed := true else ();
               admit tm)) term
        | procedure _ _ = raise Fail "observer replacement arity"
      val result = Exn.capture (fn () =>
        SmtSeqProve.with_admission_errors (fn () =>
          SmtSeqProve.with_admission_errors (fn () =>
            ignore (A.prove_admitted graph scope
              {inputs=[node],template_limit=limit,observe=observe,
               procedure=procedure})))) ()
      val _ = require "Arithmetic observer bypassed generated fuel admission"
        (!armed andalso !stopped)
      val _ = require "Arithmetic leaked/replaced its admission callback"
        (primary_preserved result)
      val _ = require "Arithmetic continued after observer rejection"
        (!after=0)
      (* Outside all consumer scopes the same error must be raw again. *)
      val reset = Exn.capture (fn () =>
        SmtSeqProve.seq_prove_with_admission
          (fn _ => raise admission_primary) replacement_goal) ()
      val _ = require "nested consumer admission scopes were not reset"
        (primary_preserved reset)
      val recovered = A.prove_admitted graph scope
        {inputs=[node],template_limit=limit,observe=fn _ => (),
         procedure=fn admit => fn [term] =>
           SmtSeqProve.seq_prove_with_admission admit term
           | _ => raise Fail "observer recovery arity"}
    in exact replacement_goal [] (#theorem recovered) end)

  (* Invoke the admitted native workers used by the graph law producers.
     In particular do NOT put with_admission_errors around the test: the
     consumer itself must preserve the callback error across its fallbacks. *)
  fun native_consumer_first_error () = with_graph (fn graph => fn scope =>
    let
      val node = import graph scope replacement_goal
      fun run label worker = first_replacement_error label (fn reject =>
        ignore (A.prove_admitted graph scope
          {inputs=[node],template_limit=limit,observe=fn _ => (),
           procedure=fn admit => fn [term] =>
             worker (fn tm => (reject tm;admit tm)) term
             | _ => raise Fail "consumer replacement arity"}))
      fun cpc name admit term =
        let
          val located = {term=term,provenance=
            CPC_Proof.UnavailableProvenance "replacement admission"}
          val step:CPC_Proof.step =
            {id="@seq",rule=valOf (CPC_Proof.lookup_rule "1.3.4" name),
             premises=[],conclusion=SOME located,args=[located]}
        in #1 (CPC_ProofReplay.graph_bounded_worker_with_admission
          admit [] (step,[])) end
      fun z3 recorded name admit term =
        let
          val rule = valOf (Z3_Proof.lookup_rule "4.15.3" name)
          val metadata = if name="th-lemma-seq" then SOME
            (Z3_Proof.mk_th_lemma_metadata ("seq",NONE,[])) else NONE
          val pt = Z3_ProofReplay.graph_local_proofterm
            rule metadata term [] []
          val proof = Z3_Proof.mk_proof
            (Redblackmap.insert (Redblackmap.mkDict Int.compare,0,pt),
             Term.empty_tmset,[],"4.15.3")
        in if recorded then #theorem
          (Z3_ProofReplay.replay_root_with_definition_occurrences_admitted
            admit [] proof)
        else Z3_ProofReplay.replay_root_admitted admit [] proof end
      val _ = List.app (fn name => run ("CPC " ^ name) (cpc name))
        ["seq-eval-op","str","trust"]
    in List.app (fn recorded => List.app (fn name =>
      run ("Z3 " ^ name ^ " recorded=" ^ Bool.toString recorded)
        (z3 recorded name)) ["th-lemma-seq","rewrite"]) [false,true] end)

  fun run () =
    (schemas_and_sharing ();false_obligations ();contextual ();
     graph_handlers ();compact_trust_identity ();parsed_z3 ();cpc_cases ();
     admission_first_error ();intermediate_admission ();
     ground_replacement ();closed_scalars ();opaque_scalar_cancellation ();
     replacement_first_error ();witness_first_error ();
     replacement_closure_reset ();nested_scalar_first_error ();
     arithmetic_observer_first_error ();native_consumer_first_error ();
     large_input ())
end
