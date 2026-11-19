(* The owned Value receiver classifies every rule (pop, resolution, CNF,
   alignment, simple Boolean/equality, truth family, bounded) while it
   prepares, and pays for that through its packet/contract guard. One
   case per route class runs through preparation and replay on a live
   packet, a stale packet and a tight-budget packet. The checks are
   relations inside one run (an exact budget reproduces the live
   outcome, charge and callback trace; one unit less is refused with a
   trace that is a prefix of the live one; a stale packet is refused
   before any step completes); no charge is pinned. *)
structure CPC_OwnedClassificationTests =
struct
  open HolKernel boolLib
  structure W = SmtReplayInvocationWork
  structure VP = SmtLib_GraphValueProof
  structure Receiver = CPC_OwnedValueNamedReplay

  fun require message yes = if yes then () else raise Fail message

  val p = mk_var("cpc_cls_p",bool)
  val q = mk_var("cpc_cls_q",bool)
  val r = mk_var("cpc_cls_r",bool)
  val f = mk_var("cpc_cls_f",bool --> bool)
  val bindings = [("p",p),("q",q),("r",r),("f",f)]
  val goal = mk_conj(mk_var("cpc_cls_goal",bool),mk_var("cpc_cls_goal",bool))
  val neg = mk_neg val disj = mk_disj val imp = mk_imp
  val eq = mk_eq val app = mk_comb

  datatype path = Plan | Replay
  (* The packet is open, closed right ahead of the path, or (Plan only)
     closed by the first type-check callback, in the middle of planning. *)
  datatype packet_state = Open | Closed | ClosedByCallback
  type observation =
    {before:IntInf.int,charged:IntInf.int,outcome:string,steps:int,
     trace:string list}

  (* One path of one case. [before] is the Work charged ahead of the
     path (packet, setup and, for Replay, planning); [charged] is what
     the path itself charged. [trace] lists the type-check callbacks
     and each completed step's theorem, in order. With [state] the
     packet is closed ahead of or during the path. A [budget] bounds the
     whole portfolio. *)
  fun observe {assumptions,text} path budget state : observation =
    let
      val total = ref 0 : IntInf.int ref
      val mark = ref 0 : IntInf.int ref
      val outcome = ref "refused: before the path" and steps = ref 0
      val trace = ref ([]:string list)
      val callbacks = ref 0
      fun run (e:CPC_OwnedValueTestFixture.env) =
        let
          fun charged () = #charged (W.audit_policy (#work e))
          val _ = total := charged ()
          val held = CPC_OwnedValueTestFixture.packet bindings e text
          val data = W.with_step (#work e) (fn () =>
            VP.contents_with_policy_for (#work e) (#query e) held)
          val values = CPC_OwnedValueTestFixture.asserted_values e data
          fun plan () = Receiver.prepare_with_policy (#work e) (#query e)
            held {assertions=values,native_contract= #contract e,
                  check_type=fn ty =>
                    (trace := ("type " ^ type_to_string ty) :: !trace;
                     if state = ClosedByCallback andalso !callbacks = 0
                     then VP.close held else ();
                     callbacks := !callbacks + 1)}
          fun refused detail = "refused: " ^ Feedback.message_of detail
          fun replay invocation =
            let
              val _ = mark := charged ()
              fun next ids =
                case Receiver.replay_next_with_policy (#work e) invocation of
                  NONE => List.rev ids
                | SOME {id,...} => (steps := !steps+1;next (id::ids))
              fun receipt id =
                let val {block,edge,...} =
                      Receiver.step_with_policy_for (#work e) invocation id
                    val theorem = W.with_step (#work e) (fn () =>
                      SmtReplayOwnedValueProof.compact_theorem_for
                        (#work e) block edge)
                in trace := ("step " ^ id ^ " " ^
                     term_to_string (concl theorem) ^ " / " ^
                     Int.toString (length (hyp theorem))) :: !trace end
            in
              (if state = Closed then VP.close held else ();
               List.app receipt (next []);outcome := "replayed")
              handle Feedback.HOL_ERR detail => outcome := refused detail
            end
          val _ = if state = Closed andalso path = Plan
            then VP.close held else ()
          val _ = mark := charged ()
          val prepared = Exn.capture plan ()
          val invocation = case prepared of
              Exn.Res (Receiver.Prepared invocation) =>
                (if path = Plan then outcome := "prepared" else ();
                 SOME invocation)
            | Exn.Res (Receiver.Needs rows) =>
                (outcome := "needs " ^ Int.toString (length rows);NONE)
            | Exn.Exn (Feedback.HOL_ERR detail) =>
                (outcome := refused detail;NONE)
            | Exn.Exn other => raise other
          val _ = if path = Plan then total := charged () else
            (case invocation of
               SOME invocation => (replay invocation;total := charged ())
             | NONE => total := charged ())
          val _ = case invocation of
              SOME invocation => (Receiver.close invocation
                handle Feedback.HOL_ERR _ => ())
            | NONE => (VP.close held handle Feedback.HOL_ERR _ => ())
        in () end
      val setup = Exn.capture (fn () =>
        CPC_OwnedValueTestFixture.fixture
          {budget=budget,retain=true,prefix="cpc_cls_"} assumptions goal run) ()
      val _ = case setup of Exn.Exn (Feedback.HOL_ERR detail) =>
          outcome := "refused: " ^ Feedback.message_of detail
        | Exn.Exn other => raise other
        | Exn.Res () => ()
    in {before= !mark,charged= !total - !mark,outcome= !outcome,
        steps= !steps,trace=List.rev (!trace)} end

  (* One case per route class. [expected] is the outcome of live
     planning: Boolean/equality/truth/CNF/resolution/alignment steps
     with a recorded conclusion are prepared; pop and bounded steps
     are returned as requirements (a pop also needs its Scope). *)
  type case_ = {label:string,expected:string,assumptions:term list,
    text:string}
  val cases:case_ list = [
    {label="resolution",expected="prepared",
     assumptions=[disj(p,q),neg p,neg q],
     text="((assume @clause (or p q)) (assume @np (not p)) "^
       "(assume @nq (not q)) (step @q q :rule resolution "^
       ":premises (@clause @np)) "^
       "(step @done false :rule resolution :premises (@q @nq)))"},
    {label="cnf",expected="prepared",
     assumptions=[neg(disj(p,imp(p,q)))],
     text="((assume @negative (not (or p (=> p q)))) "^
       "(step @clause (or p (=> p q)) "^
       ":rule cnf_implies_neg1 :args ((=> p q))) "^
       "(step @done false :rule contra :premises (@clause @negative)))"},
    {label="factoring",expected="prepared",
     assumptions=[disj(p,disj(p,q)),neg p,neg q],
     text="((assume @clause (or p p q)) (assume @np (not p)) "^
       "(assume @nq (not q)) (step @factored (or p q) :rule factoring "^
       ":premises (@clause)) (step @q q :rule resolution "^
       ":premises (@factored @np)) "^
       "(step @done false :rule resolution :premises (@q @nq)))"},
    {label="simple boolean",expected="prepared",
     assumptions=[neg(disj(neg boolSyntax.F,p))],
     text="((assume @input (not (or (not false) p))) "^
       "(step @picked (not (not false)) :rule not_or_elim "^
       ":premises (@input) :args (0)) "^
       "(step @done false :rule not_not_elim :premises (@picked)))"},
    {label="simple equality",expected="prepared",
     assumptions=[eq(app(f,p),app(f,q)),app(f,p),neg(app(f,q))],
     text="((assume @equation (= (f p) (f q))) "^
       "(assume @source (f p)) (assume @negative (not (f q))) "^
       "(step @q (f q) :rule eq_resolve :premises (@source @equation)) "^
       "(step @done false :rule contra :premises (@q @negative)))"},
    {label="truth family",expected="prepared",
     assumptions=[eq(p,boolSyntax.T),neg p],
     text="((assume @equal (= p true)) (assume @negative (not p)) "^
       "(step @p p :rule true_elim :premises (@equal)) "^
       "(step @done false :rule contra :premises (@p @negative)))"},
    {label="bounded",expected="needs 1",
     assumptions=[p,imp(p,q),neg q],
     text="((assume @p p) (assume @imp (=> p q)) (assume @negative "^
       "(not q)) (step @q q :rule modus_ponens :premises (@p @imp)) "^
       "(step @done false :rule contra :premises (@q @negative)))"},
    {label="pop",expected="needs 2",
     assumptions=[neg p],
     text="((step @clause (or p (=> p q)) "^
       ":rule cnf_implies_neg1 :args ((=> p q))) "^
       "(assume-push @local p) "^
       "(step-pop @scope (=> p p) :rule scope :premises (@local)))"}]

  fun is_prefix [] _ = true
    | is_prefix (x::xs) (y::ys) = x = y andalso is_prefix xs ys
    | is_prefix _ [] = false
  fun is_refusal (o_:observation) =
    String.isPrefix "refused" (#outcome o_)

  (* Live, tight-budget (exactly enough, and one short) and stale runs
     of one path; [live] must have been observed already. *)
  fun check_path label (c:case_) path (live:observation) =
    let
      val name = label ^ (case path of Plan => " plan" | Replay => " replay")
      val spec = {assumptions= #assumptions c,text= #text c}
      val exact = #before live + #charged live
      val same = observe spec path (SOME exact) Open
      val short = observe spec path (SOME (exact-1)) Open
      val stale = observe spec path NONE Closed
    in
      require (name ^ ": live path charged nothing") (#charged live > 0);
      require (name ^ ": an exact budget changed the outcome or charge")
        (#outcome same = #outcome live andalso
         #charged same = #charged live andalso #steps same = #steps live
         andalso #trace same = #trace live);
      require (name ^ ": one unit short was not refused")
        (is_refusal short andalso
         #before short + #charged short <= exact andalso
         is_prefix (#trace short) (#trace live));
      require (name ^ ": a stale packet was not refused")
        (is_refusal stale andalso #steps stale = 0)
    end

  fun check_case (c:case_) =
    let
      val spec = {assumptions= #assumptions c,text= #text c}
      val plan = observe spec Plan NONE Open
      val _ = require (#label c ^ ": planning outcome " ^ #outcome plan)
        (#outcome plan = #expected c)
      val _ = check_path (#label c) c Plan plan
      (* Closing the packet inside the first callback must be noticed by
         the next paid step: preparation is refused, not completed. *)
      val _ = if null (#trace plan) then () else
        require (#label c ^ ": a packet closed mid-planning was used")
          (is_refusal (observe spec Plan NONE ClosedByCallback))
      val replay = observe spec Replay NONE Open
    in
      if #expected c = "prepared" then
        (require (#label c ^ ": replay outcome " ^ #outcome replay)
           (#outcome replay = "replayed" andalso #steps replay > 0);
         check_path (#label c) c Replay replay)
      else
        require (#label c ^ ": a pending case replayed")
          (#steps replay = 0)
    end

  fun run () =
    List.app (fn c =>
      (testutils.tprint ("CPC owned classification: " ^ #label c);
       check_case c;testutils.OK ())) cases
end
