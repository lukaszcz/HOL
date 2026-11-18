(* Characterization of the eleven CPC clausal-elimination rules:
   not_implies_elim1/2, implies_elim, equiv_elim1/2, not_equiv_elim1/2,
   ite_elim1/2 and not_ite_elim1/2.

   One table of rows (premise text, premise term, expected literals with
   their operand provenance, or a refusal) is read by three engines:
   - term replay (CPC_ProofReplay.replay_root_for_test), here;
   - the graph consumer, here, through
     CPC_GraphProofReplay.check_contradiction_observing, the same entry
     that the string_named_obligations group uses; its CommandEnd events
     report the literal and provenance that discovery inferred;
   - the owned Value consumer, in selftest postlude 417, which reads the
     rows and bindings from here and checks verdicts, dependencies, the
     recorded OR boundary and refusals (its charged Work is harvested out
     of tree, not checked). *)
structure CPC_ClausalEliminationTests =
struct
  open HolKernel boolLib
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure Q = CPC_ProofParser
  structure R = CPC_GraphProofReplay
  structure F = SmtLib_GraphFrontend
  structure Prov = CPC_Proof

  fun require message yes = if yes then () else raise Fail message

  (* ---------------------------------------------------------------- *)
  (* Literals and rows                                                *)
  (* ---------------------------------------------------------------- *)

  type atom = {text : string,term : term,prov : Prov.term_provenance}
  type literal = {positive : bool,atom : atom}
  (* Refuse carries a substring of the diagnostic. *)
  datatype outcome = Accept of literal list | Refuse of string
  (* A resolution step that consumes the derived clause: [unit] is
     assumed refuted, and [result] is what remains. Resolution reads the
     clause's recorded OR boundary, so it is accepted only when the owned
     consumer recorded the clause as an OR of its literals. *)
  datatype family = Implication | Equivalence | Conditional
  (* What a row exercises; checks select rows by it, never by label. *)
  datatype case_kind = ValidPremise | AtomicLeafPremise | WrongOperand
    | NoNegation | PremiseIsT | BadArity | ReversedClause | OrBoundary
  type follow = {unit : literal,result : literal}
  type row =
    {label : string,rule : string,family : family,kind : case_kind,
     premise : string,term : term,
     (* The clause the rule derives from a valid premise, as text: the
        owned consumer needs a declared conclusion. *)
     declared : string,
     (* When present, the outcomes describe this step's result. *)
     follow : follow option,
     (* NONE: the engine has no such case. Term replay has no bound
        names. *)
     term_replay : outcome option,graph : outcome option,
     owned : outcome option}

  fun literal_text ({positive,atom={text,...}}:literal) =
    if positive then text else "(not " ^ text ^ ")"
  fun literal_term ({positive,atom={term,...}}:literal) =
    if positive then term else boolSyntax.mk_neg term
  fun literal_provenance ({positive,atom={prov,...}}:literal) =
    if positive then prov else Prov.ApplicationProvenance ("not",[prov])
  fun refutation ({positive,atom}:literal):literal =
    {positive=not positive,atom=atom}
  (* The literals whose refutation the proof assumes: the clause's own,
     or the follow-up step's result and then its resolved unit. *)
  fun final_literals (row:row) lits = case #follow row of
      SOME {unit,result} => [result,unit]
    | NONE => lits

  (* The clause a rule derives and the provenance the graph consumer
     reports for it: a single literal keeps its own, several are joined
     by an OR node. *)
  fun clause_text lits = case lits of
      [] => "false"
    | [lit] => literal_text lit
    | _ => "(or " ^ String.concatWith " " (List.map literal_text lits) ^ ")"
  fun clause_term lits = case lits of
      [] => boolSyntax.F
    | _ => boolSyntax.list_mk_disj (List.map literal_term lits)
  fun clause_provenance lits = case lits of
      [lit] => literal_provenance lit
    | _ => Prov.ApplicationProvenance ("or",List.map literal_provenance lits)

  val atomic = Prov.AtomicProvenance
  val equal2 = Prov.EqualityProvenance (atomic,atomic)
  fun flatten ({positive,atom={text,term,...}}:literal):literal =
    {positive=positive,atom={text=text,term=term,prov=atomic}}

  (* ---------------------------------------------------------------- *)
  (* Table                                                            *)
  (* ---------------------------------------------------------------- *)

  (* Operands, as (text,term,provenance); the letters follow the plan
     table: a, b for implication and equivalence; c, a, b for ITE. *)
  fun operands (p,q,r) =
    let
      val a = {text="(= p r)",term=boolSyntax.mk_eq (p,r),prov=equal2}
      val b = {text="q",term=q,prov=atomic}
      val c = {text="p",term=p,prov=atomic}
      val y = {text="(= q r)",term=boolSyntax.mk_eq (q,r),prov=equal2}
      val n = {text="(and p r)",term=boolSyntax.mk_conj (p,r),
        prov=Prov.ConjunctionProvenance (Prov.ParsedConjunction,
          [atomic,atomic])}
    in {a=a,b=b,c=c,y=y,n=n} end

  fun pos atom = {positive=true,atom=atom}
  fun neg atom = {positive=false,atom=atom}

  (* name, family, premise negated, expected literals from the operands. *)
  fun rule_table {a,b,c,y,n} =
    [("not_implies_elim1",Implication,true,[pos a]),
     ("not_implies_elim2",Implication,true,[neg b]),
     ("implies_elim",Implication,false,[neg a,pos b]),
     ("equiv_elim1",Equivalence,false,[neg a,pos b]),
     ("equiv_elim2",Equivalence,false,[pos a,neg b]),
     ("not_equiv_elim1",Equivalence,true,[pos a,pos b]),
     ("not_equiv_elim2",Equivalence,true,[neg a,neg b]),
     ("ite_elim1",Conditional,false,[neg c,pos y]),
     ("ite_elim2",Conditional,false,[pos c,pos n]),
     ("not_ite_elim1",Conditional,true,[neg c,neg y]),
     ("not_ite_elim2",Conditional,true,[pos c,neg n])]

  fun premise_shape (p,q,r) family =
    let
      val {a,b,y,n,...} = operands (p,q,r)
    in case family of
        Implication => ("(=> " ^ #text a ^ " " ^ #text b ^ ")",
          boolSyntax.mk_imp (#term a,#term b),"atom_imp")
      | Equivalence => ("(= " ^ #text a ^ " " ^ #text b ^ ")",
          boolSyntax.mk_eq (#term a,#term b),"atom_eq")
      | Conditional => ("(ite p " ^ #text y ^ " " ^ #text n ^ ")",
          boolSyntax.mk_cond (p,#term y,#term n),"atom_ite")
    end

  (* Whole premises bound to a name by the frontends, so that their
     occurrence is one atomic leaf. *)
  fun bindings (p,q,r) =
    List.concat (List.map (fn family =>
      let val (_,term,bound) = premise_shape (p,q,r) family
      in [(bound,term),("not_" ^ bound,boolSyntax.mk_neg term)] end)
      [Implication,Equivalence,Conditional])

  (* The diagnostic of each refused shape: the shared worker's, which term
     replay and the graph consumer report, and the owned consumer's. *)
  datatype refusal = Wrong | Missing | ReducedToT | Chained
  fun refusal family negated kind =
    let
      val not_negation = "not a negation"
      val declared = "non-equality premise requires a declared conclusion"
    in case (family,negated,kind) of
        (Implication,true,Missing) => not_negation
      | (Implication,true,ReducedToT) => not_negation
      | (Implication,_,_) => "not an \"==>\""
      | (Equivalence,false,_) => declared
      | (Equivalence,true,Missing) => not_negation
      | (Equivalence,true,ReducedToT) => not_negation
      | (Equivalence,true,_) => "not an \"=\""
      | (Conditional,false,_) => "premise is not a conditional"
      | (Conditional,true,_) => "premise is not a negated conditional"
    end
  fun owned_refusal family negated kind =
    case (family,negated,kind) of
        (_,true,Missing) => "expected negation"
      | (Implication,true,ReducedToT) => "expected negation"
      | (Equivalence,true,ReducedToT) => "expected negation"
      | (Equivalence,_,_) => "expected relation premise"
      | _ => "incorrect rule operand constructor"

  fun row label kind family rule premise term declared outcome owned : row =
    {label=rule ^ ": " ^ label,rule=rule,family=family,kind=kind,
     premise=premise,term=term,
     declared=declared,follow=NONE,term_replay=SOME outcome,
     graph=SOME outcome,owned=SOME owned}

  (* The expected literals of a rule over the given operands. *)
  fun rule_literals operands rule =
    case List.find (fn (name,_,_,_) => name = rule) (rule_table operands) of
        SOME (_,_,_,lits) => lits
      | NONE => raise Fail ("unknown clausal rule " ^ rule)

  (* Every rule against: a valid premise; the same premise as one atomic
     leaf; a premise of the wrong constructor; a missing negation (negated
     rows); a premise reduced to T; and a malformed operand count. *)
  fun rows (p,q,r) : row list =
    let
      val ops as {a,b,...} = operands (p,q,r)
      val T = boolSyntax.T
      val reduced = Accept [pos {text="true",term=T,prov=atomic}]
      (* A third operand: the parser keeps =>/= n-ary, and the rules read
         exactly two. *)
      val nested = {text="(=> q q)",term=boolSyntax.mk_imp (q,q),
        prov=atomic}
      fun rows_of (rule,family,negated,lits) =
        let
          fun wrap (text,term) = if negated then
              ("(not " ^ text ^ ")",boolSyntax.mk_neg term) else (text,term)
          val (text,term,bound) = premise_shape (p,q,r) family
          val (premise,premise_term) = wrap (text,term)
          val (wrong_text,wrong_term) = wrap ("p",p)
          val atomic_name = if negated then "not_" ^ bound else bound
          val declared = clause_text lits
          fun refuse kind = (Refuse (refusal family negated kind),
            Refuse (owned_refusal family negated kind))
          fun row' label kind premise term declared (outcome,owned) =
            row label kind family rule premise term declared outcome owned
          val valid = row' "valid premise" ValidPremise premise
            premise_term declared
            (Accept lits,Accept lits)
          (* The owned consumer cannot read the left literal of a negated
             implication from an atomic leaf. *)
          val flat = List.map flatten lits
          val leaf = {label=rule ^ ": atomic premise provenance",rule=rule,
            family=family,kind=AtomicLeafPremise,premise=atomic_name,
            term=premise_term,declared=declared,
            follow=NONE,term_replay=NONE,graph=SOME (Accept flat),
            owned=SOME (if rule = "not_implies_elim1" then
              Refuse "declared rule endpoint differs" else Accept flat)}
          val wrong = row' "wrong constructor" WrongOperand wrong_text
            wrong_term declared (refuse Wrong)
          val missing = row' "missing negation" NoNegation text term declared
            (refuse Missing)
          val to_t = row' "premise reduced to T" PremiseIsT "true" T "true"
            (if family = Conditional then (reduced,reduced)
             else if family = Equivalence andalso not negated then
               (reduced,Refuse (owned_refusal family negated ReducedToT))
             else refuse ReducedToT)
          val reversed = if List.length lits < 2 then [] else
            [{label=rule ^ ": reversed declared clause",rule=rule,
              family=family,kind=ReversedClause,premise=premise,
              term=premise_term,
              declared=clause_text (List.rev lits),follow=NONE,
              term_replay=NONE,
              graph=NONE,
              owned=SOME (Refuse "declared rule endpoint differs")}]
          (* The recorded OR boundary: observed by resolving the derived
             clause against the refutation of its first literal. The rules
             with a single literal record no boundary to observe (the
             clause is a literal, whose provenance no accept/refuse
             decision reads), and neither do the children of the OR (a
             literal's own provenance is only copied to the result). *)
          val observed = case lits of
              [first,second] =>
                [{label=rule ^ ": recorded OR boundary resolves",rule=rule,
                  family=family,kind=OrBoundary,premise=premise,
                  term=premise_term,declared=declared,
                  follow=SOME {unit=first,result=second},term_replay=NONE,
                  graph=NONE,owned=SOME (Accept lits)}]
            | _ => []
          val arity = case family of
              Implication =>
                let
                  val (text,term) = wrap ("(=> " ^ #text a ^ " " ^ #text b ^
                    " " ^ #text b ^ ")",boolSyntax.mk_imp (#term a,
                      boolSyntax.mk_imp (q,q)))
                  val lits = List.map flatten (rule_literals
                    {a=a,b=nested,c=a,y=a,n=a} rule)
                in [row "malformed arity (three operands)" BadArity family rule
                     text term
                     (clause_text lits) (Accept lits) (Accept lits)] end
            | Equivalence =>
                let
                  val (text,term) = wrap ("(= p r q)",
                    boolSyntax.mk_conj (boolSyntax.mk_eq (p,r),
                      boolSyntax.mk_eq (r,q)))
                in [row' "malformed arity (chained equality)" BadArity text
                     term declared (refuse Chained)] end
            (* The parser cannot build a conditional with another operand
               count: (ite ..) is checked for exactly three arguments, so
               a malformed ITE arity exists only as a constructed occurrence
               (constructed_ite_occurrence below). *)
            | Conditional => []
        in
          valid :: leaf :: wrong ::
          (if negated then [missing] else []) @ [to_t] @ arity @ reversed @
          observed
        end
    in
      List.concat (List.map rows_of (rule_table ops))
    end

  (* ---------------------------------------------------------------- *)
  (* Engines                                                          *)
  (* ---------------------------------------------------------------- *)

  datatype observed =
      Derived of {clause : term,hyps : term list,
                  provenance : Prov.term_provenance option,closed : bool}
    | Declined of string

  fun message exn = case exn of Feedback.HOL_ERR d => Feedback.message_of d
    | Fail text => text
    | other => raise other

  fun parsed text =
    let val stream = TextIO.openString text
    in Q.parse_stream_with_version
         (SmtLib_Logics.parsedicts_of_logic "ALL") "1.3.4" stream end

  fun term_replay (row:row) =
    let
      val text = "((declare-const p Bool) (declare-const q Bool) \
        \(declare-const r Bool) (assume @p1 " ^ #premise row ^ ") \
        \(step @p2 :rule " ^ #rule row ^ " :premises (@p1)))"
    in
      let val theorem = CPC_ProofReplay.replay_root_for_test (parsed text)
          val _ = Library.check_oracle_tags "CPC clausal row"
            (#label row) theorem
      in Derived {clause=Thm.concl theorem,hyps=Thm.hyp theorem,
           provenance=NONE,closed=true} end
      handle exn => Declined (message exn)
    end

  fun graph_options graph scope bindings : F.options =
    {graph=graph,scope=scope,logic="ALL",sources=bindings,
     sorts=Redblackmap.mkDict String.compare,binder_lists=[],
     import_limit=4096,literal_limit=4096,binder_limit=4096,
     recipe_limits={template_limit=4096,index_limit=4096,
       operand_limit=4096,token_limit=4096},
     special=fn _ => fn _ => NONE,ascribed=fn _ => fn _ => fn _ => NONE}

  (* The proof assumes the premise, assumes the refutation of each literal
     the proof is expected to end with, infers the clause, applies the
     row's follow-up step if any, and closes with CONTRA. Without
     Inferred the steps carry no conclusion, so the graph consumer
     reports the provenance it inferred (a declared conclusion would
     replace it). With Declared the conclusions are declared, as the owned
     consumer requires (the row's clause), and checked against the
     literals in their exact order. *)
  datatype conclusions = Inferred | Declared
  fun proof_text (row:row) lits mode =
    let
      val final = final_literals row lits
      val refuted = List.map refutation final
      val names = List.tabulate (List.length refuted,
        fn i => "@a" ^ Int.toString i)
      val assumes = ListPair.map (fn (name,lit) =>
        "(assume " ^ name ^ " " ^ literal_text lit ^ ") ")
        (names,refuted)
      fun conclusion text = case mode of Declared => text ^ " "
        | Inferred => ""
      val step = "(step @clause " ^ conclusion (#declared row) ^
        ":rule " ^ #rule row ^ " :premises (@input))"
      val follow = case #follow row of NONE => ""
        | SOME {result,...} =>
            " (step @next " ^ conclusion (literal_text result) ^
            ":rule resolution :premises (@clause @a1))"
      val last = case #follow row of NONE => "@clause" | SOME _ => "@next"
      val finish = if List.null final then "" else
        " (step @done false :rule contra :premises (" ^ last ^ " " ^
        String.concatWith " " (case #follow row of NONE => names
          | SOME _ => [List.hd names]) ^ "))"
    in
      "((assume @input " ^ #premise row ^ ") " ^ String.concat assumes ^
      step ^ follow ^ finish ^ ")"
    end

  (* The command whose inferred result the graph consumer reports (rows
     with a follow-up step are not run through it). *)
  fun observed_serial (row:row) lits =
    1 + List.length (final_literals row lits)

  fun graph_consumer_with modify (p,q,r) (row:row) lits =
    let
      val bound = [("p",p),("q",q),("r",r)] @ bindings (p,q,r)
      val refuted = List.map refutation (final_literals row lits)
      val graph = G.new () val scope = G.root_scope graph
      val sources = S.new graph scope 4096
        {assumptions= #term row :: List.map literal_term refuted,
         goal=boolSyntax.F}
      val serial = observed_serial row lits
      val inferred = ref NONE
      fun observer (R.CommandEnd {serial=seen,node,provenance}) =
            if seen = serial then
              inferred := SOME (G.representative graph node,provenance)
            else ()
        | observer _ = ()
      val input = TextIO.openString (proof_text row lits Inferred)
      fun run () =
        let
          val packet = Q.parse_graph_packet_with_version
            (graph_options graph scope bound)
            (SmtLib_Logics.parsedicts_of_logic "ALL") "1.3.4" input
          val outcome = Exn.capture (fn () =>
            R.check_contradiction_observing
              {graph=graph,scope=scope,sources=sources,
               proof=modify (SmtLib_GraphProof.proof packet),
               ordinary_limit=4096,template_limit=4096,
               worker=CPC_ProofReplay.graph_bounded_worker [],
               force_worker=NONE,observer=observer}) ()
          val _ = SmtLib_GraphProof.close packet
        in outcome end
      val outcome = Exn.capture run ()
      val cleanup = Exn.capture (fn () =>
        (TextIO.closeIn input;G.close_scope graph scope)) ()
      val _ = Exn.release cleanup
    in
      case (!inferred,outcome) of
          (SOME (clause,provenance),Exn.Res (Exn.Res theorem)) =>
            Derived {clause=clause,hyps=Thm.hyp theorem,
              provenance=SOME provenance,
              closed=Term.aconv (Thm.concl theorem) boolSyntax.F}
        | (SOME (clause,provenance),_) =>
            Derived {clause=clause,hyps=[],provenance=SOME provenance,
              closed=false}
        | (NONE,Exn.Res (Exn.Exn exn)) => Declined (message exn)
        | (NONE,Exn.Exn exn) => Declined (message exn)
        | (NONE,Exn.Res (Exn.Res _)) =>
            raise Fail "graph proof closed without inferring the clause"
    end

  val graph_consumer = graph_consumer_with (fn proof => proof)

  (* The parser keeps (ite c a b) at exactly three children, so a
     conditional occurrence with another count exists only when
     constructed: here the premise's occurrence loses its last child. The
     shared worker then reads three atomic child provenances instead of
     refusing, and the clause still carries the literals. *)
  fun truncate_premise_occurrence (proof:Q.graph_proof) : Q.graph_proof =
    let
      fun cut (SmtLib_Parser.ConstructionOccurrence
                 {value,role,token,children}) =
        SmtLib_Parser.ConstructionOccurrence {value=value,role=role,
          token=token,children=if token = "ite" then
            List.take (children,List.length children - 1)
          else List.map cut children}
      fun command (Q.GraphAssume ("@input",term:F.term)) =
            Q.GraphAssume ("@input",{node= #node term,scope= #scope term,
              binder_blocks= #binder_blocks term,
              source_syntax= #source_syntax term,
              occurrence=cut (#occurrence term)})
        | command other = other
    in {cvc_version= #cvc_version proof,
        commands=List.map command (#commands proof)} end

  (* ---------------------------------------------------------------- *)
  (* Comparison and description                                       *)
  (* ---------------------------------------------------------------- *)

  fun show_provenance provenance = case provenance of
      Prov.AtomicProvenance => "A"
    | Prov.ApplicationProvenance (token,children) =>
        token ^ "(" ^ String.concatWith "," (List.map show_provenance children)
        ^ ")"
    | Prov.EqualityProvenance (left,right) =>
        "Eq(" ^ show_provenance left ^ "," ^ show_provenance right ^ ")"
    | Prov.ConjunctionProvenance (_,children) =>
        "Conj(" ^ String.concatWith "," (List.map show_provenance children)
        ^ ")"
    | Prov.UnavailableProvenance _ => "Unavailable"
    | _ => "Other"

  fun describe observed = case observed of
      Declined text => "refused: " ^ text
    | Derived {clause,provenance,...} =>
        "derived " ^ term_to_string clause ^
        (case provenance of NONE => ""
          | SOME p => " | " ^ show_provenance p)

  (* ---------------------------------------------------------------- *)
  (* Checks                                                           *)
  (* ---------------------------------------------------------------- *)

  fun same_terms terms expected =
    HOLset.equal (HOLset.addList (Term.empty_tmset,terms),
                  HOLset.addList (Term.empty_tmset,expected))
  fun subset terms allowed = List.all (fn term =>
    List.exists (aconv term) allowed) terms
  fun literals (SOME (Accept lits)) = lits
    | literals _ = []

  fun check_outcome label expected observed accepted =
    case (expected,observed) of
        (Refuse needle,Declined text) =>
          require (label ^ ": refusal '" ^ text ^ "' lacks '" ^ needle ^ "'")
            (String.isSubstring needle text)
      | (Accept lits,Derived derived) => accepted lits derived
      | (Refuse _,Derived _) =>
          raise Fail (label ^ ": expected a refusal, got " ^ describe observed)
      | (Accept _,Declined text) =>
          raise Fail (label ^ ": expected a derivation, got " ^ describe
            observed)

  fun check_term_replay (row:row) = case #term_replay row of
      NONE => ()
    | SOME expected =>
        check_outcome (#label row) expected (term_replay row)
          (fn lits => fn {clause,hyps,...} =>
            (require (#label row ^ ": term replay concluded " ^
               term_to_string clause ^ " not " ^
               term_to_string (clause_term lits))
               (aconv clause (clause_term lits));
             require (#label row ^ ": term replay changed its hypotheses")
               (same_terms hyps [#term row])))

  (* Literals, their order and provenance as discovery infers them, and
     the proof still closing to a contradiction over the original
     assumptions and the denied goal. *)
  fun graph_accepted (row:row) provenance_of lits
      {clause,hyps,provenance,closed} =
    (require (#label row ^ ": graph literal " ^ term_to_string clause
       ^ " not " ^ term_to_string (clause_term lits))
       (aconv clause (clause_term lits));
     require (#label row ^ ": graph provenance " ^
       (case provenance of NONE => "none"
         | SOME p => show_provenance p) ^ " not " ^
       show_provenance (provenance_of lits))
       (provenance = SOME (provenance_of lits));
     require (#label row ^ ": graph proof did not close") closed;
     require (#label row ^ ": graph proof used a foreign hypothesis")
       (subset hyps (boolSyntax.mk_neg boolSyntax.F :: #term row ::
          List.map (literal_term o refutation) (final_literals row lits))))

  fun check_graph vars (row:row) = case #graph row of
      NONE => ()
    | SOME expected =>
        check_outcome (#label row) expected
          (graph_consumer vars row (literals (#graph row)))
          (fn lits => graph_accepted row clause_provenance lits)

  (* equiv_elim's term rule derives its clause when the premise is an
     equality and otherwise defers to the declared conclusion: a
     consequence of the premise is kept, anything else is refused. *)
  fun declared_fallbacks () =
    let
      val p = mk_var ("p",bool) val q = mk_var ("q",bool)
      fun replay premise rule declared =
        let val text = "((declare-const p Bool) (declare-const q Bool) \
              \(assume @p1 " ^ premise ^ ") \
              \(step @p2 " ^ declared ^ " :rule " ^ rule ^
              " :premises (@p1)))"
        in Exn.capture (fn () => CPC_ProofReplay.replay_root_for_test
             (parsed text)) () end
      fun derives label premise term rule declared clause =
        case replay premise rule declared of
            Exn.Res theorem =>
              (require (label ^ ": wrong conclusion")
                 (aconv (Thm.concl theorem) clause);
               require (label ^ ": wrong hypotheses")
                 (same_terms (Thm.hyp theorem) [term]);
               Library.check_oracle_tags "CPC clausal fallback" label theorem)
          | Exn.Exn exn =>
              raise Fail (label ^ ": refused: " ^ message exn)
      fun refuses label premise rule declared needle =
        case replay premise rule declared of
            Exn.Res theorem => raise Fail (label ^ ": expected a refusal")
          | Exn.Exn exn => require (label ^ ": diagnostic " ^ message exn)
              (String.isSubstring needle (message exn))
      val conj = boolSyntax.mk_conj (p,q)
      val not_p = boolSyntax.mk_neg p
    in
      derives "equiv_elim1 consequence of a non-equality premise"
        "(and p q)" conj "equiv_elim1" "(or (not p) q)"
        (boolSyntax.mk_disj (not_p,q));
      derives "equiv_elim2 consequence of a non-equality premise"
        "(and p q)" conj "equiv_elim2" "(or p (not q))"
        (boolSyntax.mk_disj (p,boolSyntax.mk_neg q));
      derives "equiv_elim1 declared conclusion equal to the derived one"
        "(= p q)" (boolSyntax.mk_eq (p,q)) "equiv_elim1" "(or (not p) q)"
        (boolSyntax.mk_disj (not_p,q));
      refuses "equiv_elim1 declared non-consequence" "p" "equiv_elim1"
        "(or (not p) q)" "(rule equiv_elim1) failed";
      refuses "equiv_elim1 premise reduced to T with a declared clause"
        "true" "equiv_elim1" "(or (not p) q)" "(rule equiv_elim1) failed";
      refuses "equiv_elim1 declared conclusion differing from the derived"
        "(= p q)" "equiv_elim1" "(or p q)"
        "produced a conclusion different from its certificate"
    end

  (* The forms of equality provenance the rows depend on. The parsers
     never produce ApplicationProvenance ("=",[l,r]) for an equality (a
     binary one is EqualityProvenance, an n-ary one has n children), so
     that form is unreachable through any row and is checked here, on
     equality_provenance directly. *)
  fun equality_provenance_forms () =
    let
      val left = Prov.ApplicationProvenance ("not",[atomic])
      val right = equal2
      fun read label provenance expected =
        require label (CPC_SharedReplayPlan.equality_provenance provenance
          = expected)
    in
      read "EqualityProvenance" (Prov.EqualityProvenance (left,right))
        (left,right);
      read "ApplicationProvenance (=)" (Prov.ApplicationProvenance
        ("=",[left,right])) (left,right);
      read "atomic" atomic (atomic,atomic);
      read "arity-three application" (Prov.ApplicationProvenance
        ("=",[left,right,atomic])) (atomic,atomic)
    end

  (* The conditional rules over a constructed occurrence. *)
  fun constructed_ite_occurrence vars table =
    List.app (fn (row:row) =>
      if #family row <> Conditional orelse #kind row <> ValidPremise then ()
      else
        let val lits = literals (#graph row)
        in check_outcome (#label row) (Accept lits)
             (graph_consumer_with truncate_premise_occurrence vars row lits)
             (graph_accepted row (clause_provenance o List.map flatten))
        end) table

  fun run () =
    let
      val vars as (p,q,r) = (mk_var ("p",bool),mk_var ("q",bool),
                             mk_var ("r",bool))
      val table = rows vars
      fun rule_rows rule = List.filter (fn (row:row) => #rule row = rule) table
      fun group label check = List.app (fn (rule,_,_,_) =>
        (testutils.tprint ("CPC clausal rows: " ^ label ^ " " ^ rule);
         List.app check (rule_rows rule);testutils.OK ()))
        (rule_table (operands vars))
    in
      testutils.tprint "CPC clausal rows: equality provenance forms";
      equality_provenance_forms ();testutils.OK ();
      group "term replay" check_term_replay;
      testutils.tprint "CPC clausal rows: declared conclusion fallbacks";
      declared_fallbacks ();testutils.OK ();
      group "graph consumer" (check_graph vars);
      testutils.tprint "CPC clausal rows: constructed conditional occurrence";
      constructed_ite_occurrence vars table;testutils.OK ()
    end
end
