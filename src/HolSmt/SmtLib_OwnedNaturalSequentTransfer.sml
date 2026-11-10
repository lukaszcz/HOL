(* Owned bounded natural free-variable prefix and original-sequent closure.
   This is not the full SIMP tactic or a new Source-admission route. *)
structure SmtLib_OwnedNaturalSequentTransfer :>
    SmtLib_OwnedNaturalSequentTransfer =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure T = SmtLib_CompactCarrierScheduler
  structure P = SmtReplayProof
  structure F = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  val _ = SmtLib_CompactCarrierScheduler.normalization_ordinal
  val ERR = Feedback.mk_HOL_ERR "SmtLib_OwnedNaturalSequentTransfer"
  datatype owner = Owner of
    {work:W.portfolio,traversal:T.owner,graph:G.graph,root:G.scope,
     sources:S.sources,limits:W.limits,types:int,symbols:int,
     check_type:Type.hol_type -> unit,scope_opened:G.scope -> unit,
     dead:bool ref}
  datatype recipe = Recipe of {left:Term.term,right:Term.term,rule:rule}
  and rule = Reflexive | Beta | Apply of Term.term * recipe
    | Abstract of Term.term * recipe | Trans of recipe * recipe
    | Sym of recipe | Natural of Term.term
  datatype plan = Plan of
    {owner:owner,source:Term.term,target:Term.term,program:recipe,
     variables:Term.term list,assumptions:Term.term list,goal:Term.term,
     types:Type.hol_type list,quota:W.entitlement,amount:int,
     closure_quota:W.entitlement,closure_amount:int,used:bool ref}
  datatype receipt = Receipt of
    {plan:plan,source:G.source,target:G.source,raw_source:G.source,
     raw_target:G.source,theorem:Thm.thm,finished:bool ref,
     query_marker:unit ref option ref}
  datatype query_claim = QueryClaim of {receipt:receipt,marker:unit ref}
  fun close (Owner {work,dead,...}) = (dead := true;W.close work)
  fun protect owner action = action () handle primary =>
    (close owner;raise primary)
  fun active (Owner {work,traversal,graph,root,sources,limits,
                    types,symbols,dead,...}) =
    (if !dead then raise ERR "active" "sequent owner retired" else ();
     W.validate work graph root sources limits;
     T.validate_for work traversal;
     if Type.type_epoch ()=types andalso Term.term_epoch ()=symbols
       then () else raise ERR "active" "declaration retirement changed")
  fun invoke owner action =
    (active owner;let val result=action () in active owner;result end)
  fun begin work {traversal,check_type,scope_opened} =
    let val _=T.validate_for work traversal
        val sources=W.original_sources work
        val graph=S.owning_graph sources val root=S.owning_scope sources
        val owner=Owner {work=work,traversal=traversal,graph=graph,root=root,
          sources=sources,limits=W.semantic_limits work,
          types=Type.type_epoch (),symbols=Term.term_epoch (),
          check_type=check_type,scope_opened=scope_opened,dead=ref false}
    in active owner;owner end handle primary => (W.close work;raise primary)
  fun sides (Recipe {left,right,...}) = (left,right)
  fun eq (Recipe {left,right,...}) = boolSyntax.mk_eq (left,right)
  fun reflexive term = Recipe {left=term,right=term,rule=Reflexive}
  fun apply head recipe =
    let val (a,b)=sides recipe
    in Recipe {left=Term.mk_comb (head,a),right=Term.mk_comb (head,b),
      rule=Apply (head,recipe)} end
  fun abstract variable recipe =
    let val (a,b)=sides recipe
    in Recipe {left=Term.mk_abs (variable,a),right=Term.mk_abs (variable,b),
      rule=Abstract (variable,recipe)} end
  fun trans first second =
    let val (a,b)=sides first val (c,d)=sides second
    in if Term.aconv b c then
      Recipe {left=a,right=d,rule=Trans (first,second)} else
      raise ERR "prepare" "fixed prefix middle changed" end
  fun sym recipe = let val (a,b)=sides recipe
    in Recipe {left=b,right=a,rule=Sym recipe} end
  fun quantify variable body = boolSyntax.mk_forall (variable,body)
  fun implication a b = boolSyntax.mk_imp (a,b)
  fun forall_head variable = Term.rator (quantify variable boolSyntax.T)
  fun natural_variable term = Term.is_var term andalso
    Type.compare (Term.type_of term,numSyntax.num)=EQUAL
  fun bag_variable term = Term.is_var term andalso
    (case Lib.total Type.dom_rng (Term.type_of term) of
       SOME (_,range) => Type.compare (range,numSyntax.num)=EQUAL
     | NONE => false)
  (* Exact old word-entanglement recognizer; no theorem normalization. *)
  fun num_meets_word term =
    let fun below term =
          let val (head,args)=boolSyntax.strip_comb term
          in if Library.same_const head listSyntax.length_tm then false
            else Library.type_contains_word (Term.type_of term) orelse
              List.exists below args end
          handle Feedback.HOL_ERR _ =>
            Library.type_contains_word (Term.type_of term)
        val (_,args)=boolSyntax.strip_comb term
        val head= #1 (boolSyntax.strip_comb term)
    in (Type.compare (Term.type_of term,numSyntax.num)=EQUAL andalso
         below term) orelse
       (Library.type_contains_word (Term.type_of head) andalso
        List.exists (fn arg =>
          Type.compare (Term.type_of arg,numSyntax.num)=EQUAL) args) end
  fun prepare (owner as Owner {work,traversal,graph,sources,limits,...}) =
    protect owner (fn () =>
    let val _=active owner
        val ordinal=T.normalization_ordinal traversal
    in W.with_step work (fn () =>
      let
        fun spend n = (active owner;W.spend work n;active owner)
        val policy_types=ref ([]:Type.hol_type list)
        fun weight ty =
          (spend 1;
           if Type.is_vartype ty then
             (spend (String.size (Type.dest_vartype ty));1)
           else let val {Thy,Tyop,Args}=Type.dest_thy_type ty
                    val _=spend (String.size Thy+String.size Tyop)
                in 1+List.foldl (fn (a,n) => weight a+n) 0 Args end)
        (* Every binder VARIABLE annotation is counted separately. This
           semantic admission never uses count_body for free-variable data. *)
        fun profile cap term =
          let fun walk [] raw inclusive annotations =
                    (raw,inclusive,annotations)
                | walk (term::rest) raw inclusive annotations =
                    let val _=spend 1
                        val raw=raw+1 val inclusive=inclusive+1
                        val _=if raw<=cap andalso inclusive<=cap then ()
                          else raise ERR "prepare" "fully realized bound"
                        val ty=Term.type_of term val w=weight ty
                        val _=policy_types := ty:: !policy_types
                    in if Term.is_comb term then
                         let val (f,x)=Term.dest_comb term
                         in walk (f::x::rest) raw inclusive (annotations+w) end
                       else if Term.is_abs term then
                         let val (v,b)=Term.dest_abs term
                             val _=if inclusive+1<=cap then () else
                               raise ERR "prepare" "binder VARIABLE bound"
                             val t=Term.type_of v val k=weight t
                             val _=policy_types := t:: !policy_types
                         in walk (b::rest) raw (inclusive+1)
                              (annotations+w+k) end
                       else walk rest raw inclusive (annotations+w) end
          in walk [term] 0 0 0 end
        val goal=S.canonical_goal sources
        val assumptions=List.map (G.representative graph)
          (S.assumption_nodes sources)
        val _=List.app (fn term => ignore
          (profile (#input_limit limits) term)) (goal::assumptions)
        (* Legacy successful UNDISCH fold puts the last occurrence outermost.
           Keep the original occurrence list and aliases separately. *)
        val base=List.foldl (fn (a,b) => implication a b) goal assumptions
        val _=ignore (profile (#output_limit limits) base)
        val _=spend 1
        val all_variables=Term.free_vars base
        val entangled=List.exists num_meets_word
          (Library.subterms base)
        val _=if entangled then () else
          if List.exists bag_variable all_variables then
            raise ERR "prepare" "free BAG sequent transfer not implemented"
          else ()
        val variables=if entangled then [] else
          List.filter natural_variable all_variables
        val ordered=List.rev variables
        val source=List.foldl (fn (v,b) => quantify v b)
          base variables
        val _=ignore (profile (#output_limit limits) source)
        val law=HolSmtTheory.NUM_FORALL_TO_INT
        val _=ignore (profile (#template_limit limits) (Thm.concl law))
        fun compile [] term = reflexive term
          | compile (variable::rest) term =
            let val (actual,body)=boolSyntax.dest_forall term
                (* This prefix was constructed privately from ordered.
                   dest_abs may alpha-rename its exported binder. Preserve
                   the original positional SPEC list; substitute ACTUAL. *)
                val _=if natural_variable actual andalso
                    Type.compare (Term.type_of actual,
                      Term.type_of variable)=EQUAL then () else
                  raise ERR "prepare" "legacy SPEC binder type changed"
                val predicate=Term.mk_abs (actual,body)
                val integer=Term.variant (Term.all_vars body)
                  (Term.genvar intSyntax.int_ty)
                val num=intSyntax.mk_Num integer
                (* Input is fully admitted before the bounded substitution.
                   Reserve prospective repeated replacement incidence first. *)
                val (r,i,a)=profile (#output_limit limits) body
                fun occurrences term =
                  if Term.is_var term then
                    if Term.aconv term actual then 1 else 0
                  else if Term.is_comb term then
                    let val (f,x)=Term.dest_comb term
                    in occurrences f+occurrences x end
                  else if Term.is_abs term then
                    let val (v,b)=Term.dest_abs term
                    in if Term.aconv v actual then 0 else occurrences b end
                  else 0
                val count=occurrences body
                val _=if r+2*count<= #output_limit limits andalso
                    i+2*count<= #output_limit limits then () else
                  raise ERR "prepare" "prospective substitution output bound"
                val _=spend (r+i+a+4*count)
                val replacement=Term.subst [{redex=actual,residue=num}] body
                val _=ignore (profile (#output_limit limits) replacement)
                val guard=intSyntax.mk_leq (intSyntax.zero_tm,integer)
                val lhs=quantify actual (Term.mk_comb (predicate,actual))
                val rhs=quantify integer
                  (implication guard (Term.mk_comb (predicate,num)))
                val specialized=Recipe {left=lhs,right=rhs,
                  rule=Natural predicate}
                val left_beta=Recipe
                  {left=Term.mk_comb (predicate,actual),right=body,rule=Beta}
                val left=apply (forall_head actual)
                  (abstract actual left_beta)
                val right_beta=Recipe
                  {left=Term.mk_comb (predicate,num),right=replacement,
                   rule=Beta}
                val inner=compile rest replacement
                val imp=Term.mk_comb (boolSyntax.implication,guard)
                val right=apply (forall_head integer)
                  (abstract integer (apply imp (trans right_beta inner)))
            in trans (sym left) (trans specialized right) end
        val program=compile ordered source
        val (_,target)=sides program
        val total=ref 0
        fun quote term =
          let val (r,i,a)=profile (#output_limit limits) term
          in total := !total+r+i+a end
        fun program_quote (value as Recipe {left,right,rule}) =
          (quote left;quote right;quote (eq value);
           case rule of Reflexive => () | Beta => ()
             | Apply (_,inner) => program_quote inner
             | Abstract (_,inner) => program_quote inner
             | Trans (a,b) => (program_quote a;program_quote b)
             | Sym inner => program_quote inner
             | Natural _ =>
                 (* Actual SPEC may alpha-rename binders: its ALPHA conclusion
                    wraps the whole already forecast specialized equality. *)
                 quote (boolSyntax.mk_eq (eq value,eq value)))
        val _=program_quote program
        val _=quote (boolSyntax.mk_eq (source,source))
        val _=quote (boolSyntax.mk_eq (target,target))
        val amount= !total
        val quota=W.reserve work
          {role=W.LocalCarrier,ordinal=ordinal,amount=amount}
        val _=total := 0
        (* Complete receiver syntax BEFORE its later policy/kernel work.
           SPEC inserts original variables only; surviving hypotheses are
           exact original canonical assumptions, separately quoted. *)
        val _=quote (boolSyntax.mk_eq (target,target))
        val _=quote source
        fun specs [] term = term
          | specs (v::rest) term =
            let val (bound,body)=boolSyntax.dest_forall term
                val _=quote term
                val next=Term.subst [{redex=bound,residue=v}] body
                val _=quote next
            in specs rest next end
        val body=specs ordered source
        fun premises [] term hypotheses =
              (quote term;List.app quote hypotheses)
          | premises (a::rest) term hypotheses =
            let val (antecedent,next)=boolSyntax.dest_imp term
                val _=if Term.aconv antecedent a then () else
                  raise ERR "prepare" "original implication order changed"
                val _=quote term val _=quote a val _=quote next
                val _=List.app quote (a::hypotheses)
            in premises rest next (a::hypotheses) end
        val _=premises (List.rev assumptions) body []
        val _=quote (boolSyntax.mk_eq (goal,goal))
        (* Closed denial clause also has to be quoted before any proof:
           originals -> original denied Goal -> denied quantified sequent. *)
        val denied=G.representative graph (S.denied_goal_node sources)
        val conclusion=boolSyntax.mk_neg target
        val _=quote (implication target boolSyntax.F)
        val _=quote conclusion
        val _=quote (implication denied conclusion)
        val law_term=List.foldr (fn (a,b) => implication a b)
          (implication denied conclusion) assumptions
        val _=quote law_term
        val _=quote (boolSyntax.mk_eq (law_term,law_term))
        val _=quote (boolSyntax.mk_eq (target,target))
        val _=List.app quote (denied::assumptions)
        val closure_amount= !total
        val closure_quota=W.reserve work
          {role=W.GoalDenial,ordinal=ordinal,amount=closure_amount}
      in Plan {owner=owner,source=source,target=target,program=program,
        variables=ordered,assumptions=assumptions,goal=goal,
        types=List.rev (!policy_types),quota=quota,amount=amount,
        closure_quota=closure_quota,closure_amount=closure_amount,
        used=ref false}
      end)
    end)
  fun execute (plan as Plan
      {owner=owner as Owner {work,graph,root,check_type,scope_opened,...},
       source,target,
       program,types,quota,amount,used,...}) = protect owner (fn () =>
    W.with_step work (fn () =>
    let val _=active owner
        val _=if !used then raise ERR "execute" "sequent plan consumed"
          else used := true
        val _=W.consume work quota amount
        val _=List.app (fn ty => invoke owner (fn () => check_type ty)) types
        fun run (value as Recipe {left,right,rule}) =
          let fun call f = invoke owner f
              val th=case rule of Reflexive => call (fn () => Thm.REFL left)
                | Beta => call (fn () => Thm.BETA_CONV left)
                | Apply (head,p) =>
                    let val inner=run p
                    in call (fn () => Thm.AP_TERM head inner) end
                | Abstract (v,p) =>
                    let val inner=run p
                    in call (fn () => Thm.ABS v inner) end
                | Trans (a,b) =>
                    let val first=run a val second=run b
                    in call (fn () => Thm.TRANS first second) end
                | Sym p => let val inner=run p
                    in call (fn () => Thm.SYM inner) end
                | Natural predicate =>
                    let val th=call (fn () =>
                          Thm.SPEC predicate HolSmtTheory.NUM_FORALL_TO_INT)
                        val alpha=call (fn () =>
                          Thm.ALPHA (Thm.concl th) (eq value))
                    in call (fn () => Thm.EQ_MP alpha th) end
              val _=if null (Thm.hyp th) andalso
                  Term.aconv (Thm.concl th) (eq value) then () else
                raise ERR "execute" "fixed prefix proof changed"
          in th end
        val theorem=run program
        val maximum= #output_limit (W.semantic_limits work)
        val raw_source=invoke owner (fn () =>
          G.import graph root maximum source)
        val opened_source=invoke owner (fn () =>
          G.record_opened_view graph root maximum (#node raw_source))
        val raw_target=invoke owner (fn () =>
          G.import graph root maximum target)
        val opened_target=invoke owner (fn () =>
          G.record_opened_view graph root maximum (#node raw_target))
        val _=G.validate_opened_view graph root
          (#node raw_source) opened_source
        val _=G.validate_opened_view graph root
          (#node raw_target) opened_target
        val seen=ref ([]:G.scope list)
        fun observe child =
          let val node=G.closure_child_node graph root child
          in case G.view graph node of
            G.Application _ =>
              let val (a,b)=G.closure_application_children graph root child
              in observe a;observe b end
          | G.AdmittedBinder _ =>
              let val closure=G.closure_child_binder graph root child
                  val data=G.binder_closure_data graph root closure
                  val frame= #body_frame data
                  val _=if List.exists (fn old => old=frame) (!seen) then ()
                    else (seen := frame:: !seen;
                      G.validate_scope graph frame;
                      invoke owner (fn () => scope_opened frame);
                      G.validate_scope graph frame)
              in observe (G.binder_closure_body graph root closure) end
          | _ => () end
        val _=observe (G.closure_root graph root (#node opened_source))
        val _=observe (G.closure_root graph root (#node opened_target))
        val _=G.validate_opened_view graph root
          (#node raw_source) opened_source
        val _=G.validate_opened_view graph root
          (#node raw_target) opened_target
    in Receipt {plan=plan,source=opened_source,target=opened_target,
      raw_source=raw_source,raw_target=raw_target,theorem=theorem,
      finished=ref false,query_marker=ref NONE} end))
  fun held expected (receipt as Receipt
      {plan=Plan {owner=owner as Owner {work,graph,root,...},...},
       source,target,raw_source,raw_target,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "owner" "different expected Work";
      active owner;G.validate_scope graph root;
      G.validate_opened_view graph root (#node raw_source) source;
      G.validate_opened_view graph root (#node raw_target) target;receipt)
     handle primary => (W.close expected;raise primary))
  fun description_for expected receipt =
    let val Receipt {plan=Plan {owner=Owner {sources,...},variables,...},
                     source,target,...}=held expected receipt
    in {source=source,target=target,variables=variables,
      original_sources=sources} end
  fun transfer_theorem_for expected receipt =
    let val Receipt {theorem,...}=held expected receipt in theorem end
  (* Exact WHOLE original import is distinct from opened.#original,
     which names the canonical RAW representative. Never re-import or
     reconstruct a semantic Source pair to recover this held identity. *)
  fun target_import_for expected receipt =
    let val Receipt {plan=Plan {owner=Owner {graph,root,...},...},
          raw_target,target,...}=held expected receipt
        val (imported,opened)=G.imported_opened_source graph root
          (#original raw_target) (#node target)
        val _=if Portable.pointer_eq
              (#bridge imported,#bridge raw_target) andalso
            Portable.pointer_eq (#bridge opened,#bridge target) then () else
          raise ERR "target_import_for" "different exact held whole bridges"
    in raw_target end
    handle primary => (W.close expected;raise primary)
  fun close_proof_internal receiver expected receipt evidence =
    let val Receipt {plan=Plan
          {owner=owner as Owner {work,graph,root,sources,limits,...},
           variables,assumptions,goal,source,target,closure_quota,
           closure_amount,...},theorem,finished,query_marker,...}=
            held expected receipt
        fun run operation =
          (ignore (held expected receipt);
           let val result=operation ()
           in ignore (held expected receipt);result end)
    in protect owner (fn () => W.with_step work (fn () =>
      let val _=case (receiver,!query_marker) of
            (NONE,NONE) => ()
          | (SOME expected,SOME actual) =>
              if Portable.pointer_eq (expected,actual) then () else
                raise ERR "close_proof" "different stripped receiver"
          | _ => raise ERR "close_proof" "stripped receiver owns closure"
          val _=if !finished then raise ERR "close_proof" "closure consumed"
            else finished := true
          val _=P.validate_closed_fact graph root
            (#template_limit limits) evidence
          val _=if P.closed_node evidence= #node
                (#target (description_for expected receipt)) then () else
            raise ERR "close_proof" "different transferred sequent"
          val proof=P.closed_original evidence
          val _=if null (Thm.hyp proof) then () else
            raise ERR "close_proof" "sequent proof has local hypotheses"
          (* These are small ORIGINAL variables, never retained large terms
             inserted below remaining binders. The complete prepared source
             and all surviving original hypotheses were admitted earlier. *)
          val _=W.consume work closure_quota closure_amount
          val alpha=run (fn () =>
            Thm.ALPHA (Thm.concl proof) target)
          val raw=run (fn () => Thm.EQ_MP alpha proof)
          val generalized=run (fn () =>
            Thm.EQ_MP (Thm.SYM theorem) raw)
          val specialized=List.foldl
            (fn (v,th) => run (fn () => Thm.SPEC v th))
            generalized variables
          val result=List.foldl (fn (assumption,th) =>
            let val assumed=run (fn () => Thm.ASSUME assumption)
            in run (fn () => Thm.MP th assumed) end)
            specialized (List.rev assumptions)
          val _=if Term.aconv (Thm.concl result) goal then () else
            raise ERR "close_proof" "original canonical Goal changed"
          val aligned=run (fn () => Thm.EQ_MP
            (Thm.ALPHA (Thm.concl result) goal) result)
          val answer=run (fn () =>
            Thm.EQ_MP (Thm.SYM (S.goal_bridge sources)) aligned)
          val _=S.check_goal sources answer
      in answer end)) end
  fun close_proof expected receipt evidence =
    close_proof_internal NONE expected receipt evidence
  fun claim_query expected receipt =
    let val Receipt {plan=Plan {owner=owner as Owner {work,...},...},
          finished,query_marker,...}=held expected receipt
    in protect owner (fn () => W.with_step work (fn () =>
      if !finished orelse Option.isSome (!query_marker) then
        raise ERR "claim_query" "sequent receiver already claimed"
      else let val _=W.spend work 3 val marker=ref ()
               val _=query_marker := SOME marker
           in QueryClaim {receipt=receipt,marker=marker} end)) end
  fun query_receipt expected (QueryClaim {receipt,marker}) =
    let val Receipt {query_marker,...}=held expected receipt
    in case !query_marker of SOME actual =>
         if Portable.pointer_eq (marker,actual) then receipt else
           raise ERR "query_receipt" "different stripped receiver"
       | NONE => raise ERR "query_receipt" "unclaimed stripped receiver" end
    handle primary => (W.close expected;raise primary)
  fun query_traversal_for expected claim =
    let val Receipt {plan=Plan {owner=Owner {traversal,...},...},...}=
          query_receipt expected claim
    in traversal end
  fun close_query_proof expected (claim as QueryClaim {marker,...}) evidence =
    close_proof_internal (SOME marker) expected
      (query_receipt expected claim) evidence
  fun portfolio_for expected receipt =
    let val Receipt {plan=Plan
          {owner=owner as Owner {work,graph,root,sources,limits,
                                check_type,...},
           variables,assumptions,goal,target,closure_quota,
           closure_amount,...},theorem,finished,query_marker,target=opened,...}=
            held expected receipt
        fun run operation =
          (ignore (held expected receipt);
           let val result=operation ()
           in ignore (held expected receipt);result end)
    in protect owner (fn () => W.with_step work (fn () =>
      let val _=if Option.isSome (!query_marker) then
            raise ERR "portfolio" "stripped receiver owns closure" else ()
          val _=if !finished then raise ERR "portfolio" "closure consumed"
            else finished := true
          val _=W.consume work closure_quota closure_amount
          val canonical=G.representative graph (#node opened)
          val asserted=run (fn () => Thm.ASSUME canonical)
          val raw=run (fn () => Thm.EQ_MP
            (Thm.ALPHA canonical target) asserted)
          val generalized=run (fn () =>
            Thm.EQ_MP (Thm.SYM theorem) raw)
          val specialized=List.foldl
            (fn (v,th) => run (fn () => Thm.SPEC v th))
            generalized variables
          val proved=List.foldl (fn (assumption,th) =>
            let val assumed=run (fn () => Thm.ASSUME assumption)
            in run (fn () => Thm.MP th assumed) end)
            specialized (List.rev assumptions)
          val proved=run (fn () => Thm.EQ_MP
            (Thm.ALPHA (Thm.concl proved) goal) proved)
          val denied=G.representative graph (S.denied_goal_node sources)
          val negative=run (fn () => Thm.ASSUME denied)
          val contradiction=run (fn () =>
            Thm.MP (Thm.NOT_ELIM negative) proved)
          val negated=run (fn () =>
            Thm.NOT_INTRO (Thm.DISCH canonical contradiction))
          val law=List.foldr (fn (a,th) => run
            (fn () => Thm.DISCH a th))
            (run (fn () => Thm.DISCH denied negated)) assumptions
          val _=if null (Thm.hyp law) then () else
            raise ERR "portfolio" "closed denial law retained hypotheses"
          val imported=run (fn () => G.import graph root
            (#output_limit limits) (Thm.concl law))
          val view=run (fn () => G.record_opened_view graph root
            (#output_limit limits) (#node imported))
          val recorded=run (fn () => P.record_closed_from_import
            graph root {node= #node view,theorem=law,
              template_limit= #template_limit limits,
              check_type=fn ty => run (fn () => check_type ty)})
          val inputs=S.assumption_nodes sources @
            [S.denied_goal_node sources]
          val premises=Portable.mapi
            (fn i => fn _ => F.original graph root sources i) inputs
          val target_denial=G.application graph root
            (G.constant graph root boolSyntax.negation,#node opened)
          val checked=F.apply graph root
            {law=F.recorded_closed graph root recorded,
             premises=premises,target=target_denial}
          val portfolio=F.validate_portfolio_with_work work
            {assumptions=[],goal= #node opened,denied=checked}
          val result=GP.from_portfolio_with_work work portfolio
          val _=GP.validate_with_work work result
          val _=if GP.source_nodes result=inputs andalso
              Portable.pointer_eq (GP.original_sources result,sources)
            then () else raise ERR "portfolio" "original prefix changed"
      in result end)) end

end
