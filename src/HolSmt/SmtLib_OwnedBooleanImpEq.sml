structure SmtLib_OwnedBooleanImpEq :> SmtLib_OwnedBooleanImpEq =
struct
  structure G=SmtReplayGraph
  structure W=SmtReplayInvocationWork
  structure P=SmtReplayProof
  structure O=SmtLib_OwnedContextImpCanon
  structure H=SmtLib_OwnedIncomingHypFV
  val _=SmtLib_OwnedIncomingHypFV.prepare
  val _=SmtReplayProof.prepare_source_eqt_flip
  structure Scope=SmtReplayOwnedScopeReceipt
  val _=SmtReplayProof.source_condition_statement_for
  val _=SmtLib_OwnedContextImpCanon.receipt_validation_for
  val _=Cond_rewr.false_template
  val _=SmtReplayProof.prepare_source_false_law
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedBooleanImpEq"
  type incoming={work:W.portfolio,validation:O.receipt_validation,
    hypotheses:P.source_hyp_fv_origins list,
    equality_hyp:H.receipt option ref}
  datatype action=DiscardTruth | Positive | Negative | KeepEquality
    | LoopEquality | FixedFalse of Cond_rewr.false_template
    | FlipEquality | NeedEqualityHyp
  datatype false_plan=FalsePlan of
    {work:W.portfolio,raw:incoming,
     evidence:P.source_condition_evidence,frame:Scope.receipt,
     template:Cond_rewr.false_template,template_proof:Thm.thm,
     statement:Term.term,closing:Term.term option,
     types:Type.hol_type list,check_type:Type.hol_type -> unit,
     lower:P.source_false_law_plan}
  datatype prepared=Clause of P.source_condition_rule_plan
    | FalseLaw of false_plan
    | LoopPair of P.source_condition_loop_plan
    | PairedEqT of P.source_eqt_flip_plan
  datatype plan=Plan of
    {work:W.portfolio,raw:incoming,
     batches:prepared list list,used:bool ref}
  datatype receipt=Receipt of
    {work:W.portfolio,raw:incoming,
     entries:P.source_condition_evidence list}
  fun protect expected operation=operation()handle primary=>
    (W.close expected;raise primary)
  fun raw_guard expected(raw:incoming)=
    (if Portable.pointer_eq(expected,#work raw)then ()else raise ERR
       "raw_guard" "foreign expected Work";
     ignore(O.receipt_validation_for expected(#validation raw));
     List.app(fn held=>ignore(P.source_condition_hyp_fv_origins_for
       expected held))(#hypotheses raw);
     case !(#equality_hyp raw)of NONE=>()
       | SOME held=>ignore(H.entries_for expected held))
  fun plan_guard expected(Plan{work,raw,...})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else
         raise ERR "plan_guard" "foreign expected Work";
       raw_guard expected raw))
  fun receipt_guard expected(Receipt{work,raw,entries})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else
         raise ERR "receipt_guard" "foreign expected Work";
       raw_guard expected raw;
       List.app(fn evidence=>ignore
         (P.source_condition_statement_for expected evidence))entries))
  fun false_guard expected(FalsePlan
      {work,raw,evidence,template,statement,...})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else raise ERR
         "false_guard" "foreign expected Work";
       raw_guard expected raw;
       ignore(P.source_condition_statement_for expected evidence);
       let val data=Cond_rewr.false_template_data template
           val proof= #proof data
       in if null(Tag.axioms_of(Thm.tag proof))andalso
           List.all(fn name=>name="DISK_THM")
             (#1(Tag.dest_tag(Thm.tag proof)))andalso
           Term.uptodate_term(Thm.concl proof)andalso
           Term.uptodate_term statement then ()else raise ERR
         "false_guard" "captured fixed template changed"end))
  fun prepare_false expected raw evidence template check_type=
    protect expected(fn()=>
    let val parent=P.source_condition_statement_for expected evidence
        val frame= #frame parent
        val limits=W.semantic_limits expected
        fun live()=(raw_guard expected raw;
          ignore(P.source_condition_statement_for expected evidence))
        val(template_proof,condition,result,statement,closing,types)=
          W.with_step expected(fn()=>
          let val _=live()
              val data=Cond_rewr.false_template_data template
              val proof= #proof data val condition= #condition data
              val result= #result data
              val template_limit= #template_limit limits
              val policies=ref([]:Type.hol_type list)
              val budget=ref(0:IntInf.int)
              fun tick n=(live();W.spend expected n)
              fun guarded operation=
                (live();let val answer=operation()in live();answer end)
              fun bounded term=
                (case SmtReplayImport.bounded_raw_size template_limit term of
                   SOME n=>tick n | NONE=>raise ERR "false_quote"
                     "original raw template allowance";
                 case SmtReplayImport.bounded_binder_size template_limit
                     term of SOME n=>tick n | NONE=>raise ERR "false_quote"
                       "original binder template allowance")
              fun typ ty=
                (tick 1;policies:=ty:: !policies;
                 if Type.is_vartype ty then
                   (tick(String.size(Type.dest_vartype ty));1)
                 else let val {Thy,Tyop,Args}=Type.dest_thy_type ty
                          val _=tick(String.size Thy+String.size Tyop)
                      in 1+List.foldl(fn(t,n)=>n+typ t)0 Args end)
              fun metrics term=
                let val _=tick 1 val a=typ(Term.type_of term)
                in if Term.is_abs term then
                    let val(v,b)=Term.dest_abs term
                        val domain=typ(Term.type_of v)
                        val(r,i,c)=metrics b
                    in(1+r,2+i,a+domain+c)end
                  else if Term.is_comb term then
                    let val(f,x)=Term.dest_comb term
                        val(r,i,b)=metrics f val(s,j,c)=metrics x
                    in(1+r+s,1+i+j,a+b+c)end else(1,1,a)end
              fun record hypotheses term=
                let fun cost value=
                      let val _=bounded value val(r,i,a)=metrics value
                      in IntInf.fromInt(r+i+a)end
                    val amount=List.foldl(fn(t,n)=>n+cost t)0
                      (term::hypotheses)
                    val _=budget:= !budget+amount
                in if !budget<=IntInf.fromInt(W.work_limit expected-
                      #charged(W.audit expected))then ()else raise ERR
                    "false_quote" "original cumulative Work"end
              val hypotheses=guarded(fn()=>Thm.hyp proof)
              val conclusion=guarded(fn()=>Thm.concl proof)
              val _=if guarded(fn()=>Term.aconv condition
                    (#statement parent))then ()else raise ERR "false_quote"
                  "template does not match this authentic clause"
              val(closing,statement)=case hypotheses of []=>
                    (NONE,conclusion)
                | [hypothesis]=>
                    if guarded(fn()=>Term.aconv hypothesis condition)andalso
                        guarded(fn()=>Term.aconv conclusion result)then
                      (SOME hypothesis,guarded(fn()=>
                        boolSyntax.mk_imp(hypothesis,conclusion)))
                    else raise ERR "false_quote"
                      "fixed conditional template Hyp changed"
                | _=>raise ERR "false_quote" "fixed template has extra Hyp"
              val(left,right)=guarded(fn()=>
                boolSyntax.dest_imp_only statement)
              val _=if guarded(fn()=>Term.aconv left condition)andalso
                  guarded(fn()=>Term.aconv right result)then ()else raise ERR
                "false_quote" "exact captured template endpoint changed"
              (* TF/FT have one native Hyp: forecast the actual DISCH input
                 and result before closing it. x_eq_false is already closed. *)
              val _=case closing of NONE=>record []conclusion
                | SOME _=>(record hypotheses conclusion;record []statement)
              val _=if !budget<=IntInf.fromInt(W.work_limit expected-
                    #charged(W.audit expected))then
                  W.spend expected(IntInf.toInt(!budget))else raise ERR
                    "false_quote" "original cumulative Work"
              val _=live()
          in(proof,condition,result,statement,closing,
            List.rev(!policies))end)
        val _=live()
        val lower=P.prepare_source_false_law expected
          {evidence=evidence,law_statement=statement,check_type=check_type}
        val value=FalsePlan{work=expected,raw=raw,evidence=evidence,
          template=template,template_proof=template_proof,frame=frame,
          statement=statement,closing=closing,types=types,
          check_type=check_type,lower=lower}
        val _=false_guard expected value
    in value end)
  fun execute_false expected(value as FalsePlan
      {frame,template_proof,statement,closing,types,check_type,lower,...})=
    protect expected(fn()=>
      (false_guard expected value;
       (* Both portfolios were reserved during prepare. All schema/Source
          policies precede this template's first native DISCH/import. *)
       let val ready=P.admit_source_false_law expected lower
           val _=false_guard expected value
           val _=W.with_step expected(fn()=>List.app(fn ty=>
             (false_guard expected value;check_type ty;
              false_guard expected value))types)
           val fact=W.with_step expected(fn()=>
             let fun guarded operation=
                   (false_guard expected value;
                    let val answer=operation()
                    in false_guard expected value;answer end)
                 val sd=Scope.description_for expected frame
                 val graph= #graph sd val scope= #scope sd
                 val cap= #template_limit(W.semantic_limits expected)
                 val closed=case closing of NONE=>template_proof
                   | SOME condition=>guarded(fn()=>
                       SmtReplayRuleObservation.DISCH condition template_proof)
                 val _=if null(Thm.hyp closed)andalso
                     guarded(fn()=>Term.aconv(Thm.concl closed)statement)
                     then ()else raise ERR "execute_false"
                       "native closed template differs from quote"
                 val imported=guarded(fn()=>G.import graph scope cap
                   (Thm.concl closed))
                 val opened=guarded(fn()=>G.record_opened_view graph scope cap
                   (#node imported))
                 val fact=guarded(fn()=>P.record_closed_from_import
                   graph scope{node= #node opened,theorem=closed,
                     template_limit=cap,check_type=fn _=>()})
             in fact end)
           val _=false_guard expected value
           val result=P.execute_source_false_law expected
             {ready=ready,law=fact}
           val _=false_guard expected value
       in result end))
  fun prepare expected{raw,check_type}=
    protect expected(fn()=>
    let val validation=O.prepare_receipt_validation expected raw
        val entries= #entries(O.receipt_validation_for expected validation)
        (* These producers own their actions. Prepare actual incoming Hyp
           BEFORE entering any classifier action or future UNDISCH. *)
        val rows=Portable.mapi(fn index=>fn evidence=>
          (ignore(O.receipt_validation_for expected validation);
           let val held=P.prepare_source_condition_hyp_fv_origins
                 expected evidence
               val _=ignore(O.receipt_validation_for expected validation)
           in(evidence,held,index)end))entries
        val raw:incoming={work=expected,validation=validation,
          hypotheses=List.map(fn(_,held,_)=>held)rows,
          equality_hyp=ref NONE}
        (* Existing P-only policies retain their flow. Once a genuine H
           receipt is held, every later callback validates it too. *)
        fun policy ty=case !(#equality_hyp raw)of NONE=>check_type ty
          | SOME _=>(raw_guard expected raw;check_type ty;
              raw_guard expected raw)
        val limits=W.semantic_limits expected
        val output= #output_limit limits
        fun choose(evidence,origins,index)=
          let val d=P.source_condition_statement_for expected evidence
              val actual_hyp=P.source_condition_hyp_fv_origins_for
                expected origins
              fun live()=(raw_guard expected raw;
                ignore(P.source_condition_statement_for expected evidence))
              val equality_hyp=case !(#equality_hyp raw)of NONE=>NONE
                | SOME held=>
                    let val h=H.entries_for expected held
                        val r=O.receipt_validation_for expected validation
                        val row=List.nth(#entries h,index)
                        val _=if #ordinal h= #ordinal r andalso
                            #assumption_slot h= #assumption_slot r andalso
                            #source_occurrence h= #source_occurrence r
                            andalso Portable.pointer_eq(#evidence row,
                              evidence)andalso Portable.pointer_eq
                              (#frame row,#frame d)andalso
                            Portable.pointer_eq(#statement row,
                              #statement d)then ()else raise ERR "prepare"
                              "different authentic equality Hyp row"
                    in SOME {frame= #frame row,statement= #statement row,
                      variables= #variables row,unknown= #unknown row}end
              val selected=W.with_step expected(fn()=>
                let fun tick n=(live();W.spend expected n)
                    fun guarded operation=
                      (live();let val result=operation()
                       in live();result end)
                    val statement= #statement d
                    (* FIRST inspect bounded public syntax, before any
                       metric can open an unsupported binder body. *)
                    fun binder_free term=
                      let fun pending [] visits=true
                            | pending(current::rest)visits=
                              if visits>=output then raise ERR "prepare"
                                "actual local syntax exceeds original output"
                              else(tick 1;
                                if Term.is_abs current then false
                                else if Term.is_comb current then
                                  let val(f,x)=guarded(fn()=>
                                            Term.dest_comb current)
                                  in pending(f::x::rest)(visits+1)end
                                else pending rest(visits+1))
                      in pending[term]0 end
                    val _=if binder_free statement then ()else raise ERR
                      "prepare"
                      "authentic stock prerequisite: binder/function rule"
                    val _=if guarded(fn()=>Term.aconv statement
                        (#statement actual_hyp))then ()else raise ERR
                      "prepare" "authentic incoming Hyp statement changed"
                    fun bound metric=case metric output statement of
                        SOME count=>tick count | NONE=>raise ERR "prepare"
                          "actual local syntax exceeds original output"
                    val _=bound SmtReplayImport.bounded_raw_size
                    val _=bound SmtReplayImport.bounded_binder_size
                    fun same(a,b)=(tick 1;Term.aconv a b)
                    fun constant term value=Term.is_const term andalso
                      Term.same_const term value
                    fun has_binder term=
                      (tick 1;if Term.is_abs term then true
                       else if Term.is_comb term then
                         let val(a,b)=guarded(fn()=>Term.dest_comb term)
                         in has_binder a orelse has_binder b end else false)
                    fun member term values=List.exists
                      (fn old=>(tick 1;Term.term_eq term old))values
                    fun add term values=if member term values then values
                      else(tick 1;term::values)
                    fun free term values=
                      (tick 1;if Term.is_var term then add term values
                       else if Term.is_comb term then
                         let val(a,b)=guarded(fn()=>Term.dest_comb term)
                         in free b(free a values)end else values)
                    fun occurs pattern term=
                      (tick 1;if same(pattern,term)then true
                       else if Term.is_comb term then
                         let val(a,b)=guarded(fn()=>Term.dest_comb term)
                         in occurs pattern a orelse occurs pattern b end
                       else false)
                    fun prerequisite reason=raise ERR "prepare"
                      ("authentic stock prerequisite: "^reason)
                    fun hyp_present variable=
                      if member variable(#variables actual_hyp)then true
                      else if null(#unknown actual_hyp)then false
                      else prerequisite "actual Hyp-only FV unresolved"
                    fun equality left right=
                      let val hd=case equality_hyp of NONE=>actual_hyp
                            | SOME row=>row
                          fun present variable=
                            if member variable(#variables hd)then SOME true
                            else if null(#unknown hd)then SOME false
                            else NONE
                          val lhs=free left[]
                          fun coverage []=SOME true
                            | coverage(variable::rest)=
                                if member variable lhs then coverage rest
                                else case present variable of
                                  SOME true=>coverage rest
                                | SOME false=>SOME false | NONE=>NONE
                      in case coverage(free right[])of
                        NONE=>NeedEqualityHyp
                      | SOME false=>FlipEquality
                      | SOME true=>
                          if not(Term.is_var left)then KeepEquality
                          else case present left of
                            SOME true=>KeepEquality
                          | SOME false=>FlipEquality
                          | NONE=>NeedEqualityHyp end
                    val _=if has_binder statement then
                        prerequisite "binder/function rule"else ()
                    val action=if constant statement boolSyntax.T then
                        DiscardTruth
                      else if constant statement boolSyntax.F then
                        FixedFalse(Cond_rewr.false_template
                          Cond_rewr.FalseConclusion)
                      else if boolSyntax.is_imp_only statement then
                        prerequisite "CONJ_DISCH conditional rule"
                      else if boolSyntax.is_eq statement then
                        let val(left,right)=guarded(fn()=>
                              boolSyntax.dest_eq statement)
                            val _=if Type.compare(Term.type_of left,
                                Type.bool)=EQUAL then ()else
                              prerequisite "non-Boolean equality"
                            val loop=if Term.is_var left then
                                member left(free right[])
                              else occurs left right
                        in if loop then LoopEquality
                          else if constant left boolSyntax.T andalso
                              constant right boolSyntax.F then
                            FixedFalse(Cond_rewr.false_template
                              Cond_rewr.TruthEqualsFalse)
                          else if constant left boolSyntax.F andalso
                              constant right boolSyntax.T then
                            FixedFalse(Cond_rewr.false_template
                              Cond_rewr.FalseEqualsTruth)
                          else if constant left boolSyntax.T orelse
                              constant left boolSyntax.F then
                            prerequisite "constant-left orientation/template"
                          else if Term.is_var left then equality left right
                          else if boolSyntax.is_eq left then
                            prerequisite "nested equation flip"
                          else
                            equality left right
                        end
                      else if boolSyntax.is_neg statement then
                        let val operand=guarded(fn()=>
                              boolSyntax.dest_neg statement)
                        in if boolSyntax.is_eq operand then
                            prerequisite "negative equality symmetry schema"
                          else if Term.is_var operand then
                            if hyp_present operand then Negative
                            else DiscardTruth
                          else Negative end
                      else if Term.is_var statement then
                        if hyp_present statement then Positive
                        else DiscardTruth
                      else
                        let val(head,_)=guarded(fn()=>
                              HolKernel.strip_comb statement)
                        in if Term.is_const head andalso
                            #Thy(Term.dest_thy_const head)="marker"andalso
                            #Name(Term.dest_thy_const head)="Abbrev"then
                            prerequisite "Abbrev/function conversion"
                          else Positive end
                    val _=live()
                in action end)
              val frame= #frame d
              val caller= #scope(Scope.description_for expected frame)
              fun rule steps terminal=Clause(P.prepare_source_condition_rule
                expected{evidence=evidence,frame=frame,caller=caller,
                  steps=steps,terminal=terminal,check_type=policy})
          in case selected of DiscardTruth=>[]
            | Positive=>[rule[]P.SourceTruth]
            | Negative=>[rule[]P.SourceFalse]
            | KeepEquality=>[rule[]P.SourceEquality]
            | LoopEquality=>
                let fun loop_rule steps=P.prepare_source_condition_rule
                      expected{evidence=evidence,frame=frame,caller=caller,
                        steps=steps,terminal=P.SourceTruth,
                        check_type=fn ty=>
                          (raw_guard expected raw;check_type ty;
                           raw_guard expected raw)}
                    val first=loop_rule[]
                    val second=loop_rule[P.EvidenceSymmetry]
                in [LoopPair(P.prepare_source_condition_loop expected
                  {first=first,second=second})]end
            | FixedFalse template=>[FalseLaw(prepare_false expected raw
                evidence template policy)]
            | FlipEquality=>
                [PairedEqT(P.prepare_source_eqt_flip expected
                  {evidence=evidence,check_type=fn ty=>
                    (raw_guard expected raw;check_type ty;
                     raw_guard expected raw)})]
            | NeedEqualityHyp=>
                (case !(#equality_hyp raw)of SOME _=>raise ERR "prepare"
                   ("authentic stock prerequisite: "^
                    "actual Hyp-only FV unresolved")
                 | NONE=>
                     let val _=raw_guard expected raw
                         (* H owns actions; this is outside the classifier. *)
                         val held=H.prepare expected validation
                         val _=raw_guard expected raw
                         val _=W.with_step expected(fn()=>
                           (raw_guard expected raw;W.spend expected 2;
                            #equality_hyp raw:=SOME held;
                            raw_guard expected raw))
                     in choose(evidence,origins,index)end)end
        val batches=List.map choose rows
        val result=Plan{work=expected,raw=raw,batches=batches,used=ref false}
        val _=plan_guard expected result
    in result end)
  fun execute expected(plan as Plan{work,raw,batches,used})=
    protect expected(fn()=>
      (plan_guard expected plan;
       if !used then raise ERR "execute" "primitive plan consumed"else ();
       used:=true;
       let fun run batch=List.concat(List.map(fn prepared=>
             (plan_guard expected plan;
              let val result=case prepared of Clause clause=>
                    [P.execute_source_condition_rule expected clause]
                  | FalseLaw value=>[execute_false expected value]
                  | LoopPair value=>
                      let val ready=P.admit_source_condition_loop
                            expected value
                          val _=plan_guard expected plan
                      in P.execute_source_condition_loop
                        expected ready end
                  | PairedEqT value=>
                      let val ready=P.admit_source_eqt_flip expected value
                          val _=plan_guard expected plan
                      in P.execute_source_eqt_flip expected ready end
              in plan_guard expected plan;result end))batch)
           val entries=List.concat(List.map run batches)
           val receipt=Receipt{work=work,raw=raw,entries=entries}
           val _=receipt_guard expected receipt
       in receipt end))
  fun entries_for expected(receipt as Receipt{raw,entries,...})=
    (receipt_guard expected receipt;
     let val data=O.receipt_validation_for expected(#validation raw)
     in {ordinal= #ordinal data,assumption_slot= #assumption_slot data,
       source_occurrence= #source_occurrence data,entries=entries}end)
end
