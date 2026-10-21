(* Shared compact syntax and fixed kernel rules. No operand is expanded. *)
structure SmtReplayNamedContext :> SmtReplayNamedContext =
struct
  structure O = SmtReplayRuleObservation
  val ERR = Feedback.mk_HOL_ERR "SmtReplayNamedContext"
  datatype boundary = Empty | Leaf of int | Split of boundary * boundary
  fun make_tree start count =
    if count = 0 then Empty
    else if count = 1 then Leaf start
    else let val half = count div 2 in
      Split (make_tree start half, make_tree (start + half) (count - half))
    end
  fun tree_term terms Empty = boolSyntax.T
    | tree_term terms (Leaf index) = Vector.sub (terms, index)
    | tree_term terms (Split (left, right)) =
        boolSyntax.mk_conj (tree_term terms left, tree_term terms right)
  fun project Empty _ = []
    | project (Leaf _) theorem = [theorem]
    | project (Split (left, right)) theorem =
        project left (O.CONJUNCT1 theorem) @
        project right (O.CONJUNCT2 theorem)
  fun tree_proof proofs Empty = boolTheory.TRUTH
    | tree_proof proofs (Leaf index) = Vector.sub (proofs, index)
    | tree_proof proofs (Split (left, right)) =
        O.CONJ (tree_proof proofs left) (tree_proof proofs right)

  datatype 'node view = Atom | Constant of Term.term
    | Application of 'node * 'node
  fun constructor_rhs names (Application (operator,operand)) =
        SOME (Term.mk_comb (names operator,names operand))
    | constructor_rhs _ (Constant atom) = SOME atom
    | constructor_rhs _ Atom = NONE
  fun spine observe node =
    let fun walk node arguments=case observe node of
            Application (operator,operand)=>
              walk operator (operand::arguments)
          | Constant atom=>SOME (atom,arguments)
          | Atom=>NONE
    in walk node [] end
  fun operands observe constant arity node =
    case spine observe node of SOME (head,arguments)=>
        if Term.same_const head constant andalso length arguments=arity then
          SOME arguments else NONE
      | NONE=>NONE
  fun equality observe node =
    case operands observe boolSyntax.equality 2 node of
        SOME [left,right]=>SOME (left,right) | _=>NONE
  (* No public constructor/getter can mint a substitution witness. *)
  datatype literal_substitution=LiteralSubstitution of
    {variable:Term.term,template:Term.term,input_limit:int,output_limit:int,
     guard:unit -> unit}
  datatype 'node primitive = ReflexiveName of 'node
    | Symmetry | Transitivity | Congruence | EqualityMP
    | ApplyNamedArgument of 'node | ImplicationMP
    | SubstituteLiteral of literal_substitution
  fun primitive_using invalid names recipe proofs =
    case (recipe,proofs) of
        (ReflexiveName node,[]) => O.REFL (names node)
      | (Symmetry,[proof]) => O.SYM proof
      | (Transitivity,[left,right]) => O.TRANS left right
      | (Congruence,[left,right]) => O.MK_COMB (left,right)
      | (EqualityMP,[equality,proof]) => O.EQ_MP equality proof
      | (ApplyNamedArgument node,[proof]) => O.AP_THM proof (names node)
      | (ImplicationMP,[law,premise]) => O.MP law premise
      | (SubstituteLiteral(LiteralSubstitution
          {variable,template,guard,...}),[equality,proof]) =>
          (guard();O.SUBST_LITERAL variable equality template proof)
      | _ => raise invalid ()
  fun primitive names = primitive_using
    (fn () => ERR "primitive" "incorrect fixed recipe arity") names

  type profile =
    {raw:IntInf.int,inc:IntInf.int,ann:IntInf.int,ty:IntInf.int}
  datatype shape = HeldSyntax of Term.term
    | EqualitySyntax of shape * shape | ApplicationSyntax of shape * shape
  (* Pure expression compilation. The caller owns all actual bounds and
     the scan/construction observer. Neither shapes nor constructed Terms
     confer theorem, native quota, Source or scoped-closure permission. *)
  fun ignore_shape (_:shape)=()
  fun describe_shape observe (profile:Term.term -> profile)
      type_work same_type shape =
    (observe shape;case shape of
        HeldSyntax term=>let val p=profile term in(p,Term.type_of term)end
      | ApplicationSyntax(function,argument)=>
          let val(f,ty)=describe_shape observe profile type_work same_type
                function
              val(x,argument_type)=describe_shape observe profile
                type_work same_type argument
              val(domain,range)=Type.dom_rng ty
              val _=if same_type domain argument_type then ()else
                raise ERR "freeze" "constructor argument type differs"
              val own=type_work range
          in({raw=1+ #raw f+ #raw x,inc=1+ #inc f+ #inc x,
            ann=own+ #ann f+ #ann x,ty=own}:profile,range)end
      | EqualitySyntax(left,right)=>
          let val(a,ty)=describe_shape observe profile type_work same_type
                left
              val(b,wanted)=describe_shape observe profile type_work
                same_type right
              val _=if same_type ty wanted then ()else
                raise ERR "freeze" "constructor result type differs"
          in({raw=3+ #raw a+ #raw b,inc=3+ #inc a+ #inc b,
            ann=6+3* #ty a+ #ann a+ #ann b,ty=1}:profile,Type.bool)end)
  fun realize_shape observe shape=
    (observe shape;case shape of HeldSyntax term=>term
      | ApplicationSyntax(left,right)=>Term.mk_comb
          (realize_shape observe left,realize_shape observe right)
      | EqualitySyntax(left,right)=>boolSyntax.mk_eq
          (realize_shape observe left,realize_shape observe right))
  type admission =
    {pay:IntInf.int -> unit,member:Term.term -> bool,guard:unit -> unit,
     template_limit:int,type_work_limit:int,error:string -> exn}
  type fixed_admission =
    {pay:IntInf.int -> unit,guard:unit -> unit,
     template_limit:int,type_work_limit:int,error:string -> exn}
  fun fixed_admission (admission:admission):fixed_admission =
    {pay= #pay admission,guard= #guard admission,
     template_limit= #template_limit admission,
     type_work_limit= #type_work_limit admission,error= #error admission}
  fun type_weight_using pay error ceiling root =
    let val memo=ref ([]:(Type.hol_type * IntInf.int) list)
        fun spend amount=pay (IntInf.fromInt amount)
        fun find _ []=NONE
          | find ty ((old,n)::rest)=
              (spend 1;if Portable.pointer_eq (ty,old) then SOME n
               else find ty rest)
        fun visit ty=case find ty (!memo) of SOME n=>n | NONE=>
          let val _=spend 1
              val n=if Type.is_vartype ty then
                  let val bytes=String.size (Type.dest_vartype ty)
                      val _=spend bytes
                  in 1+IntInf.fromInt bytes end
                else List.foldl (fn(child,total)=>total+visit child) 1
                  (#2 (Type.dest_type ty))
              val _=if n<=ceiling then () else
                raise error "native Type work exceeded"
              val _=memo:=(ty,n):: !memo
          in n end
    in visit root end
  fun type_weight (admission:admission) = type_weight_using
    (#pay admission) (#error admission)
    (IntInf.fromInt (#type_work_limit admission))
  fun inspector_using (admission:admission) storage =
    let val cap=IntInf.fromInt (#template_limit admission)
        val ceiling=IntInf.fromInt (#type_work_limit admission)
        fun spend amount=(#pay admission) (IntInf.fromInt amount)
        fun fail message=raise (#error admission) message
        val {find,publish}=storage spend
        fun profile term=case find term of SOME value=>value
          | NONE=>
          let val _=spend 1
              val own=type_weight admission (Term.type_of term)
              val value:profile=if Term.is_comb term then
                  let val (a,b)=Term.dest_comb term
                      val x=profile a val y=profile b
                  in {raw=1+ #raw x+ #raw y,inc=1+ #inc x+ #inc y,
                      ann=own+ #ann x+ #ann y,ty=own} end
                else if Term.is_abs term then
                  fail "binder requires its actual local native admission"
                else if Term.is_var term then
                  if (#member admission) term then
                    {raw=1,inc=1,ann=own,ty=own}
                  else fail "unowned compact variable"
                else if Term.is_const term then
                  {raw=1,inc=1,ann=own,ty=own}
                else fail "unknown compact syntax"
              val _=if #raw value<=cap andalso #inc value<=cap then () else
                fail "native compact template exceeded"
              val _=if #ann value<=ceiling then () else
                fail "native annotations exceeded"
              val _=publish term value
          in value end
        val _=(#guard admission) ()
    in {profile=profile} end
  (* Public admission callbacks keep their original per-inspector list.
     Only an authentic frozen block selects the persistent private store. *)
  fun inspector admission = inspector_using admission (fn spend =>
    let val memo=ref ([]:(Term.term * profile) list)
        fun find _ []=NONE
          | find term ((old,value)::rest)=
              (spend 1;
               if Portable.pointer_eq (term,old) then SOME value
               else find term rest)
    in {find=fn term=>find term (!memo),
        publish=fn term=>fn value=>memo:=(term,value):: !memo} end)
  (* One compact, binder-free literal occurrence. This is a fixed kernel
     recipe, not a realized/query substitution API or a theorem intake. *)
  fun literal_substitution_preview
      (admitted:fixed_admission) profile
      (LiteralSubstitution{variable,template,input_limit,output_limit,
        guard=witness_guard}) equality source =
    let
      val pay= #pay admitted val guard= #guard admitted
      val error= #error admitted
      (* Three admission selectors, eight cap observations/calculations
         and four actual local helper closures. *)
      val _=pay 6 val _=witness_guard()val _=guard()val _=pay 15
      val cap=IntInf.fromInt(#template_limit admitted)
      val input=IntInf.min(cap,IntInf.fromInt input_limit)
      val output=IntInf.min(cap,IntInf.fromInt output_limit)
      val ceiling=IntInf.fromInt(#type_work_limit admitted)
      val whole=profile template
      fun actual_input term=
        let val p=profile term val _=pay 6
        in if #raw p<=input andalso #inc p<=input then p else
          raise error "literal substitution native input exceeded"end
      val _=actual_input template
      val _=actual_input equality val source_profile=actual_input source
      val _=pay 5
      val _=if Term.is_var variable andalso
          Type.compare(Term.type_of variable,Type.bool)=EQUAL then()else
        raise error "literal substitution placeholder is not Boolean"
      val _=pay 5
      val(left,right)=boolSyntax.dest_eq equality
      val a=profile left val b=profile right
      fun spelling term=
        (pay 1;if Term.is_var term then
           let val _=pay 2 val(name,_)=Term.dest_var term
               val amount=IntInf.fromInt(String.size name)
           in pay amount;amount end
         else if Term.is_const term then
           let val _=pay 3 val{Thy,Name,...}=Term.dest_thy_const term
               val amount=IntInf.fromInt(String.size Thy+String.size Name)
           in pay amount;amount end
         else if Term.is_comb term then
           let val _=pay 2 val(f,x)=Term.dest_comb term
           in spelling f+spelling x end
         else raise error "binder in literal substitution")
      val variable_bytes=spelling variable
      fun occurrences term=
        (pay 1;if Term.is_var term then
           let val bytes=spelling term
               val _=pay(1+bytes+variable_bytes)
           in if Term.var_compare(term,variable)=EQUAL then 1 else 0 end
         else if Term.is_const term then 0
         else if Term.is_comb term then
           let val _=pay 2 val(f,x)=Term.dest_comb term
           in occurrences f+occurrences x end
         else raise error "binder in literal substitution template")
      val count=occurrences template
      val _=pay 2
      val _=if count=1 then()else
        raise error "literal substitution needs exactly one occurrence"
      val _=pay 1
      val own= #ty(profile variable)
      fun portfolio maximum(p:profile)=
        let val _=pay 18
            val raw= #raw whole+ #raw p-1
            val inc= #inc whole+ #inc p-1
            val ann= #ann whole+ #ann p-own
        in if raw<=maximum andalso inc<=maximum andalso
            ann<=ceiling then()else
          raise error "literal substitution instance exceeded"end
      val _=portfolio input a val _=portfolio output b
      val _=pay 2
      val text=spelling template+spelling left+spelling right
      val _=pay 5
      val nodes= #raw whole
      val combs=(nodes-1)div 2
      val source_nodes= #raw source_profile
      val source_annotations= #ann source_profile
      val _=pay 2
      val comparison=1+text+own
      (* Each fixed template has three variable incidences: its unique
         owned redex and the two genuine schema operand occurrences.
         A singleton substitution pays setup9, a node pass, each rebuilt
         Comb, and the three actual name/Boolean-Type probes separately. *)
      val _=pay 4
      val substitution_pass=9+nodes+combs+3*comparison
      val _=pay 4
      val source_match=1+2*(source_nodes+text+source_annotations)
      (* Metadata prediction is additional work: two real substitutions
         with their two external binding rows/cells8, then its own match. *)
      val _=pay 2
      val _=pay(8+2*substitution_pass)
      val input=Term.subst[{redex=variable,residue=left}]template
      val result=Term.subst[{redex=variable,residue=right}]template
      val _=pay source_match
      val _=if Term.aconv input source then()else
        raise error "literal substitution source differs"
      val p=profile result
      (* Native SUBST has an independent FVL node/worklist pass and at
         most six small-set comparisons (three additions + membership).
         Setup38 covers replacement4/FVL-list1/itlist-closures2/base-tuple5,
         equality destructor11/binding-rows8/result-tuple5/branch1/thm1.
         Hyp/tag union and the ordinary primitive result portfolio remain
         fully charged by the original shared preparer and XOR executor. *)
      val _=pay 4
      val free_variables=nodes+2*combs+6*comparison
      val _=pay 4
      val _=pay(38+free_variables+2*substitution_pass+source_match)
      val _=pay 6 val _=witness_guard()val _=guard()val _=pay 2
    in (p,HeldSyntax result)end
  fun prepare_fixed_quoted quote conclusion proof_hypotheses
      (admission:fixed_admission) profile names
      recipe proofs =
    let val cap=IntInf.fromInt (#template_limit admission)
        val ceiling=IntInf.fromInt (#type_work_limit admission)
        fun fail message=raise (#error admission) message
        fun eq (a:profile) (b:profile):profile=
          {raw=3+ #raw a+ #raw b,inc=3+ #inc a+ #inc b,
           ann=6+3* #ty a+ #ann a+ #ann b,ty=1}
        fun app a b=
          let val f=profile a val x=profile b
              val ty= #2 (Type.dom_rng (Term.type_of a))
              val own=type_weight_using (#pay admission) (#error admission)
                ceiling ty
          in {raw=1+ #raw f+ #raw x,inc=1+ #inc f+ #inc x,
              ann=own+ #ann f+ #ann x,ty=own}:profile end
        val _=List.app (fn proof=>ignore (profile (conclusion proof))) proofs
        fun equation proof=boolSyntax.dest_eq (conclusion proof)
        fun held term=HeldSyntax term
        val (result,shape)=case (recipe,proofs) of
            (ReflexiveName node,[])=>
              let val x=names node val p=profile x
              in (eq p p,EqualitySyntax (held x,held x)) end
          | (Symmetry,[proof])=>let val(a,b)=equation proof
              in (eq (profile b) (profile a),
                  EqualitySyntax(held b,held a)) end
          | (Transitivity,[left,right])=>
              let val(a,_)=equation left val(_,c)=equation right
              in (eq (profile a) (profile c),
                  EqualitySyntax(held a,held c)) end
          | (Congruence,[left,right])=>
              let val(a,b)=equation left val(x,y)=equation right
              in (eq (app a x) (app b y),EqualitySyntax
                  (ApplicationSyntax(held a,held x),
                   ApplicationSyntax(held b,held y))) end
          | (EqualityMP,[equality,_])=>
              let val(_,b)=equation equality in (profile b,held b) end
          | (ApplyNamedArgument node,[proof])=>
              let val(a,b)=equation proof val x=names node
              in (eq (app a x) (app b x),EqualitySyntax
                  (ApplicationSyntax(held a,held x),
                   ApplicationSyntax(held b,held x))) end
          | (ImplicationMP,[law,_])=>
              let val(_,right)=boolSyntax.dest_imp_only (conclusion law)
              in (profile right,held right) end
          | (SubstituteLiteral witness,[equality,proof])=>
              literal_substitution_preview admission profile witness
                (conclusion equality)(conclusion proof)
          | _=>fail "incorrect fixed recipe arity"
        val _=if #raw result<=cap andalso #inc result<=cap then () else
          fail "native result template exceeded"
        val hypotheses=List.concat (List.map proof_hypotheses proofs)
        fun weight (p:profile)= #raw p+ #inc p+ #ann p
        val portfolio=List.foldl (fn(term,total)=>
          total+weight (profile term)) (1+weight result) hypotheses
        val _=if portfolio<=ceiling then () else
          fail "native result/Hyp/Type work exceeded"
        val count=IntInf.fromInt (List.length hypotheses)
        val amount=portfolio+count*(count+2)+20
        val _=quote amount
        val _=(#guard admission) ()
    in {proofs=proofs,shape=shape,hypotheses=hypotheses} end
  fun prepare_fixed_observed conclusion proof_hypotheses
      (admission:fixed_admission) profile names opcode proofs =
    prepare_fixed_quoted (#pay admission) conclusion proof_hypotheses
      admission profile names opcode proofs
  fun prepare_fixed_using admission profile names recipe proofs =
    prepare_fixed_observed Thm.concl Thm.hyp admission profile names
      recipe proofs
  fun prepare_fixed admission names recipe proofs =
    let val inspect=inspector admission
    in prepare_fixed_using (fixed_admission admission) (#profile inspect)
      names recipe proofs
    end
  fun matches (HeldSyntax held) actual=
        Portable.pointer_eq(held,actual) orelse
        (Thm.kernelid="stdknl" andalso Term.aconv held actual)
    | matches (ApplicationSyntax(a,b)) actual=
        Term.is_comb actual andalso
        let val(x,y)=Term.dest_comb actual
        in matches a x andalso matches b y end
    | matches (EqualitySyntax(a,b)) actual=
        Term.is_comb actual andalso
        let val(f,y)=Term.dest_comb actual
        in Term.is_comb f andalso
          let val(c,x)=Term.dest_comb f
          in Term.is_const c andalso
            Term.same_const c boolSyntax.equality andalso
            matches a x andalso matches b y end end

  datatype 'node boolean_rule = PolicyImplicationMP | PolicyConjunction
    | PolicyConjunctLeft | PolicyConjunctRight | PolicyNotIntro
    | PolicyNotElim | PolicyEqTrueElim | PolicyEqFalseElim
    | PolicyContradiction of 'node
  datatype boolean_shape = PBHeld of Term.term | PBFalse
    | PBNegation of boolean_shape
    | PBImplication of boolean_shape * boolean_shape
    | PBConjunction of boolean_shape * boolean_shape
  (* Boolean expression grammar only. This does not select or execute a
     proof rule and cannot upgrade a model to a checked theorem. *)
  fun boolean_syntax observe shape=
    (observe shape;case shape of PBHeld term=>HeldSyntax term
      | PBFalse=>HeldSyntax boolSyntax.F
      | PBNegation a=>ApplicationSyntax
          (HeldSyntax boolSyntax.negation,boolean_syntax observe a)
      | PBImplication(a,b)=>ApplicationSyntax(ApplicationSyntax
          (HeldSyntax boolSyntax.implication,boolean_syntax observe a),
          boolean_syntax observe b)
      | PBConjunction(a,b)=>ApplicationSyntax(ApplicationSyntax
          (HeldSyntax boolSyntax.conjunction,boolean_syntax observe a),
          boolean_syntax observe b))
  fun prepare_boolean_quoted quote conclusion proof_hypotheses
      (admission:fixed_admission) profile names
      opcode proofs =
    let val cap=IntInf.fromInt (#template_limit admission)
        val ceiling=IntInf.fromInt (#type_work_limit admission)
    val _=List.app (fn proof=>ignore(profile(conclusion proof))) proofs
    fun concl proof=conclusion proof
    fun false_term term=Term.is_const term andalso
      Term.same_const term boolSyntax.F
    val shape=case(opcode,proofs) of
        (PolicyImplicationMP,[law,_])=>
          PBHeld(#2(boolSyntax.dest_imp(concl law)))
      | (PolicyConjunction,[a,b])=>
          PBConjunction(PBHeld(concl a),PBHeld(concl b))
      | (PolicyConjunctLeft,[proof])=>
          PBHeld(#1(boolSyntax.dest_conj(concl proof)))
      | (PolicyConjunctRight,[proof])=>
          PBHeld(#2(boolSyntax.dest_conj(concl proof)))
      | (PolicyNotIntro,[proof])=>
          let val(a,b)=boolSyntax.dest_imp(concl proof)
          in if false_term b then PBNegation(PBHeld a) else
            raise (#error admission) "negation premise is not to F"
          end
      | (PolicyNotElim,[proof])=>
          PBImplication(PBHeld(boolSyntax.dest_neg(concl proof)),PBFalse)
      | (PolicyEqTrueElim,[proof])=>
          let val(a,b)=boolSyntax.dest_eq(concl proof)
          in if Term.is_const b andalso
              Term.same_const b boolSyntax.T then PBHeld a else
            raise (#error admission) "equality premise is not to T"
          end
      | (PolicyEqFalseElim,[proof])=>
          let val(a,b)=boolSyntax.dest_eq(concl proof)
          in if false_term b then PBNegation(PBHeld a) else
            raise (#error admission) "equality premise is not to F"
          end
      | (PolicyContradiction node,[proof])=>
          if false_term(concl proof) then PBHeld(names node) else
            raise (#error admission) "contradiction premise is not F"
      | _=>raise (#error admission) "incorrect fixed rule arity"
    fun binary (a:profile) (b:profile)
          :profile=
      {raw=3+ #raw a+ #raw b,inc=3+ #inc a+ #inc b,
       ann=9+ #ann a+ #ann b,ty=1}
    fun describe(PBHeld term)=profile term
      | describe PBFalse={raw=1,inc=1,ann=1,ty=1}
      | describe(PBNegation child)=
          let val a=describe child
          in {raw=2+ #raw a,inc=2+ #inc a,ann=4+ #ann a,ty=1} end
      | describe(PBImplication(a,b))=binary(describe a)(describe b)
      | describe(PBConjunction(a,b))=binary(describe a)(describe b)
    val result=describe shape
    val _=if #raw result<= cap andalso
        #inc result<= cap then () else
      raise (#error admission) "native compact result exceeded"
    val hypotheses=List.concat(List.map proof_hypotheses proofs)
    fun weight(p:profile)= #raw p+ #inc p+ #ann p
    val amount=List.foldl (fn(term,total)=>total+weight(profile term))
      (1+weight result) hypotheses
    val _=if amount<= ceiling then () else
      raise (#error admission) "native result/Hyp/Type work exceeded"
    val count=IntInf.fromInt(length hypotheses)
    val _=quote (amount+count*(count+2)+20)
    in {shape=shape,hypotheses=hypotheses} end
  fun prepare_boolean_observed conclusion proof_hypotheses
      (admission:fixed_admission) profile names opcode proofs =
    prepare_boolean_quoted (#pay admission) conclusion proof_hypotheses
      admission profile names opcode proofs
  fun prepare_boolean_using admission profile names opcode proofs =
    prepare_boolean_observed Thm.concl Thm.hyp admission profile names
      opcode proofs
  fun boolean_using invalid names opcode proofs =
    case(opcode,proofs) of
              (PolicyImplicationMP,[a,b])=>O.MP a b
            | (PolicyConjunction,[a,b])=>O.CONJ a b
            | (PolicyConjunctLeft,[proof])=>
                O.CONJUNCT1 proof
            | (PolicyConjunctRight,[proof])=>
                O.CONJUNCT2 proof
            | (PolicyNotIntro,[proof])=>Thm.NOT_INTRO proof
            | (PolicyNotElim,[proof])=>O.NOT_ELIM proof
            | (PolicyEqTrueElim,[proof])=>O.EQ_MP
                (O.SYM proof) boolTheory.TRUTH
            | (PolicyEqFalseElim,[proof])=>
                O.D_EQF_ELIM proof
            | (PolicyContradiction node,[proof])=>
                O.CCONTR (names node) proof
            | _=>raise invalid ()
  fun boolean_matches shape actual =
    let
    fun fixed wanted actual=Term.is_const actual andalso
      Term.same_const actual wanted
    fun binary operator a b actual=
      Term.is_comb actual andalso
      let val(f,y)=Term.dest_comb actual
      in Term.is_comb f andalso
        let val(c,x)=Term.dest_comb f
        in fixed operator c andalso matches a x andalso matches b y end
      end
    and matches(PBHeld held) actual=
          Portable.pointer_eq(held,actual) orelse
          (Thm.kernelid="stdknl" andalso Term.aconv held actual)
      | matches PBFalse actual=fixed boolSyntax.F actual
      | matches(PBNegation child) actual=
          Term.is_comb actual andalso
          let val(f,x)=Term.dest_comb actual
          in fixed boolSyntax.negation f andalso matches child x end
      | matches(PBImplication(a,b)) actual=
          binary boolSyntax.implication a b actual
      | matches(PBConjunction(a,b)) actual=
          binary boolSyntax.conjunction a b actual
    in matches shape actual end

  type ('node,'proof) equality_operations =
    {key:'node -> int,same:'node * 'node -> bool,
     application:'node -> ('node * 'node) option,
     reflexive:'node -> 'proof,symmetry:'proof -> 'proof,
     transitivity:'proof -> 'proof -> 'proof,
     congruence:'proof * 'proof -> 'proof,definition:'node -> 'proof,
     error:string -> exn}
  fun equality_programme (operations:('node,'proof) equality_operations)
      {rule,left,right,premises=compact} =
    let
    fun symmetric_chain () =
      let
        val neighbors = ref (Redblackmap.mkDict Int.compare)
        fun add (from,to,proof) =
          let val key = (#key operations) from in
            neighbors := Redblackmap.insert (!neighbors,key,
              (to,proof) :: Option.getOpt
                (Redblackmap.peek (!neighbors,key),[])) end
        val _ = List.app (fn ((a,b),proof) =>
          (add (a,b,proof);add (b,a,(#symmetry operations) proof))) compact
        fun search [] [] _ = raise (#error operations)
              "no symmetric transitivity path"
          | search [] back seen = search (List.rev back) [] seen
          | search ((node,path) :: rest) back seen =
              if (#same operations) (node,right) then path else
                let
                  fun enqueue ((next,proof),(back,seen)) =
                    if Redblackset.member (seen,(#key operations) next) then
                      (back,seen)
                    else ((next,(#transitivity operations) path proof) :: back,
                      Redblackset.add (seen,(#key operations) next))
                  val (back,seen) = List.foldl enqueue (back,seen)
                    (Option.getOpt (Redblackmap.peek
                      (!neighbors,(#key operations) node),[]))
                in search rest back seen end
      in search [(left,(#reflexive operations) left)] []
        (Redblackset.singleton Int.compare ((#key operations) left)) end
    val memo = ref (Redblackmap.mkDict
      (fn ((a,b),(c,d)) => case Int.compare (a,c) of
         EQUAL => Int.compare (b,d) | result => result))
    fun prove (lhs,rhs) =
      if (#same operations) (lhs,rhs) then (#reflexive operations) lhs
      else case List.find
          (fn ((a,b),_) => (#same operations) (a,lhs) andalso (#same
            operations) (b,rhs)) compact of
        SOME (_,proof) => proof
      | NONE => (case List.find
          (fn ((a,b),_) => (#same operations) (a,rhs) andalso (#same
            operations) (b,lhs)) compact of
            SOME (_,proof) => (#symmetry operations) proof
          | NONE =>
              let val key = ((#key operations) lhs,(#key operations) rhs) in
                case Redblackmap.peek (!memo,key) of SOME proof => proof
                | NONE =>
                    let
                      val proof = case ((#application operations)
                        lhs,(#application operations) rhs) of
                        (SOME (f,x),SOME (g,y)) =>
                          (#transitivity operations) ((#definition
                            operations) lhs)
                            ((#transitivity operations)
                              ((#congruence operations) (prove (f,g),prove
                                (x,y)))
                              ((#symmetry operations) ((#definition
                                operations) rhs)))
                      | _ => raise (#error operations)
                          "unproved congruence leaf"
                      val _ = memo := Redblackmap.insert (!memo,key,proof)
                    in proof end
              end)
    val proof = case rule of
        "refl" => if List.null compact andalso (#same operations)
          (left,right) then
            (#reflexive operations) left
          else raise (#error operations) "invalid reflexivity endpoints"
      | "symm" => (case compact of
            [((a,b),proof)] => if (#same operations) (a,right) andalso
              (#same operations) (b,left) then
                (#symmetry operations) proof else raise (#error operations)
                  "invalid symmetry endpoints"
          | _ => raise (#error operations) "symmetry expects one premise")
      | "trans" =>
          let
            (* Preserve solver premise order. The collection above is
               reversed solely while preparing checked projections. *)
            fun chain [] _ = raise (#error operations) "empty transitivity"
              | chain [((a,b),proof)] expected =
                  if (#same operations) (a,expected) andalso (#same
                    operations) (b,right) then proof else
                    raise (#error operations)
                      "transitivity endpoint mismatch"
              | chain (((a,b),proof) :: rest) expected =
                  if (#same operations) (a,expected) then (#transitivity
                    operations) proof (chain rest b) else
                    raise (#error operations) "transitivity chain mismatch"
          in chain (List.rev compact) left end
      | "cong" => prove (left,right)
      | "trans-star" => symmetric_chain ()
      | _ => raise (#error operations) "unknown equality procedure"
    in proof end

  datatype named_inst_shape = NamedInstVariable of string * Type.hol_type
    | NamedInstConstant of Term.term * Type.hol_type
    | NamedInstApplication of named_inst_shape * named_inst_shape
  type named_inst_admission =
    {pay:IntInf.int -> unit,type_weight:Type.hol_type -> IntInf.int,
     member:Term.term -> bool,template_limit:int,type_work_limit:int,
     error:string -> string -> exn}
  fun prepare_named_inst_using result_events
      (admission:named_inst_admission)
      {substitution,theorem} =
    let val pay= #pay admission
        fun spend n=pay (IntInf.fromInt n)
        val ceiling=IntInf.fromInt (#type_work_limit admission)
        val template_limit= #template_limit admission
        val type_total=ref (0:IntInf.int)
        fun type_work ty =
          let val value=(#type_weight admission) ty
              val total= !type_total+value
              val _=if total<=ceiling then type_total:=total else
                raise (#error admission) "policy_closed_inst"
                  "native Type portfolio exceeded"
          in value end
        fun same_type left right =
          let val a = type_work left val b = type_work right
              val _ = pay (1+a+b)
          in Type.compare (left,right) = EQUAL end
        fun var_data term =
          (spend 2;
           if Term.is_var term then Term.dest_var term else
             raise (#error admission) "policy_closed_inst"
               "schema substitution must be variable to named variable")
        fun same_variable (name,ty) (other,wanted) =
          (spend (String.size name + String.size other + 1);
           name = other andalso same_type ty wanted)
        fun validate_substitution [] = ()
          | validate_substitution ({redex,residue}::rest) =
            let val _ = spend 1
                val source = var_data redex
                val target = var_data residue
                val _ = if same_type (#2 source) (#2 target) then () else
                  raise (#error admission) "policy_closed_inst"
                    "different schema substitution types"
                val _ = if (#member admission) residue then ()
                  else raise (#error admission) "guard"
                    "unowned compact variable"
                fun coherent [] = ()
                  | coherent ({redex,residue}::tail) =
                    (spend 1;
                     if same_variable source (var_data redex) andalso
                         not (same_variable target (var_data residue)) then
                       raise (#error admission) "policy_closed_inst"
                         "conflicting repeated schema hole"
                     else coherent tail)
                val _ = coherent rest
            in validate_substitution rest end
        val _ = validate_substitution substitution
        val _ = spend 2
        val input = Thm.concl theorem
        val hypotheses = Thm.hyp theorem
        val _ = if null hypotheses then () else
          raise (#error admission) "policy_closed_inst" "schema is not closed"
        val _ = spend 2
        val tag = Thm.tag theorem
        val (oracles,_) = Tag.dest_tag tag
        val _ = spend 1
        val _ = if null (Tag.axioms_of tag) then () else
          raise (#error admission) "policy_closed_inst"
            "unexpected schema axioms"
        fun oracle_work [] amount = amount
          | oracle_work (oracle::rest) amount =
            let val _ = spend 1
                val _ = spend (String.size oracle + 9)
                val _ = if oracle = "DISK_THM" then () else
                  raise (#error admission) "policy_closed_inst"
                    "unexpected schema tag"
            in oracle_work rest
                 (amount + 2*IntInf.fromInt (String.size oracle) + 3) end
        val tag_work = oracle_work oracles (5:IntInf.int)
        (* Same size-first order as the compact guard. No output or Type
           work is inferred from a caller coefficient or constructed Term. *)
        fun raw [] count = count
          | raw (current::rest) count =
            (spend 1;
             if count >= template_limit then
               raise (#error admission) "guard"
                 "expanded compact proof template"
             else
               let val _ = spend 1
               in if Term.is_comb current then
                    let val _ = spend 4
                        val (left,right) = Term.dest_comb current
                    in raw (left::right::rest) (count+1) end
                  else
                    (spend 1;
                     if Term.is_abs current then
                       raise (#error admission) "policy_closed_inst"
                         "binder schema requires a bounded local proof block"
                     else raw rest (count+1))
               end)
        val _ = spend 1
        val raw_nodes = raw [input] 0
        fun replacement source [] = NONE
          | replacement source ({redex,residue}::rest) =
            (spend 1;
             if same_variable source (var_data redex) then SOME residue
             else replacement source rest)
        (* Profile every actual input annotation and the corresponding
           future output annotation. Variable replacements preserve Type
           exactly; constants/apps are untouched. Pay future local matches
           before INST, including equal-name cloned variable comparisons. *)
        fun derive current =
          let val _ = spend 2
              val ty = Term.type_of current
              val annotation = type_work ty
              val _ = pay (1+annotation)
              val _ = spend 1
          in if Term.is_var current then
              let val source = var_data current
                  val output = case replacement source substitution of
                      SOME residue => residue | NONE => current
                  val _ = if (#member admission) output
                    then ()
                    else raise (#error admission) "guard"
                      "unowned compact variable"
                  val (name,wanted) = var_data output
                  val _ = pay
                    (7+2*IntInf.fromInt (String.size name)+2*annotation)
                  val _ = spend 1
              in NamedInstVariable (name,wanted) end
             else if Term.is_comb current then
              let val _ = spend 2
                  val (left,right) = Term.dest_comb current
                  val a = derive left val b = derive right
                  val _ = pay (6+2*annotation)
                  val _ = spend 1
              in NamedInstApplication (a,b) end
             else
              let val _ = spend 1
                  val _ = if Term.is_const current then () else
                    raise (#error admission) "policy_closed_inst"
                      "unknown closed schema syntax"
                  val _ = spend 3
                  val {Thy,Name,...} = Term.dest_thy_const current
                  val bytes = IntInf.fromInt (String.size Thy) +
                    IntInf.fromInt (String.size Name)
                  val _ = pay (6+2*annotation+2*bytes)
                  val _ = spend 1
              in NamedInstConstant (current,ty) end
          end
        val shape = derive input
        (* Output Raw/Inclusive equal the measured binder-free input, not
           an expanded graph coefficient. Repeated annotation debit above
           is cumulative and independent of the syntax cap. *)
        val _ = pay (2*IntInf.fromInt raw_nodes)
        (* Future INST call, read/branch/write, exact empty-Hyp/tag/result
           checks, six empty Leaves/counter/Dependency/Edge events. *)
        val _ = pay
          (1+tag_work+3+3+result_events)
    in {shape=shape,oracles=oracles} end
  fun prepare_named_inst admission request=
    prepare_named_inst_using 6 admission request
  fun named_inst_matches (NamedInstVariable (name,ty)) actual =
        Term.is_var actual andalso
        let val (other,wanted)=Term.dest_var actual
        in name=other andalso Type.compare (ty,wanted)=EQUAL end
    | named_inst_matches (NamedInstConstant (held,ty)) actual =
        Term.is_const actual andalso Term.same_const held actual andalso
        Type.compare (ty,Term.type_of actual)=EQUAL
    | named_inst_matches (NamedInstApplication (a,b)) actual =
        Term.is_comb actual andalso
        let val (left,right)=Term.dest_comb actual
        in named_inst_matches a left andalso named_inst_matches b right end

  type 'node operations =
    {guard:unit -> unit,spend:IntInf.int -> unit,key:'node -> int,
     type_of:'node -> Type.hol_type,view:'node -> 'node view,
     name:'node -> Term.term,check_type:Type.hol_type -> unit,
     native_limits:unit -> SmtReplayNativeContract.limits}
  (* Successful compact syntax only: no theorem, dependency, Source or
     callback result is retained. Each block owns its own stamped table. *)
  datatype profile_cache = ProfileCache of
    {epoch:int,symbols:int,template:int,ceiling:int,
     rows:(Term.term * profile) list Array.array}
  type profile_store=profile_cache option ref
  fun empty_profile_store_using (pay:IntInf.int -> unit)=
    (pay 1;ref NONE:profile_store)
  datatype dependency = Dependency of int * dependency_body
  and dependency_body = Leaves of int list | Union of dependency list
  datatype 'node block = Block of
    {owner:unit ref,active:bool ref,operations:'node operations,
     names:(int,Term.term) Redblackmap.dict,
     definitions:(int,int) Redblackmap.dict,terms:Term.term vector,
     projections:Thm.thm vector,source_count:int,
     template_limit:int,variables:Term.term HOLset.set,
     next_dependency:int ref,profiles:profile_cache option ref}
  datatype edge = Edge of
    {owner:unit ref,theorem:Thm.thm,dependency:dependency}
  fun active (Block {active,operations,...}) =
    (if !active then () else raise ERR "active" "named block retired";
     #guard operations ())
  fun pay (block as Block {operations,...}) amount =
    (active block;#spend operations amount;active block)
  fun retire (Block {active,...}) = active := false
  fun block_map block action []=(active block;[])
    | block_map block action (value::rest)=
        (pay block 1;action value::block_map block action rest)
  fun block_append block [] tail=(active block;tail)
    | block_append block (value::rest) tail=
        (pay block 1;value::block_append block rest tail)
  fun name (block as Block {operations,names,...}) node =
    let val _ = pay block 1 val key = #key operations node
        val ty = #type_of operations node
        val result = case Redblackmap.peek (names,key) of SOME value => value
          | NONE => raise ERR "name" "node outside frozen block"
        val limit=IntInf.fromInt
          (#type_work_limit ((#native_limits operations) ()))
        val a=type_weight_using (pay block) (ERR "name") limit ty
        val b=type_weight_using (pay block) (ERR "name") limit
          (Term.type_of result)
        val _=pay block (1+a+b)
        val _ = if Type.compare (ty,Term.type_of result)=EQUAL then () else
          raise ERR "name" "named node type changed"
    in active block;result end
  fun theorem (block as Block {owner,...})
      (Edge {owner=held,theorem,...}) =
    (active block;if Portable.pointer_eq (owner,held) then theorem else
       raise ERR "theorem" "proof edge belongs to another block")
  fun clean proof =
    let val (oracles,_) = Tag.dest_tag (Thm.tag proof)
    in List.all (fn oracle => oracle="DISK_THM") oracles andalso
       null (Tag.axioms_of (Thm.tag proof)) end
  fun new_dependency (block as Block {next_dependency,...}) body =
    let val _=pay block 1 val id= !next_dependency
        val _=next_dependency:=id+1
    in Dependency (id,body) end
  fun dependencies block (edge as Edge {dependency,...}) =
    let val _=theorem block edge
        fun collect [] _ leaves=Redblackset.listItems leaves
          | collect (Dependency (id,body)::rest) visited leaves=
              (pay block 1;
               if Redblackset.member (visited,id) then
                 collect rest visited leaves
               else
                 let val visited=Redblackset.add (visited,id) in
                   case body of Leaves indices=>collect rest visited
                       (Redblackset.addList (leaves,indices))
                     | Union children=>collect
                         (block_append block children rest)
                         visited leaves end)
        fun compare_ids (a,b)=(pay block 1;Int.compare (a,b))
    in collect [dependency] (Redblackset.empty compare_ids)
      (Redblackset.empty compare_ids) end
  fun finish_edge (block as Block {owner,...}) dependencies proof =
    (active block;Edge {owner=owner,theorem=proof,
      dependency=new_dependency block (Union dependencies)})
  fun projection (block as Block {owner,projections,...}) index =
    (pay block 1;
     Edge {owner=owner,theorem=Vector.sub (projections,index),
       dependency=new_dependency block (Leaves [index])})
  fun source (block as Block {source_count,...}) index =
    (active block;if index>=0 andalso index<source_count then
       projection block index else raise ERR "source" "unknown occurrence")
  fun definition (block as Block {operations,definitions,...}) node =
    (ignore (name block node);
     case Redblackmap.peek (definitions,#key operations node) of
         SOME index => projection block index
       | NONE => raise ERR "definition" "node has no constructor equation")
  fun admission (block as Block {operations,variables,...}) =
    let val _=active block val native=(#native_limits operations) ()
        val _=active block
    in {pay=pay block,member=fn term=>
          (pay block 1;HOLset.member (variables,term)),
        guard=fn()=>active block,
        template_limit= #template_limit (#semantic_limits native),
        type_work_limit= #type_work_limit native,
        error=ERR "policy_primitive"}:admission end
  fun inspector_with_store (admitted:admission)
      (profiles:profile_store) = inspector_using admitted (fn spend =>
    let
      val _=spend 2
      val template= #template_limit admitted
      val ceiling= #type_work_limit admitted
      fun fail ()=raise ERR "profile" "native profile lifetime changed"
      fun fresh ()=
        let
          (* Array plus 127 initialized cells, five fields and record,
             two epoch reads, SOME and the block publication. *)
          val _=spend 138
          val saved=ProfileCache
            {epoch=Type.type_epoch (),symbols=Term.term_epoch (),
             template=template,ceiling=ceiling,rows=Array.array(127,[])}
          val _=profiles:=SOME saved
        in saved end
      fun matches (ProfileCache {epoch,symbols,template=cap,
            ceiling=limit,...})=
        (* Two epoch reads and four comparisons; no callback intervenes. *)
        (spend 6;epoch=Type.type_epoch () andalso
         symbols=Term.term_epoch () andalso cap=template andalso
         limit=ceiling)
      val _=spend 2
      val saved=case !profiles of NONE=>fresh ()
        | SOME old=>if matches old then old else fresh ()
      val _=spend 3
      val ProfileCache {epoch,symbols,rows,...}=saved
      (* Each pure metadata access is preceded by the SAME owning pay/
         active guards. Its seven stamp operations are paid together;
         there is no callback between the stamp and table access. *)
      fun gate amount=
        (spend (amount+7);
         if epoch=Type.type_epoch () andalso
             symbols=Term.term_epoch () then
           (case !profiles of SOME actual=>
              if Portable.pointer_eq(saved,actual) then () else fail ()
            | NONE=>fail ())
         else fail ())
      fun find_rows _ []=(gate 1;NONE)
        | find_rows term ((held,value)::rest)=
            (gate 2;if Portable.pointer_eq(term,held) then SOME value
             else find_rows term rest)
      fun find term=
        let val _=gate 0
            val index=SmtReplayImport.pointer_bucket_observed
              (#pay admitted) 2 127 term
            val _=gate 1
        in find_rows term (Array.sub(rows,index)) end
      fun publish term value=
        let val _=gate 0
            val index=SmtReplayImport.pointer_bucket_observed
              (#pay admitted) 2 127 term
            (* Actual bucket read, pair, cons and array write. *)
            val _=gate 4
        in Array.update(rows,index,(term,value)::Array.sub(rows,index)) end
      val _=spend 3
    in {find=find,publish=publish} end)
  fun block_inspector (Block {profiles,...}) admitted=
    inspector_with_store admitted profiles
  fun derive block recipe edges =
    let val admission=admission block
        val inspect=block_inspector block admission
        val proofs=List.map (fn edge=>
          (pay block 2;theorem block edge)) edges
        val prepared=prepare_fixed_using (fixed_admission admission)
          (#profile inspect)
          (name block) recipe proofs
        val proof=primitive (name block) recipe proofs
        val _=if matches (#shape prepared) (Thm.concl proof) andalso
            clean proof andalso List.all (fn term=>List.exists
              (fn held=>Portable.pointer_eq (term,held))
              (#hypotheses prepared)) (Thm.hyp proof) then () else
          raise ERR "policy_primitive" "fixed rule result/Hyp changed"
        val dependencies=block_map block
          (fn Edge {dependency,...}=>dependency)
          edges
    in finish_edge block dependencies proof end
  fun compact_profile block term =
    let val admission=admission block
        val _=pay block 0
        val result= #profile (block_inspector block admission) term
    in active block;result end
  fun native_type_weight block ty =
    let val admission=admission block
        val _=pay block 0 val result=type_weight admission ty
    in active block;result end
  fun derive_boolean block opcode edges =
    let val admission=admission block
        val inspect=block_inspector block admission
        val proofs=List.map (fn edge=>
          (pay block 2;theorem block edge)) edges
        val prepared=prepare_boolean_using (fixed_admission admission)
          (#profile inspect) (name block) opcode proofs
        val proof=boolean_using
          (fn()=>ERR "policy_boolean" "incorrect fixed rule arity")
          (name block) opcode proofs
        val _=if boolean_matches (#shape prepared) (Thm.concl proof) andalso
            clean proof andalso List.all (fn term=>List.exists
              (fn held=>Portable.pointer_eq (term,held))
              (#hypotheses prepared)) (Thm.hyp proof) then () else
          raise ERR "policy_boolean" "fixed proof changed"
        val dependencies=block_map block
          (fn Edge {dependency,...}=>dependency)
          edges
    in finish_edge block dependencies proof end
  fun execute_prepared_named_inst block substitution original
      (prepared:{shape:named_inst_shape,oracles:string list}) =
    let
        val _=active block
        val _=pay block 2
        val result=O.INST substitution original
        val result_tag=Thm.tag result
        val _=if null (Thm.hyp result) andalso
            null (Tag.axioms_of result_tag) andalso
            #1 (Tag.dest_tag result_tag)= #oracles prepared andalso
            named_inst_matches (#shape prepared) (Thm.concl result)
          then () else
          raise ERR "policy_closed_inst" "closed schema result changed"
    in result end
  (* SAME closed schema preflight, now usable before the first native
     assembly operation. Ordinary closed still chooses literal []. *)
  fun prepare_closed_named_inst_using block substitution original =
    let val admitted=admission block
        val _=pay block 0
    in prepare_named_inst
          {pay=pay block,type_weight=native_type_weight block,
           member= #member admitted,
           template_limit= #template_limit admitted,
           type_work_limit= #type_work_limit admitted,error=ERR}
          {substitution=substitution,theorem=original}end
  fun closed block original =
    let val prepared=prepare_closed_named_inst_using block [] original
        val result=execute_prepared_named_inst block [] original prepared
    in finish_edge block [] result end

  (* Only the explicit prepared route allocates this envelope. The input
     theorem is genuinely closed and has passed the original name/Type/
     input/output/tag/annotation/native portfolio. No caller quote amount,
     hypothesis, dependency or edge can enter this private plan. *)
  datatype 'node closed_inst_plan=ClosedInstPlan of
    {block:'node block,substitution:(Term.term,Term.term)Lib.subst,
     original:Thm.thm,prepared:{shape:named_inst_shape,oracles:string list},
     epoch:int,symbols:int,used:bool ref}
  fun prepare_closed_inst block {substitution,theorem}=
    let
      (* Entry declaration data precedes the first supplied callback. *)
      val epoch=Type.type_epoch()val symbols=Term.term_epoch()
      val _=active block
      (* Seven fields, envelope, ref, entry reads and final six-event
         declaration fence. No changed epoch can be blessed at mint. *)
      val _=pay block 17
      val prepared=prepare_closed_named_inst_using block substitution theorem
      val _=active block
      val _=if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols
        then ()else raise ERR "closed_inst" "declaration lifetime changed"
    in ClosedInstPlan{block=block,substitution=substitution,original=theorem,
      prepared=prepared,epoch=epoch,symbols=symbols,used=ref false}end
  fun execute_closed_inst
      (ClosedInstPlan{block,substitution,original,prepared,epoch,symbols,
        used})=
    let
      val _=active block
      (* Epoch reads/comparisons/control and actual once read/write. *)
      val _=pay block 9
      val _=if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols
        then ()else raise ERR "closed_inst" "declaration lifetime changed"
      val _=if !used then raise ERR "closed_inst" "used closed schema plan"
        else used:=true
      (* Final epoch reads/control are prepaid before the SAME sole INST.
         The native worker and exact original edge envelope stay shared. *)
      val _=pay block 6
      val result=execute_prepared_named_inst block substitution original
        prepared
      val _=active block
      val _=if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols
        then ()else raise ERR "closed_inst" "declaration lifetime changed"
    in finish_edge block [] result end
  (* One actual constructor-spine programme, with static context arguments.
     No per-call operations record, partial callback closure or body import
     is introduced by the old block specialization. *)
  fun constructor_using active observe definition derive context node =
    (active context;case observe node of
        Constant _ => definition context node
      | Application (operator,operand) =>
          derive context Transitivity
            [definition context node,
             derive context (ApplyNamedArgument operand)
               [constructor_using active observe definition derive
                 context operator]]
      | Atom => derive context (ReflexiveName node) [])
  fun constructor (block as Block {operations,...}) node =
    constructor_using active (#view operations) definition derive block node
  fun needed_sources (block as Block {terms,source_count,...}) edge =
    let val hypotheses=Thm.hyp (theorem block edge)
        val admitted=admission block
        fun same_variable left right =
          (pay block 1;if not (Term.is_var left) then false else
            let val (a,ty)=Term.dest_var left
                val (b,wanted)=Term.dest_var right
                val _=pay block (1+IntInf.fromInt (String.size a)+
                  IntInf.fromInt (String.size b))
                val x=type_weight admitted ty
                val y=type_weight admitted wanted
                val _=pay block (1+x+y)
            in a=b andalso Type.compare (ty,wanted)=EQUAL end)
        fun collect index result=
          if index=source_count then List.rev result else
            (pay block 1;
             if List.exists (fn term=>same_variable term
                 (Vector.sub (terms,index))) hypotheses then
               collect (index+1) (index::result)
             else collect (index+1) result)
    in collect 0 [] end

  (* Existing closures and concrete maps are direct parameters. The
     root path constructs no plan/context box or additional callback. *)
  fun finish_freeze operations (pay:IntInf.int -> unit) execute
      copy_rows copy_terms copy_proofs
      vector_terms vector_proofs names variables indices source_count
      template_limit _ planned =
    let
      (* Prepay and allocate the private empty cache before ASSUME. Its
         first actual inspector separately pays all 127 bucket cells. *)
      val _=pay 2
      val profiles=ref NONE
      val rows=copy_rows execute planned
      val terms=vector_terms (copy_terms #1 rows)
      val projections=vector_proofs (copy_proofs #2 rows)
      val result = Block {owner=ref (),active=ref true,operations=operations,
        names=names,definitions=indices,terms=terms,projections=projections,
        source_count=source_count,template_limit=template_limit,
        variables=variables,next_dependency=ref 0,profiles=profiles}
      val _ = active result
    in result end

  (* Static empty specializations preserve the old prefix exactly. These
     return the existing list and count without a new per-call context. *)
  fun ordinary_freeze_facts _ _ _ facts=facts
  fun ordinary_freeze_count _ count sources=count sources 0

  (* Formal source shapes are syntax, not original Source permission.
     Every Held leaf must be an actual compact owned name or a constant.
     A bounded occurrence pass precedes the shared exact shape quote. *)
  fun formal_freeze_facts formals (pay:IntInf.int -> unit) quote
      (admitted:admission)facts=
    let
      val _=pay 4
      fun validate shape=
        let val _=pay 2 val visits=ref 0
            fun walk current=
              let val _=pay 5
                  val _=if !visits< #template_limit admitted then ()else
                    raise ERR "formal_freeze" "formal syntax exceeds cap"
                  val _=visits:= !visits+1
              in case current of
                  HeldSyntax term=>
                    (pay 3;
                     if Term.is_const term then ()else
                     if Term.is_var term andalso #member admitted term
                       then ()else raise ERR "formal_freeze"
                         "formal leaf is not an actual compact name")
                | EqualitySyntax(a,b)=>(pay 2;walk a;walk b)
                | ApplicationSyntax(a,b)=>(pay 2;walk a;walk b)
              end
            val _=pay 1
        in walk shape end
      fun prepare []=(pay 1;[])
        | prepare(shape::rest)=
            let val _=pay 2 val _=validate shape val held=quote shape
            in held::prepare rest end
      fun append [] tail=(pay 1;tail)
        | append(value::rest)tail=(pay 2;value::append rest tail)
      val extra=prepare formals
    in append facts extra end
  fun formal_freeze_count formals (pay:IntInf.int -> unit) count sources=
    let val _=pay 1
        fun visit [] total=(pay 1;total)
          | visit(_::rest)total=(pay 2;visit rest(total+1))
    in visit formals(count sources 0)end
  fun freeze_using_sources facts_source count_source finish
      (operations:'node operations)
      {nodes,sources,template_limit} =
    let
      val _ = #guard operations ()
      val native = (#native_limits operations) ()
      val native_cap = #template_limit (#semantic_limits native)
      val ceiling = IntInf.fromInt (#type_work_limit native)
      val _ = if template_limit=native_cap andalso template_limit>0 then ()
        else raise ERR "freeze" "different native compact template bound"
      fun pay amount =
        (#guard operations ();#spend operations amount;#guard operations ())
      fun type_work ty = type_weight_using pay (ERR "freeze") ceiling ty
      fun same_type left right =
        let val a=type_work left val b=type_work right
            val _=pay (1+a+b)
        in Type.compare (left,right)=EQUAL end
      fun compare_int (a,b) = (pay 1;Int.compare (a,b))
      fun copy_map action []=(#guard operations ();[])
        | copy_map action (value::rest)=
            (pay 1;action value::copy_map action rest)
      fun append [] tail=(#guard operations ();tail)
        | append (value::rest) tail=(pay 1;value::append rest tail)
      fun reverse values=
        let fun loop [] result=(#guard operations ();result)
              | loop (value::rest) result=
                  (pay 1;loop rest (value::result))
        in loop values [] end
      fun count [] total=(#guard operations ();total)
        | count (_::rest) total=(pay 1;count rest (total+1))
      fun vector values=
        let val _=pay (IntInf.fromInt (count values 0))
        in Vector.fromList values end
      fun compare_names (left,right) =
        let val _=pay (1+IntInf.fromInt
              (String.size (#1 (Term.dest_var left)))+
              IntInf.fromInt (String.size (#1 (Term.dest_var right))))
            val a=type_work (Term.type_of left)
            val b=type_work (Term.type_of right)
            val _=pay (1+a+b)
        in Term.compare (left,right) end
      fun row (node,(names,variables)) =
        let val _ = pay 1
            val key = #key operations node
            val ty = #type_of operations node
            val _ = #check_type operations ty
            val term = #name operations node
            val _ = #guard operations ()
            val _ = if Term.is_var term andalso
                same_type ty (Term.type_of term) then () else
              raise ERR "freeze" "name is not a typed variable"
            val _ = if Redblackmap.inDomain (names,key) orelse
                HOLset.member (variables,term) then
              raise ERR "freeze" "duplicate node or compact name" else ()
        in (Redblackmap.insert (names,key,term),
            HOLset.add (variables,term)) end
      val (names,variables) = List.foldl row
        (Redblackmap.mkDict compare_int,HOLset.empty compare_names) nodes
      fun named node =
        (ignore (#type_of operations node);
         Redblackmap.find (names,#key operations node))
      val admission:admission =
        {pay=pay,member=fn term=>HOLset.member (variables,term),
         guard= #guard operations,template_limit=template_limit,
         type_work_limit= #type_work_limit native,error=ERR "freeze"}
      val inspect = inspector admission
      fun describe shape=describe_shape ignore_shape (#profile inspect)
        type_work same_type shape
      (* Forecast every actual constructor and ASSUME conclusion/Hyp before
         constructing syntax. No wide native conjunction is needed by this
         sparse block, so no native bound is imposed on such a conjunction. *)
      fun quote shape =
        let val _=pay 1 val (p,ty)=describe shape
            val _=if same_type ty Type.bool then () else
              raise ERR "freeze" "non-Boolean compact leaf"
            val _=if #raw p<=IntInf.fromInt template_limit andalso
                #inc p<=IntInf.fromInt template_limit then () else
              raise ERR "freeze" "compact leaf exceeds native template"
            (* Actual Term input, output conclusion and output Hyp each
               retain this syntax/annotation incidence. *)
            val portfolio=1+3*(#raw p+ #inc p+ #ann p)
            val _=if portfolio<=ceiling then () else
              raise ERR "freeze" "native ASSUME result/Hyp portfolio exceeded"
            val _=pay portfolio
        in shape end
      fun fact node = (pay 1;quote (HeldSyntax (named node)))
      val facts=facts_source pay quote admission(List.map fact sources)
      val source_count=count_source pay count sources
      fun definition (node,(shapes,indices,index)) =
        let val _=pay 1
            val rhs=case #view operations node of
                Atom=>NONE
              | Constant atom=>
                  if Term.is_const atom then SOME (HeldSyntax atom) else
                    raise ERR "freeze" "constant view is not atomic"
              | Application (function,argument)=>SOME (ApplicationSyntax
                  (HeldSyntax (named function),HeldSyntax (named argument)))
        in case rhs of NONE=>(shapes,indices,index)
          | SOME rhs=>
              let val shape=quote (EqualitySyntax (HeldSyntax (named
                node),rhs))
              in (shape::shapes,Redblackmap.insert
                (indices,#key operations node,index),index+1) end
        end
      val (definitions,indices,_) = List.foldl definition
        ([],Redblackmap.mkDict compare_int,source_count) nodes
      fun realize shape=realize_shape ignore_shape shape
      fun execute shape =
        (#guard operations ();
         let val term=realize shape val _= #guard operations ()
             val proof=O.ASSUME term val _= #guard operations ()
         in (term,proof) end)
      val planned=append facts (reverse definitions)
    in finish operations pay execute copy_map copy_map copy_map
      vector vector names variables indices source_count template_limit
      realize planned end

  fun freeze_using finish operations inputs=
    freeze_using_sources ordinary_freeze_facts ordinary_freeze_count
      finish operations inputs

  fun freeze operations inputs=freeze_using finish_freeze operations inputs

  (* These are formal named-programme fields, not original Sources.
     Every callback/function below already belongs to the actual prefix.
     No caller native quote or mutable credit can enter this constructor. *)
  datatype 'node freeze_plan=FreezePlan of
    {operations:'node operations,pay:IntInf.int -> unit,
     execute:shape -> Term.term * Thm.thm,
     copy_rows:(shape -> Term.term * Thm.thm) -> shape list ->
       (Term.term * Thm.thm) list,
     copy_terms:(Term.term * Thm.thm -> Term.term) ->
       (Term.term * Thm.thm) list -> Term.term list,
     copy_proofs:(Term.term * Thm.thm -> Thm.thm) ->
       (Term.term * Thm.thm) list -> Thm.thm list,
     vector_terms:Term.term list -> Term.term vector,
     vector_proofs:Thm.thm list -> Thm.thm vector,
     names:(int,Term.term) Redblackmap.dict,variables:Term.term HOLset.set,
     definitions:(int,int) Redblackmap.dict,source_count:int,
     template_limit:int,planned:shape list,epoch:int,symbols:int,
     realize:shape -> Term.term,
     materialized:((shape * Term.term) vector * Term.term list) option ref,
     used:bool ref}
  fun plan_freeze operations (pay:IntInf.int -> unit) execute
      copy_rows copy_terms copy_proofs vector_terms vector_proofs
      names variables indices source_count template_limit realize planned =
    let
      (* Nineteen fields, constructor/two refs and two epoch reads. These
         metadata events are separate from the original macro quotation. *)
      val _=pay 24
      val epoch=Type.type_epoch () val symbols=Term.term_epoch ()
    in FreezePlan{operations=operations,pay=pay,execute=execute,
      copy_rows=copy_rows,copy_terms=copy_terms,copy_proofs=copy_proofs,
      vector_terms=vector_terms,vector_proofs=vector_proofs,names=names,
      variables=variables,definitions=indices,source_count=source_count,
      template_limit=template_limit,planned=planned,epoch=epoch,
      symbols=symbols,realize=realize,materialized=ref NONE,
      used=ref false}end
  fun prepare_freeze operations inputs=
    freeze_using plan_freeze operations inputs

  (* Only this explicit new mode allocates the two captured hook values
     and reconstructs the ordinary input record. The root entry above
     uses static functions and performs none of this setup. *)
  fun prepare_freeze_with_formals operations
      {nodes,sources,formals,template_limit}=
    let val _= #guard operations ()
        val _= #spend operations 6
        val facts=formal_freeze_facts formals
        val count=formal_freeze_count formals
    in freeze_using_sources facts count plan_freeze operations
      {nodes=nodes,sources=sources,template_limit=template_limit}end
  fun freeze_with_formals operations
      {nodes,sources,formals,template_limit}=
    let val _= #guard operations ()
        val _= #spend operations 6
        val facts=formal_freeze_facts formals
        val count=formal_freeze_count formals
    in freeze_using_sources facts count finish_freeze operations
      {nodes=nodes,sources=sources,template_limit=template_limit}end
  fun freeze_layout(FreezePlan{operations,pay,planned,definitions,
      source_count,epoch,symbols,used,...})=
    let
      val _= #guard operations ()
      (* Three immutable data fields+record, two declaration reads/two
         comparisons/branch, and the once-state read/branch. *)
      val _=pay 11
      val _=if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
          then ()else raise ERR "freeze_layout" "declaration lifetime changed"
      val _=if !used then raise ERR "freeze_layout" "used freeze plan"else ()
      val result={shapes=planned,definitions=definitions,
        source_count=source_count}
      val _= #guard operations ()
    in result end
  fun materialize_freeze(FreezePlan{operations,pay,planned,realize,
      materialized,epoch,symbols,used,...})=
    let
      val _= #guard operations ()
      (* Epoch reads/comparisons/branch, used read/branch and cache access. *)
      val _=pay 9
      val _=if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
          then ()else raise ERR "materialize_freeze"
            "declaration lifetime changed"
      val _=if !used then raise ERR "materialize_freeze" "used freeze plan"
        else ()
    in case !materialized of SOME(_,terms)=>terms | NONE=>
      let
        (* Two captured visitors and final epoch work. The actual Term
           construction is the original already-quoted macro incidence,
           performed ONCE here rather than repeated before ASSUME. *)
        val _=pay 7
        fun reverse values=
          let val _=pay 1
              fun visit [] result=(#guard operations ();result)
                | visit(value::rest)result=
                    (pay 2;visit rest(value::result))
          in visit values [] end
        fun build [] rows terms count=
              let val rows=reverse rows val terms=reverse terms
                  val _=pay(1+IntInf.fromInt count)
                  val rows=Vector.fromList rows
                  (* Existing immutable rows/terms pair, SOME and write. *)
                  val _=pay 3
                  val saved=(rows,terms)
                  val _= #guard operations ()
                  val _=if Type.type_epoch ()=epoch andalso
                      Term.term_epoch ()=symbols then ()else
                    raise ERR "materialize_freeze"
                      "declaration lifetime changed"
                  val _=materialized:=SOME saved
              in terms end
          | build(shape::rest)rows terms count=
              let val _= #guard operations ()
                  (* Actual list visit, row pair, two cons and count step. *)
                  val _=pay 5
                  val term=realize shape
                  val _= #guard operations ()
              in build rest((shape,term)::rows)(term::terms)(count+1)end
      in build planned [] [] 0 end
    end
  fun execute_freeze(FreezePlan{operations,pay,execute,copy_rows,copy_terms,
      copy_proofs,vector_terms,vector_proofs,names,variables,definitions,
      source_count,template_limit,planned,epoch,symbols,realize,
      materialized,used})=
    let
      val _= #guard operations ()
      val _=pay 8
      val _=if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
          then ()else raise ERR "execute_freeze" "declaration lifetime changed"
      val _=if !used then raise ERR "execute_freeze" "used freeze plan"else
        (pay 1;used:=true)
      (* The known final epoch/branch work is prepaid before ASSUME. *)
      val _=pay 6
      (* Only the opt-in materialized route allocates this reader. The
         original route retains its actual execute closure unchanged. *)
      val _=pay 2
      val prepared_execute=case !materialized of NONE=>execute
        | SOME(rows,_)=>
          let val _=pay 1 val count=Vector.length rows
              (* Two setup objects, two amount operations and ten actual
                 scalar reader events per row, before the first ASSUME. *)
              val _=pay(4+10*IntInf.fromInt count)
              val cursor=ref 0
              fun cached shape=
                (#guard operations ();
                 let val index= !cursor
                     val (actual,term)=Vector.sub(rows,index)
                     val _=if Portable.pointer_eq(actual,shape)then ()else
                       raise ERR "execute_freeze" "different private row"
                     val _=cursor:=index+1
                     val proof=O.ASSUME term
                     val _= #guard operations ()
                 in (term,proof)end)
          in cached end
      val result=finish_freeze operations pay prepared_execute
        copy_rows copy_terms copy_proofs vector_terms vector_proofs names
        variables definitions source_count template_limit realize planned
      val _= #guard operations ()
      val _=if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
          then ()else raise ERR "execute_freeze" "declaration lifetime changed"
    in result end

  (* The opaque plan retains the actual named Block and its genuine input
     edges. No caller theorem or native result can be published as an edge. *)
  datatype 'node unit_resolution_plan = UnitResolutionPlan of
    {block:'node block,plan:dependency SmtReplayNamedClause.plan,used:bool ref}
  fun prepare_unit_resolution_using aliases
      (block as Block {operations,terms,...})
      {premises,target,target_expanded,fallbacks,tree_view,
       metadata_template} =
    let
      val _=active block
      val admitted=admission block
      val inspect=block_inspector block admitted
      val native=(#native_limits operations) ()
      fun hypothesis held=
        let val _=active block
            fun scan index=
              (pay block 1;if index=Vector.length terms then false else
               (pay block 2;
                Portable.pointer_eq(held,Vector.sub(terms,index))orelse
                scan(index+1)))
        in scan 0 end
      fun named node=name block node
      fun constant wanted node=
        (pay block 1;case (#view operations) node of Constant term=>
           Term.same_const term wanted | _=>false)
      fun constant_term node=case (#view operations) node of
          Constant term=>term
        | _=>raise ERR "unit_resolution" "constant origin changed"
      fun count [] total=(active block;total)
        | count(_::rest)total=(pay block 1;count rest(total+1))
      fun operator wanted arity node=
        let fun walk current arguments=
              (ignore(named current);case (#view operations) current of
                  Application(a,b)=>walk a(b::arguments)
                | Constant term=>
                    if Term.same_const term wanted andalso
                        count arguments 0=arity then arguments else
                      raise ERR "unit_resolution" "actual operator changed"
                | _=>raise ERR "unit_resolution"
                    "missing actual constructor spine")
        in walk node [] end
      fun node_view node=case (#view operations) node of
          Constant _=>SmtReplayNamedClause.NodeConstant
        | Application pair=>SmtReplayNamedClause.NodeApplication pair
        | Atom=>SmtReplayNamedClause.NodeAtom
      fun dependency edge=
        let val _=theorem block edge
            val Edge {dependency,...}=edge
        in dependency end
      val shared=
        {guard=fn()=>active block,tick=fn()=>pay block 1,
         pay=pay block,future=pay block,profile= #profile inspect,
         type_weight=type_weight admitted,
         template=IntInf.fromInt(#template_limit(#semantic_limits native)),
         metadata_template=metadata_template,
         ceiling=IntInf.fromInt(#type_work_limit native),hypothesis=hypothesis,
         error=ERR "unit_resolution",tree_view=tree_view,node_view=node_view,
         same_node=fn(a,b)=>(#key operations) a=(#key operations) b,
         named=named,constant=constant,constant_term=constant_term,
         operator=operator,theorem=theorem block,definition=definition block,
         dependency=dependency}
      val plan=case aliases of []=>SmtReplayNamedClause.prepare shared
        {premises=premises,target=target,target_expanded=target_expanded,
         fallbacks=fallbacks}
       | _=>SmtReplayNamedClause.prepare_with_atom_aliases aliases shared
        {premises=premises,target=target,target_expanded=target_expanded,
         fallbacks=fallbacks}
      val _=pay block 2
    in UnitResolutionPlan {block=block,plan=plan,used=ref false} end
  fun prepare_unit_resolution block options=
    prepare_unit_resolution_using [] block options
  fun prepare_unit_resolution_with_atom_aliases aliases block options=
    prepare_unit_resolution_using aliases block options
  fun execute_unit_resolution
      (UnitResolutionPlan {block,plan,used}) =
    let val _=active block
        val _=pay block 1
        val _=if !used then raise ERR "unit_resolution" "used plan" else
          used:=true
        val Block {operations,...}=block
        val result=SmtReplayNamedClause.execute
          {guard=fn()=>active block,check_type= #check_type operations,
           error=ERR "unit_resolution"} plan
    in finish_edge block (#dependencies result) (#theorem result) end

  fun atom_model_operations
      (block as Block{operations,terms,...}) metadata_template =
    let
      (* New-only admission setup: six fields, record and four actual
         callbacks/partial applications in the existing admission helper. *)
      val _=pay block 11
      val admitted=admission block
      val inspect=block_inspector block admitted
      val _=pay block 1
      val native=(#native_limits operations)()
      (* Four local functions, three guard/key callbacks and seven partial
         applications in the actual new operations record below. *)
      val _=pay block 14
      fun hypothesis held=
        let
          (* This scan closure is fresh at every actual Hyp observation. *)
          val _=pay block 1
          fun scan index=
            (pay block 1;if index=Vector.length terms then false else
             (pay block 2;
              Portable.pointer_eq(held,Vector.sub(terms,index))orelse
              scan(index+1)))
        in scan 0 end
      fun constant_term node=case (#view operations)node of
          Constant term=>term
        | _=>raise ERR "atom_congruence" "constant origin changed"
      fun node_view node=case (#view operations)node of
          Constant _=>SmtReplayNamedClause.NodeConstant
        | Application pair=>SmtReplayNamedClause.NodeApplication pair
        | Atom=>SmtReplayNamedClause.NodeAtom
      fun dependency edge=
        let val _=theorem block edge
            val Edge{dependency,...}=edge
        in dependency end
      (* Eighteen fields and the operations record. Two native-limit
         projections/conversions and the profile projection are separate. *)
      val _=pay block 25
      val shared=
        {guard=fn()=>active block,tick=fn()=>pay block 1,
         pay=pay block,future=pay block,profile= #profile inspect,
         type_weight=type_weight admitted,
         template=IntInf.fromInt(#template_limit(#semantic_limits native)),
         metadata_template=metadata_template,
         ceiling=IntInf.fromInt(#type_work_limit native),hypothesis=hypothesis,
         error=ERR "atom_congruence",node_view=node_view,
         same_node=fn(a,b)=>(#key operations)a=(#key operations)b,
         named=name block,constant_term=constant_term,
         theorem=theorem block,definition=definition block,
         dependency=dependency}
    in shared end

  (* Only genuine nodes of this actual named Block enter the shared model.
     The plan has no public theorem, name, edge or dependency intake. *)
  datatype 'node atom_congruence_plan = AtomCongruencePlan of
    {block:'node block,owner:unit ref,dependency:dependency,
     plan:dependency SmtReplayNamedClause.congruence_plan,used:bool ref}
  fun prepare_atom_congruence
      (block as Block{owner,...})
      {left,right,metadata_template} =
    let
      val _=active block
      val shared=atom_model_operations block metadata_template
      (* Actual pair and alias-list cells. Unused static selectors are
         module fields, not per-call allocations or performed work. *)
      val _=pay block 2
      val plan=SmtReplayNamedClause.prepare_atom_congruence shared(left,right)
      val _=active block
      (* Union constructor and its private counter/Dependency events.
         All dependency metadata is fixed before executing the native plan. *)
      val _=pay block 3
      val dependency=new_dependency block(Union
        (SmtReplayNamedClause.atom_congruence_dependencies plan))
      (* Five plan fields, record/constructor and the once ref. *)
      val _=pay block 8
    in AtomCongruencePlan{block=block,owner=owner,dependency=dependency,
      plan=plan,used=ref false}end

  fun execute_atom_congruence
      (AtomCongruencePlan{block,owner,dependency,plan,used}) =
    let
      val _=active block
      (* Once read/write, three execute fields/record, guard closure,
         callback projection and error partial application, four final
         Edge fields/record, twelve actual fixed endpoint events (four
         dest_comb, two same_const, four destructor tuples, two pointer
         comparisons), plus the result theorem projection. No new
         metadata spend follows the native call. *)
      val _=pay block 26
      val _=if !used then raise ERR "atom_congruence" "used plan"else
        used:=true
      val Block{operations,...}=block
      val result=SmtReplayNamedClause.execute_atom_congruence
        {guard=fn()=>active block,check_type= #check_type operations,
         error=ERR "atom_congruence"}plan
      val _=active block
    in Edge{owner=owner,theorem= #theorem result,dependency=dependency}end

  datatype 'node owned_constructor_plan=OwnedConstructorPlan of
    {block:'node block,owner:unit ref,dependency:dependency,
     plan:dependency SmtReplayNamedClause.constructor_plan,used:bool ref}
  fun prepare_owned_constructor (block as Block{owner,...})
      {node,metadata_template} =
    let
      val _=active block
      val shared=atom_model_operations block metadata_template
      val prepared=SmtReplayNamedClause.prepare_constructor shared node
      val _=active block
      val _=pay block 3
      val dependency=new_dependency block(Union
        (SmtReplayNamedClause.constructor_dependencies prepared))
      val _=pay block 8
    in OwnedConstructorPlan{block=block,owner=owner,dependency=dependency,
      plan=prepared,used=ref false}end
  fun owned_constructor_model
      (OwnedConstructorPlan{block,plan,...}) =
    (active block;pay block 2;
     SmtReplayNamedClause.constructor_model plan)
  fun execute_owned_constructor
      (OwnedConstructorPlan{block,owner,dependency,plan,used}) =
    let
      val _=active block
      val _=pay block 26
      val _=if !used then raise ERR "constructor" "used plan"else used:=true
      val Block{operations,...}=block
      val result=SmtReplayNamedClause.execute_constructor
        {guard=fn()=>active block,check_type= #check_type operations,
         error=ERR "constructor"}plan
      val _=active block
    in Edge{owner=owner,theorem= #theorem result,dependency=dependency}end

  (* The theorem is derived once during the ordinary HolSmt theory build.
     Active replay consumes the stored binder-free fifteen-node theorem,
     never an unmetered SPEC_ALL/load-time derived value. *)
  datatype 'node pointwise_xor_plan=PointwiseXorPlan of
    {block:'node block,proof:Thm.thm,
     substitution:(Term.term,Term.term)Lib.subst,
     prepared:{shape:named_inst_shape,oracles:string list},
     predicted:Term.term,epoch:int,symbols:int,
     used:bool ref}
  fun prepare_pointwise_xor
      (block as Block{operations,...}){left,right,metadata_template}=
    let
      val _=active block
      (* Admission11, local helpers4, native limit observations10 and
         the two declaration epoch reads. *)
      val _=pay block 27
      val admitted=admission block
      val native=(#native_limits operations)()
      val limits= #semantic_limits native
      val ceiling=IntInf.fromInt(#type_work_limit native)
      val bound=Int.min(#input_limit limits,
        Int.min(#output_limit limits,#template_limit limits))
      val types=Type.type_epoch()val symbols=Term.term_epoch()
      fun fail text=raise ERR "fixed_xor" text
      fun guard()=
        (active block;pay block 6;
         if types=Type.type_epoch()andalso symbols=Term.term_epoch()then()
         else fail "fixed pointwise XOR epochs changed")
      fun tick()=(guard();pay block 1)
      val original=HolSmtTheory.xor_pointwise
      val statement=Thm.concl original
      val _=pay block 3
      val token=case SmtReplayImport.bounded_raw_size_with_bound_observed
          {limit=bound,observe=tick}statement of SOME token=>token
        | NONE=>fail "fixed XOR instance exceeds native input bound"
      (* Actual pointer/control3, declaration reads/comparisons/control6,
         and the returned two-field record3, before the passive getter. *)
      val _=pay block 12
      val measured=SmtReplayImport.raw_bound_data token statement
      val _=pay block 8
      val _=if #raw_upper measured=15 andalso #inc_upper measured=15
          andalso SmtReplayResourcePolicy.allows metadata_template 15
        then()else fail "fixed XOR pointwise schema or template differs"
      (* The trusted source is binder-free before the following ordinary
         destructors. Real operands below are privately owned named vars. *)
      val _=pay block 21
      val(left_schema,right_schema)=boolSyntax.dest_eq statement
      val(partial,y)=Term.dest_comb left_schema
      val(operator,x)=Term.dest_comb partial
      val equality=boolSyntax.dest_neg right_schema
      val(a,b)=boolSyntax.dest_eq equality
      val _=if Term.is_const operator andalso
          Term.same_const operator
            (Term.prim_mk_const{Thy="HolSmt",Name="xor"})andalso
          Term.is_var x andalso Term.is_var y then()else
        fail "fixed XOR pointwise source geometry differs"
      fun bytes term=
        (tick();if Term.is_var term then
          let val _=pay block 2 val(name,_)=Term.dest_var term
              val amount=IntInf.fromInt(String.size name)
          in pay block amount;amount end
        else if Term.is_const term then
          let val _=pay block 3 val{Thy,Name,...}=Term.dest_thy_const term
              val amount=IntInf.fromInt(String.size Thy+String.size Name)
          in pay block amount;amount end
        else if Term.is_comb term then
          let val _=pay block 2 val(f,z)=Term.dest_comb term
          in bytes f+bytes z end
        else fail "binder in stored pointwise XOR")
      val names=bytes x+bytes y+bytes a+bytes b
      val _=pay block(2+names)
      val _=if Term.var_compare(x,a)=EQUAL andalso
          Term.var_compare(y,b)=EQUAL then()else
        fail "fixed XOR pointwise variable geometry differs"
      (* Exactly two variable-to-owned-variable substitutions. This is
         the SAME original named-inst forecast/matcher; the private zero
         result-event instance returns a theorem, not an unused N edge. *)
      (* Two substitution records6 and cons2, admission record7,
         two partial applications2, and the request record3. *)
      val _=pay block 20
      val substitution=[{redex=x,residue=left},{redex=y,residue=right}]
      val prepared=prepare_named_inst_using 0
        {pay=pay block,type_weight=native_type_weight block,
         member= #member admitted,template_limit=bound,
         type_work_limit= #type_work_limit native,error=ERR}
        {substitution=substitution,theorem=original}
      val spelling=bytes statement+bytes left+bytes right
      val _=pay block(1+30*(1+spelling))
      val predicted=Term.subst substitution statement
      val _=guard()
      (* Price this additional proof-free prediction match independently
         of the SAME helper's retained future native-result comparison. *)
      val _=pay block(1+60*(1+spelling))
      val _=if named_inst_matches(#shape prepared)predicted then()else
        fail "fixed XOR prediction differs"
      val _=pay block 4
      val callback_types=ref([]:Type.hol_type list)
      fun annotations term=
        let val _=tick()val ty=Term.type_of term
            val _=pay block 3
            val _=callback_types:=ty:: !callback_types
        in if Term.is_comb term then
            let val _=pay block 2 val(f,z)=Term.dest_comb term
            in annotations f;annotations z end
          else if Term.is_var term orelse Term.is_const term then()else
            fail "binder in fixed XOR callback portfolio"end
      val _=annotations statement val _=annotations predicted
      val _=annotations left val _=annotations right
      val _=pay block 8
      val _=SmtReplayLocalSpecialize.callback_forest
        {visit=tick,type_weight=native_type_weight block,
         ceiling=ceiling,error=ERR "fixed_xor"}(!callback_types)
      fun check []=guard()
        | check(ty::rest)=
            (tick();guard();(#check_type operations)ty;guard();check rest)
      val _=check(!callback_types)
      (* Eight fields plus the record, constructor and once ref. Shared
         named-inst already quotes INST, its once branch, actual empty
         Hyp/tag and the full shape checks. *)
      val _=pay block 11
    in PointwiseXorPlan{block=block,proof=original,
      substitution=substitution,prepared=prepared,predicted=predicted,
      epoch=types,symbols=symbols,used=ref false}end
  fun pointwise_xor_guard block epoch symbols=
    (active block;pay block 6;
     if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols then()
     else raise ERR "fixed_xor" "pointwise declaration lifetime changed")
  fun pointwise_xor_conclusion
      (PointwiseXorPlan{block,predicted,epoch,symbols,...})=
    (pointwise_xor_guard block epoch symbols;predicted)
  fun pointwise_xor_oracles
      (PointwiseXorPlan{block,prepared,epoch,symbols,...})=
    (pointwise_xor_guard block epoch symbols;#oracles prepared)
  fun execute_pointwise_xor(PointwiseXorPlan
      {block,proof,substitution,prepared,epoch,symbols,used,...})=
    let
      val _=pointwise_xor_guard block epoch symbols
      val _=if !used then raise ERR "fixed_xor" "used instance plan"else
        used:=true
      (* The original named-inst forecast pays the actual once read,
         branch and write. This additional quote covers only the final
         declaration fence, before the sole shared kernel operation. *)
      val _=pay block 6
      val result=execute_prepared_named_inst block substitution proof prepared
      val _=active block
      val _=if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols then()
        else raise ERR "fixed_xor" "pointwise declaration lifetime changed"
    in result end

  (* Four small, normally derived schemas replace a raw defining equation
     at the already-CNF SAT boundary. A single genuine constructor bridge
     is shared; no syntax comparison creates a proof or Source receipt. *)
  datatype xor_clause = XorPositiveOne | XorPositiveTwo
    | XorNegativeOne | XorNegativeTwo
  type xor_model={conclusion:Term.term,hypotheses:Term.term list}
  datatype xor_instruction = XorClosed of
      {original:Thm.thm,substitution:(Term.term,Term.term)Lib.subst,
       prepared:{shape:named_inst_shape,oracles:string list}}
    | XorPrimitive of
      {opcode:Term.term primitive,inputs:int list,shape:shape,
       hypotheses:Term.term list,oracles:string list}
  datatype 'node fixed_xor_plan=FixedXorPlan of
    {block:'node block,owner:unit ref,
     constructor:'node owned_constructor_plan,
     instructions:xor_instruction vector,output:int,
     dependency:dependency,epoch:int,symbols:int,used:bool ref}
  fun xor_conclusion({conclusion,...}:xor_model)=conclusion
  fun xor_hypotheses({hypotheses,...}:xor_model)=hypotheses
  fun xor_identity value=value
  fun xor_shape_term block(HeldSyntax term)=(pay block 1;term)
    | xor_shape_term block(ApplicationSyntax(left,right))=
        let val a=xor_shape_term block left
            val b=xor_shape_term block right
        in pay block 4;Term.mk_comb(a,b)end
    | xor_shape_term block(EqualitySyntax(left,right))=
        let val a=xor_shape_term block left
            val b=xor_shape_term block right
        in pay block 4;boolSyntax.mk_eq(a,b)end
  fun xor_spelling block term=
    (pay block 1;if Term.is_var term then
       let val _=pay block 2 val(name,_)=Term.dest_var term
           val amount=IntInf.fromInt(String.size name)
       in pay block amount;amount end
     else if Term.is_const term then
       let val _=pay block 3 val{Thy,Name,...}=Term.dest_thy_const term
           val amount=IntInf.fromInt(String.size Thy+String.size Name)
       in pay block amount;amount end
     else if Term.is_comb term then
       let val _=pay block 2 val(f,x)=Term.dest_comb term
       in xor_spelling block f+xor_spelling block x end
     else raise ERR "fixed_xor" "binder in admitted XOR clause")
  fun xor_weight block(p:profile)=
    (pay block 5;#raw p+ #inc p+ #ann p)
  fun xor_matching block profile(HeldSyntax term)=
        let val _=pay block 1 val p=profile term
            val text=xor_spelling block term
        in if Thm.kernelid="stdknl"then
          1+2*(xor_weight block p+text)else 1 end
    | xor_matching block profile(ApplicationSyntax(a,b))=
        (pay block 1;4+xor_matching block profile a+
          xor_matching block profile b)
    | xor_matching block profile(EqualitySyntax(a,b))=
        (pay block 1;8+xor_matching block profile a+
          xor_matching block profile b)
  fun xor_length block []=(pay block 1;0:IntInf.int)
    | xor_length block(_::rest)=(pay block 1;1+xor_length block rest)
  fun xor_tag_work block [] total=(pay block 1;total)
    | xor_tag_work block(name::rest)total=
        let val size=IntInf.fromInt(String.size name)
            val _=pay block(1+size)
        in xor_tag_work block rest(total+10+2*size)end
  fun xor_clause_schema kind=case kind of
      XorPositiveOne=>HolSmtTheory.xor_cnf_pos1
    | XorPositiveTwo=>HolSmtTheory.xor_cnf_pos2
    | XorNegativeOne=>HolSmtTheory.xor_cnf_neg1
    | XorNegativeTwo=>HolSmtTheory.xor_cnf_neg2
  fun xor_clause_negative kind=case kind of
      XorPositiveOne=>true | XorPositiveTwo=>true | _=>false
  fun xor_clause_raw kind=case kind of XorPositiveTwo=>19 | _=>15

  fun prepare_fixed_xor
      (block as Block{operations,owner,...})
      {node,left,right,clause,metadata_template} =
    let
      val epoch=Type.type_epoch()val symbols=Term.term_epoch()
      val _=active block
      (* Admission11, nineteen local helpers, native limit observations7
         and the two entry epoch reads. Inspector setup is separate. *)
      val _=pay block 39
      val admitted=admission block
      val _=pay block 11
      val inspect=block_inspector block admitted
      val native=(#native_limits operations)()
      val limits= #semantic_limits native
      val bound=Int.min(#input_limit limits,
        Int.min(#output_limit limits,#template_limit limits))
      fun guard()=
        (active block;pay block 6;
         if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols then()
         else raise ERR "fixed_xor" "clause declaration lifetime changed")
      (* Execution rechecks the same actual lifetime; its six metadata
         events are prepaid by emit, not charged after earlier effects. *)
      fun execute_guard()=
        (active block;
         if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols then()
         else raise ERR "fixed_xor" "clause declaration lifetime changed")
      fun tick()=(guard();pay block 1)
      fun fail text=raise ERR "fixed_xor" text
      fun same_node(a,b)=
        (pay block 3;(#key operations)a=(#key operations)b)
      fun application value=
        (pay block 1;case (#view operations)value of
            Application pair=>pair
          | _=>fail "actual XOR is not a binary application")
      val(partial,actual_right)=application node
      val(head,actual_left)=application partial
      val _=if same_node(left,actual_left)andalso
          same_node(right,actual_right)then ()else
        fail "actual XOR operand cursors differ"
      val _=pay block 7
      val _=case (#view operations)head of Constant actual=>
          if Term.same_const actual
              (Term.prim_mk_const{Thy="HolSmt",Name="xor"})then()else
            fail "actual XOR head differs from the fixed operator"
        | _=>fail "actual XOR head is not constant"
      val left_name=name block left val right_name=name block right
      val _=pay block 3
      val constructor=prepare_owned_constructor block
        {node=node,metadata_template=metadata_template}
      val model=owned_constructor_model constructor
      (* Three model/instruction/counter refs, original-source ref and
         the one initial model-list cons. *)
      val _=pay block 5
      val originals=ref([]:Term.term list)
      val models=ref[model:xor_model]
      val instructions=ref([]:xor_instruction list)
      val next=ref 1
      fun index 0(value::_)=(pay block 1;value)
        | index n(_::rest)=(pay block 2;index(n-1)rest)
        | index _ []=fail "private XOR model index"
      fun model_for slot=
        (pay block 4;index(!next-1-slot)(!models))
      fun model_inputs []=(guard();pay block 1;[])
        | model_inputs(slot::rest)=
            (pay block 2;model_for slot::model_inputs rest)
      fun publish model instruction=
        let val _=guard()val _=pay block 9 val slot= !next
            val _=next:=slot+1
            val _=models:=model:: !models
            val _=instructions:=instruction:: !instructions
        in slot end
      fun emit oracles opcode inputs=
        let val count=xor_length block inputs
            val actual=model_inputs inputs
            val _=pay block 7
            val prepared=prepare_fixed_observed xor_conclusion
              xor_hypotheses(fixed_admission admitted)(#profile inspect)
              xor_identity opcode actual
            (* The SAME admitted output shape is materialized only as
               compact native-name metadata, before any kernel effect. *)
            val conclusion=xor_shape_term block(#shape prepared)
            val hypotheses= #hypotheses prepared
            val h=xor_length block hypotheses
            val matching=xor_matching block(#profile inspect)
              (#shape prepared)
            val tags=xor_tag_work block oracles 7
            (* Shared primitive already quotes its native portfolio.
               These are the additional exact shape/Hyp/tag and private
               instruction-input/result bookkeeping observations. *)
            val _=pay block 8
            val _=pay block(17+4*count+matching+h*(h+2)+tags)
            val _=case opcode of SubstituteLiteral _=>pay block 6|_=>()
            (* Four prepared projections, inspector selector, model3
               and instruction7. *)
            val _=pay block 15
            val model={conclusion=conclusion,
              hypotheses=hypotheses}:xor_model
            val instruction=XorPrimitive{opcode=opcode,inputs=inputs,
              shape= #shape prepared,hypotheses=hypotheses,oracles=oracles}
        in publish model instruction end
      val _=pay block 1
      val reversed=emit [] Symmetry[0]
      fun prepare_clause kind=
        let
          val _=guard()val _=pay block 4
          val original=xor_clause_schema kind
          val statement=Thm.concl original
          val _=pay block 3
          val _=originals:=statement:: !originals
          val expected=IntInf.fromInt(xor_clause_raw kind)
          val _=pay block 3
          val token=case SmtReplayImport.bounded_raw_size_with_bound_observed
              {limit=bound,observe=tick}statement of SOME token=>token
            | NONE=>fail "fixed XOR clause exceeds native input bound"
          val _=pay block 12
          val measured=SmtReplayImport.raw_bound_data token statement
          val _=pay block 8
          val _=if #raw_upper measured=expected andalso
              #inc_upper measured=expected andalso
              SmtReplayResourcePolicy.allows metadata_template expected
              then()else
            fail "fixed XOR clause schema or template differs"
          (* This source is measured before ordinary Boolean destructors. *)
          (* disj5, selected polarity/branch2, two comb destructors4,
             head/variable tests and constructor12; neg destructor2 only
             for a positive clause. *)
          val _=pay block 23
          val(first,tail)=boolSyntax.dest_disj statement
          val actual=if xor_clause_negative kind then
              (pay block 2;boolSyntax.dest_neg first)else first
          val(partial,y)=Term.dest_comb actual
          val(operator,x)=Term.dest_comb partial
          val _=if Term.is_const operator andalso
              Term.same_const operator
                (Term.prim_mk_const{Thy="HolSmt",Name="xor"})andalso
              Term.is_var x andalso Term.is_var y then()else
            fail "stored XOR clause operand geometry differs"
          (* Two binding records/cells8, admission7, request3, two
             partials2 and actual admission/native field selectors2. *)
          val _=pay block 22
          val substitution=[{redex=x,residue=left_name},
            {redex=y,residue=right_name}]
          val prepared=prepare_named_inst_using 0
            {pay=pay block,type_weight=native_type_weight block,
             member= #member admitted,template_limit=bound,
             type_work_limit= #type_work_limit native,error=ERR}
            {substitution=substitution,theorem=original}
          val _=pay block 2
          val spelling=xor_spelling block statement+
            xor_spelling block left_name+xor_spelling block right_name
          (* Additional DATA prediction only: two-entry substitution
             setup18, one source-node pass/rebuilt Comb, at most nine
             two-entry dictionary comparisons (one insert + four probes).
             The shared INST worker retains its complete native quote. *)
          val _=pay block 10
          val combs=(expected-1)div 2
          val own= #ty((#profile inspect)left_name)
          val comparison=1+spelling+own
          val _=pay block(18+expected+combs+9*comparison)
          val predicted=Term.subst substitution statement
          val _=pay block 8
          val predicted_profile=(#profile inspect)predicted
          val _=pay block(6* #raw predicted_profile+
            2* #ann predicted_profile+2*spelling)
          val _=if named_inst_matches(#shape prepared)predicted then()else
            fail "fixed XOR clause prediction differs"
          (* Closed action/model constructors8, and its interpreter's
             vector/branch/write/loop bookkeeping8. *)
          val _=pay block 16
          val closed=publish
            {conclusion=predicted,hypotheses=[]}
            (XorClosed{original=original,substitution=substitution,
              prepared=prepared})
          (* The owned name is a genuine Boolean variable and must occur
             once in this compact literal template. SUBST consumes the
             small constructor equality directly, never a full-clause EQ. *)
          val _=pay block 6
          val named=name block node
          val(_,tail)=boolSyntax.dest_disj predicted
          val _=pay block 2
          val literal=if xor_clause_negative kind then
              (pay block 2;boolSyntax.mk_neg named)else named
          val _=pay block 3
          val template=boolSyntax.mk_disj(literal,tail)
          (* Five witness fields/record/constructor7 and actual native
             limit projections2; the oracle selector is separate. *)
          val _=pay block 9
          val witness=LiteralSubstitution{variable=named,template=template,
            input_limit= #input_limit limits,
            output_limit= #output_limit limits,guard=execute_guard}
          val _=pay block 1
            (* Two argument cons cells and its primitive constructor. *)
            val _=pay block 3
        in emit(#oracles prepared)(SubstituteLiteral witness)
          [reversed,closed]end
      val output=prepare_clause clause
      (* The actual callback accumulator ref; no unrequested law or list. *)
      val _=pay block 1
      val callback_types=ref([]:Type.hol_type list)
      fun annotations term=
        let val _=guard()val _=pay block 6
            val ty=Term.type_of term
            val _=callback_types:=ty:: !callback_types
        in if Term.is_comb term then
            let val _=pay block 2 val(f,x)=Term.dest_comb term
            in annotations f;annotations x end
          else(pay block 2;if Term.is_var term then()else
            (pay block 2;if Term.is_const term then()else
              fail "binder in compact XOR transport model"))end
      fun collect []=(guard();pay block 1)
        | collect((model:xor_model)::rest)=
            (pay block 2;annotations(#conclusion model);
             collect_hypotheses(#hypotheses model);collect rest)
      and collect_hypotheses []=(guard();pay block 1)
        | collect_hypotheses(term::rest)=
            (pay block 1;annotations term;collect_hypotheses rest)
      fun collect_originals []=(guard();pay block 1)
        | collect_originals(term::rest)=
            (pay block 1;annotations term;collect_originals rest)
      val _=collect_originals(!originals)
      val _=collect(!models)
      fun collect_templates []=(guard();pay block 1)
        | collect_templates(XorPrimitive{opcode,inputs,...}::rest)=
            (pay block 1;collect(model_inputs inputs);
             (case opcode of SubstituteLiteral(LiteralSubstitution
                {variable,template,...})=>
                  (pay block 2;annotations variable;annotations template)
              | _=>());collect_templates rest)
        | collect_templates(_::rest)=
            (pay block 1;collect_templates rest)
      val _=collect_templates(!instructions)
      val _=pay block 10
      val _=SmtReplayLocalSpecialize.callback_forest
        {visit=tick,type_weight=native_type_weight block,
         ceiling=IntInf.fromInt(#type_work_limit native),
         error=ERR "fixed_xor"}(!callback_types)
      fun check []=(guard();pay block 1)
        | check(ty::rest)=
            (pay block 2;guard();(#check_type operations)ty;guard();check rest)
      val _=check(!callback_types)
      fun reverse [] result=(guard();pay block 1;result)
        | reverse(value::rest)result=
            (pay block 2;reverse rest(value::result))
      val ordered=reverse(!instructions)[]
      val _=pay block(7+IntInf.fromInt(!next-1))
      val programme=Vector.fromList ordered
      val OwnedConstructorPlan{dependency,...}=constructor
      (* All result-array/selection/check/publication bookkeeping is
         quoted before the shared constructor or any INST/native step. *)
      (* Entry epochs6/once3/vector-length1/array-size1, array header
         and cells(1+next), three helpers, initial slot2, final epochs6,
         output lookup2 and genuine Edge5. *)
      val _=pay block 3
      val _=pay block(30+IntInf.fromInt(!next))
      val _=guard()
      val _=pay block 12
    in FixedXorPlan{block=block,owner=owner,constructor=constructor,
      instructions=programme,output=output,dependency=dependency,
      epoch=epoch,symbols=symbols,used=ref false}end

  fun execute_fixed_xor(FixedXorPlan
      {block,owner,constructor,instructions,output,dependency,
       epoch,symbols,used}) =
    let
      val _=active block
      val _=if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols
        then()else raise ERR "fixed_xor" "clause declaration lifetime changed"
      val _=if !used then raise ERR "fixed_xor" "used plan"else used:=true
      val count=Vector.length instructions
      val proofs=Array.array(count+1,NONE:Thm.thm option)
      fun result index=case Array.sub(proofs,index)of SOME proof=>proof
        | NONE=>raise ERR "fixed_xor" "missing private native result"
      fun inputs []=[] | inputs(index::rest)=result index::inputs rest
      val bridge=theorem block(execute_owned_constructor constructor)
      val _=Array.update(proofs,0,SOME bridge)
      fun run index=if index=count then()else
        let
          val _=active block
          val proof=case Vector.sub(instructions,index)of
              XorClosed{original,substitution,prepared}=>
                execute_prepared_named_inst block substitution original
                  prepared
            | XorPrimitive{opcode,inputs=indices,shape,hypotheses,oracles}=>
                let val proof=primitive xor_identity opcode(inputs indices)
                    val tag=Thm.tag proof
                    val _=if matches shape(Thm.concl proof)andalso
                        null(Tag.axioms_of tag)andalso
                        #1(Tag.dest_tag tag)=oracles andalso
                        List.all(fn term=>List.exists
                          (fn held=>Portable.pointer_eq(term,held))
                          hypotheses)(Thm.hyp proof)then()else
                      raise ERR "fixed_xor" "native transport result changed"
                in proof end
          val _=active block
          val _=Array.update(proofs,index+1,SOME proof)
        in run(index+1)end
      val _=run 0
      val _=active block
      val _=if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols
        then()else raise ERR "fixed_xor" "clause declaration lifetime changed"
    in Edge{owner=owner,theorem=result output,dependency=dependency}end
end
