(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayUnifyTests =
struct
  open HolKernel testutils
  structure G = SmtReplayGraph
  structure U = SmtReplayUnify
  structure P = SmtReplayProof
  structure N = SmtReplayUnifyPlan
  structure B = SmtReplayUnifyBinder
  fun ensure message condition = if condition then () else die message
  fun rejected action = (action ();false) handle Feedback.HOL_ERR _ => true
  fun success (U.Unified result) = result
    | success _ = raise Fail "unexpected unification refusal"
  fun clean theorem =
    let val (oracles,_) = Tag.dest_tag (Thm.tag theorem) in
      null oracles andalso null (Tag.axioms_of (Thm.tag theorem)) end
  fun shared 0 atom = atom
    | shared depth atom =
        let val child = shared (depth-1) atom in
          boolSyntax.mk_conj (child,child) end
  fun variable graph scope kind name ty =
    G.variable graph scope kind (Term.mk_var (name,ty))

  fun run () =
  let
    val _ = tprint "Mixed-type names retain distinct flexible and rigid owners"
    val graph = G.new ()
    val scope = G.root_scope graph
    val x = variable graph scope G.SolverFlexible "same" Type.bool
    val n = variable graph scope G.SolverFlexible "same" numSyntax.num
    val truth = G.constant graph scope boolSyntax.T
    val zero = G.constant graph scope numSyntax.zero_tm
    val generated = variable graph scope G.Generated "same" Type.bool
    val mixed = success (U.unify graph
      {scope=scope,flexible=[x,n],equations=[(x,truth),(n,zero),(truth,x)]})
    val _ = ensure "mixed typed assignments merged or lost a checked endpoint"
      (length (U.assignments mixed) = 2 andalso length (U.proofs mixed) = 3)
    val _ = ensure "generated node gained solver authority"
      (rejected (fn () => ignore (U.unify graph
         {scope=scope,flexible=[generated],equations=[]})) andalso
       (case U.unify graph
         {scope=scope,flexible=[x],equations=[(x,truth),(generated,truth)]} of
            U.NoMatch U.RigidMismatch => true | _ => false))
    val _ = OK ()

    val _ = tprint "Assignment witnesses prove the exact owned endpoint"
    val plan = N.discover graph scope mixed
    val obligations = N.obligations plan
    val block = P.freeze graph
      {scope=scope,roots=N.roots plan,
       sources=List.map #equation obligations,template_limit=8192}
    fun witness (obligation : N.obligation) =
      let fun seek index (first::rest : N.obligation list) =
            if #equation first = #equation obligation then P.source block index
            else seek (index+1) rest
            | seek _ [] = raise Fail "missing assignment"
      in seek 0 obligations end
    val _ = ensure "wrong assignment witness accepted"
      (rejected (fn () => ignore (N.assemble block plan
        (fn _ => P.source block 0))))
    val edges = N.assemble block plan witness
    val _ = List.app (fn (edge,{target,...} : N.equation) =>
      ensure "mixed-type compact witness lost its exact endpoint"
        (Portable.pointer_eq (Thm.concl (P.theorem block edge),
           P.name block target))) (ListPair.zipEq (edges,N.equations plan))
    val target = #target (List.last (N.equations plan))
    val theorem = P.realize block target (List.last edges)
    val _ = ensure "realized witness changed endpoint/Hyp/tags"
      (Portable.pointer_eq
         (Thm.concl theorem,G.representative graph target) andalso
       clean theorem andalso List.all (fn hypothesis =>
         List.exists (fn {equation,...} => Term.aconv hypothesis
           (G.representative graph equation)) obligations) (Thm.hyp theorem))
    val _ = OK ()

    val _ = tprint "Local realization checks exact equality witnesses and Hyp"
    fun local_assignment ({equation,...} : N.obligation) =
      Thm.ASSUME (G.representative graph equation)
    fun realize input = N.realize_local plan
      {assignment=input,binder=fn _ => raise Fail "unexpected binder"}
    val theorem = realize local_assignment
    val _ = ensure "local realization changed its final checked endpoint"
      (Term.aconv (Thm.concl theorem)
        (G.representative graph (#target (List.last (N.equations plan))))
       andalso clean theorem)
    val _ = ensure "local realization accepted a wrong endpoint"
      (rejected (fn () => ignore (realize
        (fn _ => local_assignment (hd obligations)))))
    val _ = ensure "local realization accepted an unrelated hypothesis"
      (rejected (fn () => ignore (realize (fn obligation =>
        Drule.ADD_ASSUM boolSyntax.F (local_assignment obligation)))))
    val invalid_tag = Thm.tag (Thm.mk_oracle_thm "task44_invalid"
      ([],boolSyntax.T))
    val _ = ensure "local realization accepted an unchecked oracle"
      (rejected (fn () => ignore (realize (fn obligation =>
        Thm.add_tag (invalid_tag,local_assignment obligation)))))
    val _ = OK ()

    val _ = tprint "Binder metadata cannot replace an independently checked law"
    val bound = Term.mk_var ("bound",Type.bool)
    fun binder body =
      let
        val frame = G.new_scope graph scope []
        val variable = G.fresh_bound_variable graph frame bound
        val result = G.abstraction graph scope 64 (variable,body)
        val _ = G.close_scope graph frame
      in result end
    val conjunction = G.constant graph scope boolSyntax.conjunction
    fun conj left right = G.application graph scope
      (G.application graph scope (conjunction,left),right)
    val left = binder truth
    val right = binder (G.constant graph scope boolSyntax.F)
    val demands = ref 0
    val unchecked = success (U.unify_with_binders graph
      (fn _ => (demands := !demands+1;SOME []))
      {scope=scope,flexible=[],equations=[(left,right),(right,left)],binders=[]})
    val binder_plan = N.discover graph scope unchecked
    val binder_block = P.freeze graph
      {scope=scope,roots=N.roots binder_plan,sources=[],template_limit=8192}
    val _ = ensure "binder pair was rediscovered or hidden as a definition"
      (!demands = 1 andalso length (N.binder_relations binder_plan) = 1 andalso
       null (N.obligations binder_plan))
    val _ = ensure "binder equality accepted without a checked relation"
      (rejected (fn () => ignore (N.assemble binder_block binder_plan
         (fn _ => raise Fail "unexpected assignment"))) andalso
       not (Option.isSome (B.discover graph scope
         {left=left,right=right,flexible=[],limit=64})))
    val _ = ensure "wrong binder witness endpoint accepted"
      (rejected (fn () => ignore (N.assemble_with_relations binder_block
        binder_plan {assignment=fn _ => raise Fail "unexpected assignment",
          binder=fn _ => P.definition binder_block left})))
    val _ = ensure "local metadata forged a binder equality without a witness"
      (rejected (fn () => ignore (N.realize_local binder_plan
        {assignment=fn _ => raise Fail "unexpected assignment",
         binder=fn relation => Thm.ASSUME
           (G.representative graph (#equation relation))})))
    val _ = ensure "binder discovery assigned a generated/rigid node"
      (rejected (fn () => ignore (U.unify_with_binders graph
        (fn _ => SOME [{variable=generated,residue=truth}])
        {scope=scope,flexible=[x],equations=[(left,right)],binders=[]})))
    val negated = G.application graph scope
      (G.constant graph scope boolSyntax.negation,x)
    val _ = ensure "binder discovery bypassed occurs checking"
      (case U.unify_with_binders graph
        (fn _ => SOME [{variable=x,residue=negated}])
        {scope=scope,flexible=[x],equations=[(left,right)],binders=[]} of
           U.NoMatch U.OccursCheck => true | _ => false)
    val _ = ensure "binder discovery bypassed type checking"
      (case U.unify_with_binders graph
        (fn _ => SOME [{variable=x,residue=zero}])
        {scope=scope,flexible=[x],equations=[(left,right)],binders=[]} of
           U.NoMatch U.TypeMismatch => true | _ => false)
    val nested = G.new_scope graph scope []
    val escaping = variable graph nested G.Bound "escaping" Type.bool
    val _ = ensure "binder discovery bypassed declaration scope checking"
      (case U.unify_with_binders graph
        (fn _ => SOME [{variable=x,residue=escaping}])
        {scope=nested,flexible=[x],equations=[(left,right)],binders=[]} of
           U.NoMatch U.EscapingScope => true | _ => false)
    val foreign = G.new ()
    val namesake = variable foreign (G.root_scope foreign)
      G.SolverFlexible "same" Type.bool
    val _ = ensure "foreign colliding callback assignment accepted"
      (G.node_id namesake = G.node_id x andalso rejected (fn () => ignore
        (U.unify_with_binders graph
          (fn _ => SOME [{variable=namesake,residue=truth}])
          {scope=scope,flexible=[x],equations=[(left,right)],binders=[]})))
    val _ = OK ()

    val _ = tprint "Local binder normalization is simultaneous and checked"
    val y = variable graph scope G.SolverFlexible "other" Type.bool
    val source = binder (conj x y)
    val (normalized,_) = B.normalize graph scope
      {node=source,limit=64,
       resolve=fn node => if node=x then y else if node=y then truth else node}
    val _ = ensure "binder normalization sequentially substituted a residue"
      (Term.aconv (G.representative graph normalized)
        (Term.mk_abs (bound,boolSyntax.mk_conj
          (G.representative graph y,boolSyntax.T))))
    val simple = binder x
    val (_,relation) = B.normalize graph scope
      {node=simple,limit=64,resolve=fn node => if node=x then truth else node}
    val definition = hd (N.obligations (N.discover graph scope (success
      (U.unify graph {scope=scope,flexible=[x],equations=[(x,truth)]}))))
    val equation = #equation definition
    val theorem = B.prove graph scope relation
      [{variable=x,residue=truth,equation=equation}]
    val _ = ensure "checked binder proof lost its exact definition assumption"
      (clean theorem andalso length (Thm.hyp theorem)=1 andalso
       Term.aconv (hd (Thm.hyp theorem)) (G.representative graph equation))
    val _ = ensure "normalizer metadata proved a false binder relation"
      (rejected (fn () => ignore (B.prove graph scope relation [])))
    val repeated = binder (conj x x)
    val residue = #node (G.import graph scope 64 (shared 3 boolSyntax.T))
    val _ = ensure "local binder output was not prospectively admitted"
      ((ignore (B.normalize graph scope
         {node=repeated,limit=40,
          resolve=fn node => if node=x then residue else node});false)
       handle Feedback.HOL_ERR error =>
         Feedback.top_structure_of error = "SmtReplayUnifyBinder" andalso
         Feedback.top_function_of error = "admission")
    val _ = OK ()

    val _ = tprint "Dereferenced binder discovery stays compact in shared DAGs"
    val f = Term.mk_var ("task44_function",Type.mk_type
      ("fun",[Type.bool,Type.bool]))
    val z = Term.mk_var ("task44_value",Type.bool)
    val h = Term.mk_var ("task44_head",Type.mk_type
      ("fun",[Term.type_of f,Type.mk_type
        ("fun",[Term.type_of f,Type.bool])]))
    fun pair a b = Term.mk_comb (Term.mk_comb (h,a),b)
    val lhs = pair f f
    val rhs = pair (Term.mk_abs (bound,z)) (Term.mk_abs (bound,boolSyntax.T))
    val variables = HOLset.addList (Term.empty_tmset,[f,z])
    val expected = HOLset.addList (Term.empty_tmset,
      [boolSyntax.mk_eq (f,Term.mk_abs (bound,boolSyntax.T)),
       boolSyntax.mk_eq (z,boolSyntax.T)])
    fun check depth reversed =
      let
        val left = shared depth (if reversed then rhs else lhs)
        val right = shared depth (if reversed then lhs else rhs)
        val theorem = Library.gen_instantiation (left,right,variables)
        val (actual_left,actual_right) = Term.dest_eq (Thm.concl theorem)
      in ensure "public unifier expanded or changed definitions/endpoints/tags"
        (Portable.pointer_eq (actual_left,left) andalso
         Portable.pointer_eq (actual_right,right) andalso
         HOLset.equal (Thm.hypset theorem,expected) andalso clean theorem) end
    val _ = List.app (fn depth => (check depth false;check depth true)) [0,80]
    val _ = ensure "inconsistent repeated binders accepted"
      (rejected (fn () => ignore (Library.gen_instantiation
        (lhs,pair (Term.mk_abs (bound,boolSyntax.T))
                  (Term.mk_abs (bound,boolSyntax.F)),variables))))
    val _ = ensure "binder discovery captured a free flexible source"
      (rejected (fn () => ignore (Library.gen_instantiation
        (Term.mk_abs (bound,z),Term.mk_abs (bound,bound),variables))))
    val _ = OK ()

    val _ = tprint "Opaque binder refusal retains the original metric/diagnostic"
    fun message action = (action ();raise Fail "expected binder admission gate")
      handle Feedback.HOL_ERR error =>
        (Feedback.top_structure_of error,Feedback.top_function_of error,
         Feedback.message_of error)
    val expected = message (fn () => SmtResource.check_term_size_for
      "BitVector" "binder-opening" (SmtResource.max_bv_replay_term_nodes+1))
    val actual = message (fn () => ignore (Library.gen_instantiation
      (f,Term.mk_abs (bound,shared 21 bound),variables)))
    val _ = ensure "opaque binder changed the standing first diagnostic"
      (actual=expected)
    val inconsistent = shared 80 (pair (Term.mk_abs (bound,boolSyntax.T))
      (Term.mk_abs (bound,boolSyntax.F)))
    val _ = ensure "failed shared binder changed the old fallback diagnostic"
      (message (fn () => ignore (Library.gen_instantiation
         (shared 80 lhs,inconsistent,variables))) = expected)
    val _ = ensure "post-discovery mismatch lost the old fallback diagnostic"
      (message (fn () => ignore (Library.gen_instantiation
         (shared 80 (boolSyntax.mk_conj (lhs,boolSyntax.T)),
          shared 80 (boolSyntax.mk_conj (rhs,boolSyntax.F)),variables))) =
       expected)
    val _ = OK ()

    val _ = tprint "Demanded binders preserve the original internal Type policy"
    fun shared_type 0 = Type.bool
      | shared_type depth =
          let val child=shared_type (depth-1) in child --> child end
    val hidden_type = shared_type 21
    val head = Term.mk_var ("hidden_head",hidden_type --> Type.bool)
    val atom = Term.mk_var ("hidden_atom",hidden_type)
    val hidden = Term.mk_comb (head,atom)
    val hidden_left = Term.mk_abs (bound,boolSyntax.mk_conj (hidden,z))
    val hidden_right = Term.mk_abs
      (bound,boolSyntax.mk_conj (hidden,boolSyntax.T))
    val theorem = Library.gen_instantiation
      (lhs,pair hidden_left hidden_right,variables)
    val expected_hyp = HOLset.addList (Term.empty_tmset,
      [boolSyntax.mk_eq (f,hidden_right),boolSyntax.mk_eq (z,boolSyntax.T)])
    val _ = ensure "legacy internal Type positive changed Goal/Hyp/tags"
      (Term.aconv (Thm.concl theorem)
         (boolSyntax.mk_eq (lhs,pair hidden_left hidden_right)) andalso
       HOLset.equal (Thm.hypset theorem,expected_hyp) andalso clean theorem)
    val _ = ensure "aligned binder lost its stricter standing Type admission"
      (message (fn () => ignore (Library.gen_instantiation
         (hidden_left,hidden_right,variables))) = expected)
    val function_type = hidden_type --> hidden_type
    val large_z = Term.mk_var ("hidden_function",function_type)
    val large_bound = Term.mk_var ("hidden_bound",hidden_type)
    val identity = Term.mk_abs (large_bound,large_bound)
    val use = Term.mk_var ("hidden_use",function_type --> Type.bool)
    val left_body = Term.mk_comb (use,large_z)
    val right_body = Term.mk_comb (use,identity)
    val right = pair (Term.mk_abs (bound,left_body))
      (Term.mk_abs (bound,right_body))
    val theorem = Library.gen_instantiation
      (lhs,right,HOLset.addList (Term.empty_tmset,[f,large_z]))
    val expected_hyp = HOLset.addList (Term.empty_tmset,
      [boolSyntax.mk_eq (f,Term.mk_abs (bound,right_body)),
       boolSyntax.mk_eq (large_z,identity)])
    val _ = ensure "raw binder residue import reintroduced a Type cutoff"
      (Term.aconv (Thm.concl theorem) (boolSyntax.mk_eq (lhs,right)) andalso
       HOLset.equal (Thm.hypset theorem,expected_hyp) andalso clean theorem)
    val _ = OK ()
  in () end
end
