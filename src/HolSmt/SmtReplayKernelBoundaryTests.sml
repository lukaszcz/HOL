(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayKernelBoundaryTests =
struct
  open HolKernel testutils
  structure G = SmtReplayGraph

  fun require message yes = if yes then () else raise Fail message
  fun shared 0 leaf = leaf
    | shared depth leaf =
        let val child = shared (depth-1) leaf
        in boolSyntax.mk_conj (child,child) end
  fun shared_type 0 = Type.bool
    | shared_type depth =
        let val child = shared_type (depth-1) in child --> child end
  fun definition left right = Thm.ASSUME (boolSyntax.mk_eq (left,right))
  fun rewrite definitions target =
    Library.checked_definition_rewrite_conv definitions target
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem)
    in null (Tag.axioms_of (Thm.tag theorem)) andalso
       List.all (fn tag => tag = "DISK_THM") tags end
  fun exact_hyps expected theorem =
    let val actual = Thm.hyp theorem
    in length actual = length expected andalso
       List.all (fn term => List.exists (fn original =>
         Portable.pointer_eq (term,original)) expected) actual end
  fun checked target expected hypotheses theorem =
    let val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
    in require "checked definition conversion changed endpoints/Hyp/tags"
      (Term.aconv left target andalso Term.aconv right expected andalso
       exact_hyps hypotheses theorem andalso clean theorem) end
  fun diagnostic action = (action ();raise Fail "expected binder-opening")
    handle Feedback.HOL_ERR error =>
      (Feedback.top_structure_of error,Feedback.top_function_of error,
       Feedback.message_of error)
  fun binder_diagnostic () = diagnostic (fn () =>
    SmtResource.check_term_size_for "BitVector" "binder-opening"
      (SmtResource.max_bv_replay_term_nodes+1))
  fun guarded definitions target =
    require "prospective binder refusal changed the standing diagnostic"
      (diagnostic (fn () => ignore (rewrite definitions target)) =
       binder_diagnostic ())

  val p = Term.mk_var ("task55_p",Type.bool)
  val q = Term.mk_var ("task55_q",Type.bool)
  val a = Term.mk_var ("task55_a",Type.bool)
  val b = Term.mk_var ("task55_b",Type.bool)
  val fresh = Term.mk_var ("task55_fresh",Type.bool)

  fun small () =
    let
      val equation = boolSyntax.mk_eq (p,b)
      val extra = boolSyntax.mk_disj (a,b)
      val rule = Drule.ADD_ASSUM extra (Thm.ASSUME equation)
      val target = Term.mk_abs (b,boolSyntax.mk_conj (p,b))
      val expected = Term.mk_abs (fresh,boolSyntax.mk_conj (b,fresh))
      val _ = checked target expected [equation,extra]
        (rewrite [rule] target)
      val rules = [definition p b,definition b boolSyntax.T]
      val target = Term.mk_abs (p,boolSyntax.mk_conj (p,b))
      val expected = Term.mk_abs (p,boolSyntax.mk_conj (p,boolSyntax.T))
      val _ = checked target expected [Thm.concl (List.nth (rules,1))]
        (rewrite rules target)
      (* A name match at a different Type is not lexical shadowing. *)
      val number = Term.mk_var ("task55_p",numSyntax.num)
      val zero = numSyntax.zero_tm
      val rule = definition number zero
      val target = Term.mk_abs (p,boolSyntax.mk_conj
        (p,boolSyntax.mk_eq (number,zero)))
      val expected = Term.mk_abs (p,boolSyntax.mk_conj
        (p,boolSyntax.mk_eq (zero,zero)))
      val _ = checked target expected [Thm.concl rule] (rewrite [rule] target)
      val rules = [definition p q,definition q b]
      val target = Term.mk_abs (b,p)
      val expected = Term.mk_abs (fresh,b)
      val _ = checked target expected (List.map Thm.concl rules)
        (rewrite rules target)
      val target = Term.mk_abs (b,Term.mk_abs (b,
        boolSyntax.mk_conj (p,b)))
      val expected = Term.mk_abs (fresh,Term.mk_abs (fresh,
        boolSyntax.mk_conj (b,fresh)))
      val rule = definition p b
      val _ = checked target expected [Thm.concl rule]
        (rewrite [rule] target)
      val rhs = shared 12 b
      val rule = definition p rhs
      val target = Term.mk_abs (b,p)
      val expected = Term.mk_abs (fresh,rhs)
      val _ = checked target expected [Thm.concl rule] (rewrite [rule] target)
    in () end

  (* No tree comparison of the expanded endpoints: compare their imported
     application graph IDs instead. This checks actual proof endpoints, not
     just successful return, while retaining the large-output contract. *)
  fun large_endpoint left right =
    let
      val graph = G.new ()
      val scope = G.root_scope graph
      val maximum = case Int.maxInt of SOME n => n
        | NONE => SmtResource.max_metric
      fun node term = #node (G.import graph scope maximum term)
    in node left = node right end
  fun large_outputs () =
    let
      val rhs = shared 24 a
      val rule = definition p rhs
      fun check target expected =
        let
          val theorem = rewrite [rule] target
          val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
        in require "large binder-free output lost its proof/Hyp/tags"
          (large_endpoint left target andalso large_endpoint right expected
           andalso exact_hyps [Thm.concl rule] theorem andalso clean theorem)
        end
      val _ = check p rhs
      val _ = check (boolSyntax.mk_conj (p,p))
        (boolSyntax.mk_conj (rhs,rhs))
      (* Each residue fits; their simultaneous repeated output does not.
         Output size is only native eligibility, never a root refusal. *)
      val rhs = shared 18 a
      val rule = definition p rhs
      val target = boolSyntax.mk_conj (p,p)
      val theorem = rewrite [rule] target
      val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
    in require "repeated bounded residues introduced a whole-output cap"
      (large_endpoint left target andalso
       large_endpoint right (boolSyntax.mk_conj (rhs,rhs)) andalso
       exact_hyps [Thm.concl rule] theorem andalso clean theorem) end

  fun selection () =
    let
      val huge = shared 24 a
      val unused = definition q huge
      val small = definition p boolSyntax.T
      val target = Term.mk_abs (b,p)
      val expected = Term.mk_abs (b,boolSyntax.T)
      val _ = checked target expected [Thm.concl small]
        (rewrite [unused,small] target)
      (* SUBST_CONV selects only the fresh hole left by Term.subst's last
         duplicate entry. An unselected huge RHS must not be admitted. *)
      val unused = definition p huge
      val theta = [{redex=p,residue=definition p boolSyntax.F},
                   {redex=p,residue=small}]
      val native = Drule.SUBST_CONV theta target target
      val _ = checked target expected [Thm.concl small] native
      val _ = checked target expected [Thm.concl small]
        (rewrite [unused,small] target)
      val _ = guarded [small,unused] target
      (* Likewise, a huge selected definition is irrelevant when shadowed. *)
      val target = Term.mk_abs (p,p)
      val _ = checked target target [] (rewrite [unused] target)
      (* The graph branch must make the very same duplicate selection. *)
      val target = shared 24 p
      val theorem = rewrite [unused,small] target
      val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
    in require "graph duplicate selection differs from native substitution"
      (large_endpoint left target andalso
       large_endpoint right (shared 24 boolSyntax.T) andalso
       exact_hyps [Thm.concl small] theorem andalso clean theorem) end

  fun prospective_binders () =
    let
      val huge = shared 21 a
      val rule = definition p huge
      val _ = guarded [rule] (Term.mk_abs (b,p))
      val _ = guarded [rule]
        (Term.mk_abs (b,Term.mk_abs (fresh,p)))
      (* Each RHS fits the raw bound; its two occurrences below ABS do not.
         Admission must count simultaneous output, not just individual RHSs. *)
      val rule = definition p (shared 18 a)
      val _ = guarded [rule]
        (Term.mk_abs (b,boolSyntax.mk_conj (p,p)))
      (* Recheck after each layer exposes a new definition dependency. *)
      val rules = [definition p q,definition q huge]
      val _ = guarded rules (Term.mk_abs (b,p))
    in () end

  fun exhausted_cycles () =
    let
      val rule = definition p (boolSyntax.mk_conj (p,p))
      val target = Term.mk_abs (b,shared 17 p)
      val expected = diagnostic (fn () => raise Feedback.mk_HOL_ERR
        "Library" "checked_definition_rewrite_conv"
        "cyclic definition expansion")
      fun check target = require "exhausted cycle lost first diagnostic"
        (diagnostic (fn () => ignore (rewrite [rule] target)) = expected)
      (* The first output fits. At remaining=0 the second output exceeds
         the binder bound, but the original worker reports cyclic expansion
         before checking that output. Neither site may do unsafe SUBST just
         to recover that diagnostic. *)
      val _ = check target
      val context = shared 24 (Term.mk_comb (target,boolSyntax.T))
    in check context end

  fun competing_cycles () =
    let
      val cycle = definition p (boolSyntax.mk_neg p)
      val growth = definition q (shared 19 a)
      val application = Term.mk_comb (Term.mk_abs (b,q),boolSyntax.T)
      val cyclic = diagnostic (fn () => raise Feedback.mk_HOL_ERR
        "Library" "checked_definition_rewrite_conv"
        "cyclic definition expansion")
      fun check rules target expected = require
        "prospective binder admission changed graph first-exception order"
        (diagnostic (fn () => ignore (rewrite rules target)) = expected)
      val rules = [cycle,growth]
      val _ = check rules (boolSyntax.mk_conj (p,application)) cyclic
      (* A global reachable-cycle check would incorrectly choose the cycle
         here. Preserve left-to-right discovery in both directions. *)
      val _ = check rules (boolSyntax.mk_conj (application,p))
        (binder_diagnostic ())
      val indirect = definition fresh (boolSyntax.mk_neg p)
      val _ = check (indirect::rules)
        (boolSyntax.mk_conj (fresh,application)) cyclic
      (* The earlier binder fits its first output but fails on the next
         layer. It must still beat a later graph cycle. *)
      val later = definition a (shared 19 boolSyntax.T)
      val chain = definition q a
      val first = Term.mk_comb (Term.mk_abs (b,q),boolSyntax.T)
      val last = Term.mk_comb (Term.mk_abs (b,fresh),boolSyntax.T)
      val _ = check [cycle,chain,later,definition fresh (shared 19 a)]
        (boolSyntax.mk_conj (first,boolSyntax.mk_conj (p,last)))
        (binder_diagnostic ())
      (* This binder is inserted FROM a residue, so it must not receive the
         virtual initial layer a second time. A bound occurrence remains
         shadowed while the separate right binder causes the refusal. *)
      val identity = Term.mk_abs (q,q)
      val inserted = definition fresh (Term.mk_comb (identity,boolSyntax.T))
      val _ = check (inserted::rules)
        (boolSyntax.mk_conj (fresh,boolSyntax.mk_conj (p,application))) cyclic
    in () end

  (* A typed FVL over this tiny body compares two equal but physically
     distinct exponential Types. Native SUBST would do that BEFORE returning
     any step, in either kernel. Counting syntax and shadowing needs neither
     typed FVL nor Type traversal. This operational poison witnesses an early
     guard, not merely the eventual oversized-binder exception. No global
     substitution hook or test-only production callback is involved. *)
  fun poison_binder () =
    let
      val first_type = shared_type 80
      val second_type = shared_type 80
      fun distinct 0 _ _ = true
        | distinct depth left right =
            not (Portable.pointer_eq (left,right)) andalso
            distinct (depth-1) (#1 (Type.dom_rng left))
              (#1 (Type.dom_rng right))
      val _ = require "typed-FVL poison lost independent Type allocations"
        (distinct 80 first_type second_type)
      fun atom index ty =
        let
          val head = Term.mk_var ("task55_poison_head" ^ index,
            ty --> Type.bool)
          val argument = Term.mk_var ("task55_poison_argument",ty)
        in Term.mk_comb (head,argument) end
      val first = atom "1" first_type
      val second = atom "2" second_type
    in Term.mk_abs (b,boolSyntax.mk_conj
      (p,boolSyntax.mk_conj (first,second))) end
  fun before_native () =
    Timeout.apply (Time.fromSeconds 30) (fn () =>
      let
        val target = poison_binder ()
        val rule = definition p (shared 21 a)
        val _ = guarded [rule] target
        (* The oversized source selects graph conversion immediately. Its
           lambda is opaque during import, so the same poison now witnesses
           the independent graph-branch binder helper's preflight. *)
        val context = shared 24 (Term.mk_comb (target,boolSyntax.T))
        val _ = guarded [rule] context
      in () end) ()

  (* Name collisions force exact typed variable selection. Put the poison
     both before and after the excessive prefix: short-circuiting alone is
     insufficient. The polymorphic prefix keeps REFL construction cheap. *)
  fun annotation_collisions () =
    Timeout.apply (Time.fromSeconds 3) (fn () =>
      let
        fun check prefix matching =
          let
            val first_type = Type.alpha --> shared_type 80
            val second_type = Type.alpha --> shared_type 80
            val _ = require "collision poison lost independent Types"
              (not (Portable.pointer_eq (first_type,second_type)))
            val u = Term.mk_var ("task55_same",first_type)
            val r = Term.mk_var
              (if matching then "task55_same" else "task55_other",
               second_type)
            val h = Term.mk_var ("task55_h",first_type --> Type.bool)
            val atom = Term.mk_comb (h,u)
            val body = if prefix then boolSyntax.mk_conj (atom,p)
                       else boolSyntax.mk_conj (p,atom)
            val target = Term.mk_abs (b,body)
            val rules = [definition p (shared 19 a),Thm.REFL r]
            val _ = guarded rules target
            val context = shared 24 (Term.mk_comb (target,boolSyntax.T))
          in guarded rules context end
      in
        check false false;check false true;
        check true false;check true true
      end) ()

  fun run () =
    (tprint "Checked definitions preserve capture, shadowing, Hyp and tags";
     small ();OK ();
     tprint "Checked definitions preserve small-input large binder-free DAGs";
     large_outputs ();OK ();
     tprint "Checked definitions admit only selected unshadowed residues";
     selection ();OK ();
     tprint "Checked definitions bound prospective simultaneous binder output";
     prospective_binders ();OK ();
     tprint "Both definition sites retain exhausted-cycle diagnostic priority";
     exhausted_cycles ();OK ();
     tprint "Both checked-definition native sites guard before typed FVL";
     before_native ();OK ();
     tprint "Prospective binders preserve competing graph first exceptions";
     competing_cycles ();OK ();
     tprint "Prospective selection handles colliding exponential Types";
     annotation_collisions ();OK ())
end
