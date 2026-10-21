open HolKernel boolLib
structure PublicCond : LegacyCond_rewr = Cond_rewr
val _ = Paired.check "complete Cond_rewr ascription" true
val p = mk_var ("public_atom", bool)
val rule = CONJUNCT1 (SPEC p boolTheory.AND_CLAUSES)
val controlled : PublicCond.controlled_thm =
  (rule, BoundedRewrites.UNBOUNDED)
val _ : BoundedRewrites.controlled_thm = controlled
val rules = PublicCond.mk_cond_rewrs controlled
val canonical = PublicCond.IMP_EQ_CANON controlled
val quantified = PublicCond.QUANTIFY_CONDITIONS controlled
val conversion : Abbrev.conv = PublicCond.COND_REWR_CONV
  ("public_rule", rule) false (fn _ => ASSUME) []
val input = lhs (concl rule)
val (result, fired) = PublicCond.with_tracking conversion input
val (number, _) = PublicCond.with_tracking (fn n : int => n + 1) 2
val _ : int ref = PublicCond.stack_limit
val _ = Paired.check "original conditional rewrite types and execution"
  (not (null rules) andalso not (null canonical) andalso
   not (null quantified) andalso number = 3 andalso length fired = 1
   andalso PublicCond.ac_term_ord (p, p) = EQUAL
   andalso aconv (concl result) (concl rule) andalso null (hyp result))
