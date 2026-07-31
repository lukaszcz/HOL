(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: SML type of Z3 proofs *)

structure Z3_Proof =
struct

  (* A single Z3 inference step is represented as a value of type
     'proofterm'.  The constructors below are the compatibility layer
     used by the existing replay code; rule discovery and parser lookup
     are driven by the registry that follows the datatype.  Premises of
     the inference step are given by proofterms.  However, to allow
     encoding of a proof as a graph (rather than a tree), there is an
     'ID' constructor that merely takes an integer argument (which is an
     index into the 'proof' dictionary, cf. type 'proof' below).  The
     inference step's conclusion is given as a term.  Additionally,
     there is a 'THEOREM' constructor that encapsulates the theorem that
     is obtained from replaying the inference step in HOL. *)

  (* At the time of writing (2010-09-08), the Z3 documentation
     unfortunately is outdated with respect to the inference rules
     that the most recent Z3 version (2.11) uses.  I have applied Z3
     to a large number of SMT-LIB benchmarks.  'proofterm' provides a
     constructor for each inference rule that appears (at least once)
     in the generated proofs.  Rules that only appear in compressed Z3
     proofs are NOT supported.

     To add another inference rule, extend 'proof_rule_registry' below.
     If the rule has a new replay behavior, add a replay handler and
     bind its handler identity in the parser/replay compatibility
     wrappers. *)

  type th_lemma_metadata = {
    theory : string,
    subkind : string option,
    indices : string list
  }

  fun mk_th_lemma_metadata (theory, subkind, indices) : th_lemma_metadata = {
    theory = theory,
    subkind = subkind,
    indices = indices
  }

  fun th_lemma_metadata_to_string ({theory, subkind, indices}
      : th_lemma_metadata) =
    "theory=" ^ theory ^
    ", subkind=" ^ Option.getOpt (subkind, "<none>") ^
    ", indices=[" ^ String.concatWith ", " indices ^ "]"

  fun th_lemma_rule_name metadata =
    "th_lemma[" ^ th_lemma_metadata_to_string metadata ^ "]"

  datatype proofterm = AND_ELIM of proofterm * Term.term
                     | APPLY_DEF of proofterm * Term.term
                     | ASSERTED of Term.term
                     | COMMUTATIVITY of Term.term
                     | DEF_AXIOM of Term.term
                     | ELIM_UNUSED of Term.term
                     | HYPOTHESIS of Term.term
                     | IFF_FALSE of proofterm * Term.term
                     | IFF_TRUE of proofterm * Term.term
                     | INTRO_DEF of Term.term
                     | LEMMA of proofterm * Term.term
                     | MONOTONICITY of proofterm list * Term.term
                     | MP of proofterm * proofterm * Term.term
                     | MP_EQ of proofterm * proofterm * Term.term
                     | NNF_NEG of proofterm list * Term.term
                     | NNF_POS of proofterm list * Term.term
                     | NOT_OR_ELIM of proofterm * Term.term
                     | PROOF_BIND of Term.term list * proofterm
                     | QUANT_INST of Term.term list * Term.term
                     | QUANT_INTRO of proofterm * Term.term
                     | REFL of Term.term
                     | REWRITE of Term.term
                     | SKOLEM of Term.term
                     | SYMM of proofterm * Term.term
                     | TH_LEMMA_ARITH of th_lemma_metadata * proofterm list *
                         Term.term
                     | TH_LEMMA_ARRAY of th_lemma_metadata * proofterm list *
                         Term.term
                     | TH_LEMMA_BASIC of th_lemma_metadata * proofterm list *
                         Term.term
                     | TH_LEMMA_BV of th_lemma_metadata * proofterm list *
                         Term.term
                     | TH_LEMMA_DATATYPE of th_lemma_metadata *
                         proofterm list * Term.term
                     | TH_LEMMA_SEQ of th_lemma_metadata * proofterm list *
                         Term.term
                     | TH_LEMMA_CHAR of th_lemma_metadata * proofterm list *
                         Term.term
                     | TH_LEMMA_ADVANCED of th_lemma_metadata * proofterm list *
                         Term.term
                     | TRANS of proofterm * proofterm * Term.term
                     | TRANS_STAR of proofterm list * Term.term
                     | TRUE_AXIOM of Term.term
                     | UNIT_RESOLUTION of proofterm list * Term.term
                     | ID of int
                     | THEOREM of Thm.thm

  datatype proof_premise_shape = ZeroPremises
                               | OnePremise
                               | TwoPremises
                               | ListPremises
                               | TermArguments

  datatype proof_conclusion_shape = BooleanConclusion

  datatype proof_version_support = AllZ3Versions
                                 | Z3VersionPrefixes of string list
                                 | Z3Versions of string list

  type proof_rule = {
    name : string,
    aliases : string list,
    version_support : proof_version_support,
    premise_shape : proof_premise_shape,
    conclusion_shape : proof_conclusion_shape,
    replay_handler : string
  }

  val unknown_z3_version = "<unknown>"

  (* The exact tested anchors, whose proof dialect was measured by the version
     verifier; keep in sync with the "Supported Z3 versions" table in
     src/HolSmt/README.  A patch release does not change the dialect, so each
     entry stands for its whole `major.minor` series.  An unlisted version is
     not rejected: `resolve_version` warns and replays it under the nearest
     anchor. *)
  val supported_z3_versions =
    ["4.11.2", "4.12.4", "4.13.0", "4.14.1", "4.15.3"]

  fun mk_rule_with_version version_support
      (name, aliases, premise_shape, replay_handler) : proof_rule = {
    name = name,
    aliases = aliases,
    version_support = version_support,
    premise_shape = premise_shape,
    conclusion_shape = BooleanConclusion,
    replay_handler = replay_handler
  }

  fun mk_rule args = mk_rule_with_version AllZ3Versions args

  fun mk_z3_4_rule args =
    mk_rule_with_version (Z3VersionPrefixes ["4."]) args

  val proof_rule_registry : proof_rule list = [
    mk_rule ("and-elim", [], OnePremise, "and_elim"),
    (* Version gates come from a per-rule histogram measured over the 4.11.2,
       4.12.4, 4.13.0, 4.14.1, and 4.15.3 proof corpora (Z3 4.x is the only
       supported dialect).  We gate rules with measured 4.x evidence to the
       4.x dialect when that remains consistent with the version verifier in
       the `holsmt-validation` repository, which shows that some 4.11.2
       non-observations are corpus gaps rather than version gaps.
       Never-observed residual rules stay at the default AllZ3Versions until
       a later measurement or owner decision says otherwise. *)
    mk_z3_4_rule ("apply-def", [], OnePremise, "apply_def"),
    mk_rule ("asserted", [], ZeroPremises, "asserted"),
    mk_rule ("commutativity", [], ZeroPremises, "commutativity"),
    mk_rule ("def-axiom", [], ZeroPremises, "def_axiom"),
    mk_rule ("elim-unused", [], ZeroPremises, "elim_unused"),
    mk_rule ("hypothesis", [], ZeroPremises, "hypothesis"),
    mk_rule ("iff-false", [], OnePremise, "iff_false"),
    mk_rule ("iff-true", [], OnePremise, "iff_true"),
    mk_z3_4_rule ("intro-def", [], ZeroPremises, "intro_def"),
    mk_rule ("lemma", [], OnePremise, "lemma"),
    mk_rule ("monotonicity", [], ListPremises, "monotonicity"),
    mk_rule ("mp", [], TwoPremises, "mp"),
    mk_rule ("mp~", ["mp-eq", "mp_eq"], TwoPremises, "mp_eq"),
    mk_rule ("nnf-neg", [], ListPremises, "nnf_neg"),
    mk_rule ("nnf-pos", [], ListPremises, "nnf_pos"),
    mk_rule ("not-or-elim", [], OnePremise, "not_or_elim"),
    (* The complete C1 corpus observes proof-bind in each tested Z3 series.
       Keep the gate pinned to those measured dialects; version resolution
       maps patch and untested releases to one of these anchors. *)
    mk_rule_with_version (Z3VersionPrefixes
      ["4.11.", "4.12.", "4.13.", "4.14.", "4.15."])
      ("proof-bind", [], OnePremise, "proof_bind"),
    mk_rule ("quant-inst", [], TermArguments, "quant_inst"),
    mk_rule ("quant-intro", [], OnePremise, "quant_intro"),
    mk_rule ("refl", [], ZeroPremises, "refl"),
    mk_rule ("rewrite", [], ZeroPremises, "rewrite"),
    mk_rule ("sk", ["skolem"], ZeroPremises, "skolem"),
    mk_rule ("symm", [], OnePremise, "symm"),
    mk_rule ("th-lemma-arith", ["th-lemma[arith]"], ListPremises,
      "th_lemma[arith]"),
    mk_rule ("th-lemma-array", ["th-lemma[array]"], ListPremises,
      "th_lemma[array]"),
    mk_rule ("th-lemma-basic", ["th-lemma[basic]"], ListPremises,
      "th_lemma[basic]"),
    mk_rule ("th-lemma-bv", ["th-lemma[bv]"], ListPremises,
      "th_lemma[bv]"),
    mk_rule ("th-lemma-fp", ["th-lemma[fp]", "th-lemma-fpa",
      "th-lemma[fpa]", "th-lemma-floating-point",
      "th-lemma[floating-point]"], ListPremises, "th_lemma[advanced]"),
    mk_z3_4_rule ("th-lemma-seq", ["th-lemma[seq]", "th-lemma-sequence",
      "th-lemma[sequence]", "th-lemma-sequences", "th-lemma[sequences]"],
      ListPremises, "th_lemma[seq]"),
    mk_z3_4_rule ("th-lemma-string", ["th-lemma[string]",
      "th-lemma-strings",
      "th-lemma[strings]", "th-lemma-str", "th-lemma[str]"],
      ListPremises, "th_lemma[seq]"),
    mk_z3_4_rule ("th-lemma-regexp", ["th-lemma[regexp]",
      "th-lemma-regex",
      "th-lemma[regex]", "th-lemma-re", "th-lemma[re]"], ListPremises,
      "th_lemma[seq]"),
    mk_z3_4_rule ("th-lemma-char", ["th-lemma[char]",
      "th-lemma-character", "th-lemma[character]",
      "th-lemma-characters", "th-lemma[characters]"], ListPremises,
      "th_lemma[char]"),
    mk_rule ("th-lemma-datatype", ["th-lemma[datatype]",
      "th-lemma-datatypes", "th-lemma[datatypes]", "th-lemma-dt",
      "th-lemma[dt]"], ListPremises, "th_lemma[datatype]"),
    mk_rule ("th-lemma-nonlinear-arith", ["th-lemma[nonlinear-arith]",
      "th-lemma-nonlinear", "th-lemma[nonlinear]", "th-lemma-nla",
      "th-lemma[nla]", "th-lemma-nra", "th-lemma[nra]", "th-lemma-nia",
      "th-lemma[nia]"], ListPremises, "th_lemma[advanced]"),
    mk_rule ("trans", [], TwoPremises, "trans"),
    mk_rule ("trans*", ["trans-star"], ListPremises, "trans_star"),
    mk_rule ("true-axiom", [], ZeroPremises, "true_axiom"),
    mk_rule ("unit-resolution", [], ListPremises, "unit_resolution")
  ]

  fun rule_names (rule : proof_rule) = #name rule :: #aliases rule

  fun rule_matches name rule = List.exists (Lib.equal name) (rule_names rule)

  (* Resolves a discovered Z3 version to the tested anchor whose proof dialect
     the registry replays under; see `Library`.  Callers resolve once, at the
     proof-parsing boundary, so `version_supported` below always sees a tested
     anchor and an unknown or untested Z3 never fails a proof by itself -- it
     warns and replays under the nearest measured dialect. *)
  fun resolve_version version =
    Library.resolve_solver_version
      {solver = "Z3", supported = supported_z3_versions, version = version}

  fun version_supported version (rule : proof_rule) =
    case #version_support rule of
      AllZ3Versions => true
    | Z3Versions versions => List.exists (Lib.equal version) versions
    | Z3VersionPrefixes prefixes =>
        List.exists (fn prefix => String.isPrefix prefix version) prefixes

  fun lookup_rule (version : string) (name : string) =
    case List.find (rule_matches name) proof_rule_registry of
      SOME rule => if version_supported version rule then SOME rule else NONE
    | NONE => NONE

  fun lookup_rule_by_handler (handler : string) =
    List.find (fn (rule : proof_rule) => #replay_handler rule = handler)
      proof_rule_registry

  fun registry_lookup_failure (version : string) (name : string) =
    if Option.isSome (List.find (rule_matches name) proof_rule_registry) then
      "Z3 proof rule registry lookup failed: rule " ^ name ^
      " not supported by Z3 version " ^ version
    else
      "Z3 proof rule registry lookup failed: unknown rule " ^ name ^
      " for Z3 version " ^ version

  (* The Z3 proof is a directed acyclic graph of inference steps.  A
     unique integer ID is assigned to each inference step.  Note that
     Z3 assigns no ID to the proof's root node, which derives the
     final theorem "... |- F".  We will use ID 0 for the root node.

     Additionally, Z3 also defines variables in proofs, which we keep
     keep track of in a set, so we can properly replay the proof. *)

  type proof_steps = (int, proofterm) Redblackmap.dict

  (* A bit-decomposition is only a syntactic hint at this stage.  In
     particular, [equation] is not an assumption and [bv_var] has not yet
     been given a HOL definition.  Floating-point replay uses the association
     to recognize the rewrite at which it is safe to construct and prove such
     a definition. *)
  type bit_decomposition = {
    fp_var : Term.term,
    bv_var : Term.term,
    equation : Term.term
  }

  type proof = {
    steps : proof_steps,
    vars : Term.term HOLset.set,
    bit_decompositions : bit_decomposition list,
    z3_version : string
  }

  fun mk_proof (steps, vars, bit_decompositions, z3_version) : proof = {
    steps = steps,
    vars = vars,
    bit_decompositions = bit_decompositions,
    z3_version = z3_version
  }

  fun empty_proof z3_version = mk_proof
    (Redblackmap.mkDict Int.compare, Term.empty_tmset, [], z3_version)

  fun proof_steps (proof : proof) = #steps proof
  fun proof_vars (proof : proof) = #vars proof
  fun proof_bit_decompositions (proof : proof) = #bit_decompositions proof
  fun proof_version (proof : proof) = #z3_version proof

  fun update_proof_steps (proof : proof) steps = {
    steps = steps,
    vars = #vars proof,
    bit_decompositions = #bit_decompositions proof,
    z3_version = #z3_version proof
  }

  fun update_proof_vars (proof : proof) vars = {
    steps = #steps proof,
    vars = vars,
    bit_decompositions = #bit_decompositions proof,
    z3_version = #z3_version proof
  }

  fun update_proof_bit_decompositions (proof : proof) bit_decompositions = {
    steps = #steps proof,
    vars = #vars proof,
    bit_decompositions = bit_decompositions,
    z3_version = #z3_version proof
  }

  fun proofterm_premises (AND_ELIM (pt, _)) = [pt]
    | proofterm_premises (APPLY_DEF (pt, _)) = [pt]
    | proofterm_premises (IFF_FALSE (pt, _)) = [pt]
    | proofterm_premises (IFF_TRUE (pt, _)) = [pt]
    | proofterm_premises (LEMMA (pt, _)) = [pt]
    | proofterm_premises (MONOTONICITY (pts, _)) = pts
    | proofterm_premises (MP (pt1, pt2, _)) = [pt1, pt2]
    | proofterm_premises (MP_EQ (pt1, pt2, _)) = [pt1, pt2]
    | proofterm_premises (NNF_NEG (pts, _)) = pts
    | proofterm_premises (NNF_POS (pts, _)) = pts
    | proofterm_premises (NOT_OR_ELIM (pt, _)) = [pt]
    | proofterm_premises (PROOF_BIND (_, pt)) = [pt]
    | proofterm_premises (QUANT_INTRO (pt, _)) = [pt]
    | proofterm_premises (SYMM (pt, _)) = [pt]
    | proofterm_premises (TH_LEMMA_ARITH (_, pts, _)) = pts
    | proofterm_premises (TH_LEMMA_ARRAY (_, pts, _)) = pts
    | proofterm_premises (TH_LEMMA_BASIC (_, pts, _)) = pts
    | proofterm_premises (TH_LEMMA_BV (_, pts, _)) = pts
    | proofterm_premises (TH_LEMMA_DATATYPE (_, pts, _)) = pts
    | proofterm_premises (TH_LEMMA_SEQ (_, pts, _)) = pts
    | proofterm_premises (TH_LEMMA_CHAR (_, pts, _)) = pts
    | proofterm_premises (TH_LEMMA_ADVANCED (_, pts, _)) = pts
    | proofterm_premises (TRANS (pt1, pt2, _)) = [pt1, pt2]
    | proofterm_premises (TRANS_STAR (pts, _)) = pts
    | proofterm_premises (UNIT_RESOLUTION (pts, _)) = pts
    | proofterm_premises _ = []

end
