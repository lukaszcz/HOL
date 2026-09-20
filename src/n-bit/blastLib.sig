signature blastLib =
sig
    (* Checked word normalization primitives.  BIT_BLAST_CONV performs its
       internal tree scans, so callers must use it only on separately bounded
       inputs (for example, small schematic terms). *)
    val WORD_SIMP_CONV   : Conv.conv
    val BIT_BLAST_CONV   : Conv.conv
    val BBLAST_CONV      : Conv.conv
    val BBLAST_CONV_WITH_PROFILES :
      (Conv.conv -> Conv.conv) -> (Conv.conv -> Conv.conv) -> Conv.conv
    val BBLAST_PROVE     : Conv.conv
    val BBLAST_PROVE_TAC : Tactic.tactic
    val BBLAST_RULE      : Conv.rule
    val BBLAST_TAC       : Tactic.tactic
    val FULL_BBLAST_TAC  : Tactic.tactic
    val MP_BLASTABLE_TAC : Tactic.tactic
end
