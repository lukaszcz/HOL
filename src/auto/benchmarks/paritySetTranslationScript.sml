open HolKernel Parse boolLib bossLib

val _ = new_theory "paritySetTranslation"

Theorem source_compl_image_fixedpoint:
  !left right.
    ?fixed.
      fixed = COMPL (IMAGE right (COMPL (IMAGE left fixed)))
Proof
  rpt gen_tac
  >> qexists_tac
       `fixedPoint$lfp
          (\set. COMPL (IMAGE right (COMPL (IMAGE left set))))`
  >> irule EQ_SYM
  >> qspec_then
       `(\set. COMPL (IMAGE right (COMPL (IMAGE left set))))`
       mp_tac (cj 1 fixedPointTheory.lfp_fixedpoint)
  >> impl_tac
  >- (simp[fixedPointTheory.monotone_def,
           pred_setTheory.SUBSET_DEF]
      >> metis_tac[])
  >> simp[]
QED

Theorem source_compl_image_fixedpoint_iff:
  !left right.
    ((?fixed.
        fixed = COMPL (IMAGE right (COMPL (IMAGE left fixed)))) <=>
     T)
Proof
  simp[source_compl_image_fixedpoint]
QED

val _ = export_theory()
