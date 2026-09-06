def proved: .szs == "Theorem";
def recon: proved and .recon_ok == true;
($old|sort_by(.goal_id)) as $o | ($new|sort_by(.goal_id)) as $n |
[range(0;3000) | select(
  (($o[.]|proved) and (($n[.]|proved)|not)) or
  (($o[.]|recon) and (($n[.]|recon)|not))) |
  {goal_id:$o[.].goal_id,
   proved_loss:(($o[.]|proved) and (($n[.]|proved)|not)),
   reconstruction_loss:(($o[.]|recon) and (($n[.]|recon)|not)),
   phase2:{szs:$o[.].szs,recon_ok:$o[.].recon_ok,
     prover:$o[.].prover,error:$o[.].error},
   phase3:{szs:$n[.].szs,recon_ok:$n[.].recon_ok,
     prover:$n[.].prover,error:$n[.].error,
     stop:$n[.].stop,slices:$n[.].slices}}]
