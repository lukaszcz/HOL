(* Fixed kernel programme only; no Source or ownership admission. *)
signature SmtReplaySimultaneousRealization =
sig
  (* The owning caller admits the compact closing law and substitution
     before entry. Large residues are inserted simultaneously, never
     revisited by matching, INST_TYPE or an ALPHA pass here. *)
  val instantiate :
    {guard:unit -> unit,error:string -> exn,
     contexts:Term.term list,proof:Thm.thm,
     substitution:(Term.term,Term.term) Lib.subst} -> Thm.thm
  (* Witnesses are genuine already checked theorems. This function mints
     no receipt and cannot declare any hypothesis an original Source. *)
  val apply :
    {guard:unit -> unit,law:Thm.thm,witnesses:Thm.thm list} -> Thm.thm
end
