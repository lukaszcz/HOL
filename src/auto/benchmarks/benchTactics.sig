signature benchTactics =
sig
  (* The HOL4 tactics an Isabelle method name stands for, in the order
     the method tries them.  Nearly every method names one; the list
     exists because [algebra] is [ring_tac ORELSE ideal_tac] in
     Isabelle, and a chooser that picked a side by reading the goal
     would make a mapping failure look like a HOL4 limitation.

     The goal is consulted only for its carrier type.  A numeric method
     names a decision procedure, and which instance of that procedure
     applies is a property of the statement's type rather than of the
     individual problem; every other method ignores the goal entirely.
     Nothing else about the goal is read, so this dispatch cannot become
     a per-goal hint however the corpus grows.

     An Isabelle method the table does not cover raises, naming it.
     There is no fallback tactic: a method silently mapped to something
     plausible would let the measurement claim a result the source proof
     never asked for.  The list a covered method returns is never
     empty. *)
  val tactics : string -> Term.term -> benchLib.tactic_id list
  val methods : string list
end
