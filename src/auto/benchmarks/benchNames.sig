signature benchNames =
sig
  (* One Isabelle lemma name, exactly as a source proof cites it, mapped
     to one HOL4 theorem.  The table is keyed by the Isabelle name alone:
     a goal identifier must not appear in it, in any form, including in a
     comment, and a name resolves to the same theorem for every goal that
     cites it.

     A citation carrying an attribute that changes the theorem --
     [symmetric], [OF ...], [THEN ...] -- is its own key.  A citation
     whose attribute only instantiates it -- [of ...], [where ...] --
     is its own key too, and resolves either to the general theorem or,
     through [instantiated], to the instance the source method wrote.
     Matching recovers an instantiation only when the general
     statement's left-hand side occurs in the goal; where the instance
     collapses a constant -- an identity key turning [insort_key f]
     into [insort] -- it does not, and the general theorem reaches the
     goal not at all.  The instantiating terms are transcribed from the
     method, never chosen per goal, so the entry says the same thing
     for every goal that cites that string.

     Each key appears once.  [lookup] takes the first entry under a
     name, so a second one is unreachable and free to contradict it;
     the selftest rejects a repeat. *)

  datatype resolution =
      (* More than one theorem in two cases only: the Isabelle name
         abbreviates a fact list -- [option.splits], [ac_simps] -- in
         which case the entry lists what that abbreviation stands for;
         or one Isabelle lemma's content is spread over several HOL4
         theorems, as [set_takeWhileD]'s conjunctive conclusion is. *)
      Theorems of benchLib.named_thm list
    (* An Isar context fact -- [assms], [that], or a label bound by the
       enclosing lemma's [assumes].  The translated goal already carries
       it as a hypothesis, so it contributes no argument. *)
    | Context
    (* An Isabelle definition the translation writes out in the goal, so
       the goal carries a beta-redex where Isabelle carries a constant
       and the citation has nothing left to unfold. *)
    | Inlined
    (* A rule a HOL4 engine applies without being handed it, or an
       arithmetic fact the ambient simpset already carries. *)
    | Native
    (* An Isabelle fact HOL4 has no counterpart for, in the library or
       in the translation theory.  A goal citing one cannot be given the
       argument its source proof had; the measurement reports it as
       translation-limited rather than pretending otherwise. *)
    | Unrepresented

  val lookup : string -> resolution option
  (* Raises, naming the citation, when the table does not cover it. *)
  val resolve : string -> resolution
  (* The resolver [benchRecipe.to_recipe] wants: empty for every
     resolution that names no theorem, an exception for an unknown
     citation. *)
  val theorems : string -> benchLib.named_thm list
  val names : string list
end
