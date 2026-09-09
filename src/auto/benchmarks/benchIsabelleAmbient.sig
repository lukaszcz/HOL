(* Why each constant the translation defines is, or is not, in the
   ambient set: the command Isabelle introduces it with, mined from the
   Isabelle2025-2 sources, where the constant is Isabelle's; the
   translation's own reason for naming it, where it is not. *)
signature benchIsabelleAmbient =
sig

  datatype introduction =
      (* Declares its equations simp. *)
      Fun
    | Primrec
      (* A datatype selector or predicator: the package declares those
         equations simp too. *)
    | Datatype
      (* A constant Isabelle's simpset reduces without being told,
         though the introducing command declared nothing: a separately
         declared characterisation ([sort_key_simps], [atLeast_iff]), or
         an inductive set whose introduction rules carry [simp]. *)
    | Simp
      (* The translation names a term Isabelle writes inline -- an
         [abbreviation] among them -- so an Isabelle goal never contains
         the constant at all, and the equation restores the term the
         source proof worked on. *)
    | Notation
      (* The translation's own encoding of a source type HOL4 states
         differently.  Unfolding it is reading the representation, not a
         source definition. *)
    | Representation
      (* The constant renames one HOL4 already has, argument for
         argument.  The equation is the bridge between two vocabularies
         rather than a source definition, and the facts an Isabelle
         method reads about the source constant answer to HOL4's.  This
         is why a plain [definition] is nonetheless supplied; where
         Isabelle's own command already makes the constant ambient, that
         command is recorded instead, being the more particular fact. *)
    | Alias
      (* Declares no simp equation: Isabelle's simpset leaves the
         constant folded. *)
    | Definition
      (* [function] proves its equations but declares none simp, unlike
         [fun]. *)
    | Function
      (* A datatype constructor whose type carries no ambient selector
         equations: opaque to Isabelle's simpset, so the translation's
         defining equation goes beyond what the source has.  A
         constructor of a type HOL4 states differently is Representation
         instead -- there the selector equations Isabelle's simpset does
         carry have no HOL4 counterpart but the encoding. *)
    | Constructor

  (* Definition theorem name, how Isabelle introduces the constant it
     defines, and the Isabelle line that says so. *)
  val introductions : (string * introduction * string) list

  val ambient : introduction -> bool

  (* Raises on a definition the table does not cover: the corpus and the
     table are kept in step by the selftest, and a silent default here
     would decide the measurement instead. *)
  val is_ambient : string -> bool

end
