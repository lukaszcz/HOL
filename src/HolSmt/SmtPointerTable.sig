signature SmtPointerTable =
sig
  type 'a table

  (* [hint modulus term] selects a bucket in [0, modulus).  It only places
     keys: lookups compare by physical identity, so the hint supplies no
     equality or proof fact.  The table starts with [initial] buckets and
     doubles (plus one) when entries exceed twice the bucket count, never
     beyond [ceiling] buckets. *)
  val new : {hint : int -> Term.term -> int, initial : int, ceiling : int}
            -> 'a table
  (* The most recent binding of a physically identical key. *)
  val lookup : 'a table -> Term.term -> 'a option
  val insert : 'a table -> Term.term -> 'a -> unit
  (* Drop every entry.  The bucket array keeps its grown size. *)
  val clear : 'a table -> unit
  (* True exactly on the first visit of a pointer. *)
  val mark : unit table -> Term.term -> bool
  (* Number of insertions since creation or the last [clear]. *)
  val size : 'a table -> int
end
