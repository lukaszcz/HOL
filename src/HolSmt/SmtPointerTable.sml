(* Copyright (c) 2026 The HOL4 contributors. *)

structure SmtPointerTable :> SmtPointerTable =
struct
  type 'a table =
    {hint : int -> Term.term -> int, ceiling : int,
     buckets : (Term.term * 'a) list Array.array ref, entries : int ref}

  fun new {hint, initial, ceiling} : 'a table =
    {hint = hint, ceiling = ceiling,
     buckets = ref (Array.array (initial, [])), entries = ref 0}

  fun peek entries term =
    case List.find (fn (saved, _) => Portable.pointer_eq (term, saved))
        entries of
      NONE => NONE
    | SOME (_, value) => SOME value

  fun lookup ({hint, buckets, ...} : 'a table) term =
    let val table = !buckets in
      peek (Array.sub (table, hint (Array.length table) term)) term
    end

  (* Cons onto bucket [index] of the current array, growing if needed. *)
  fun place ({hint, ceiling, buckets, entries} : 'a table) index term value =
    let
      val table = !buckets
      val size = Array.length table
      val _ = Array.update
        (table, index, (term, value) :: Array.sub (table, index))
      val _ = entries := !entries + 1
    in
      if size < ceiling andalso !entries > 2 * size then
        let
          val size = Int.min (ceiling, 2 * size + 1)
          val grown = Array.array (size, [])
          fun move (entry as (term, _)) =
            let val index = hint size term in
              Array.update (grown, index, entry :: Array.sub (grown, index))
            end
          (* Preserve newest-first lookup even for repeated keys. *)
          val _ = Array.app (List.app move o List.rev) table
        in buckets := grown end
      else ()
    end

  fun insert (table as {hint, buckets, ...} : 'a table) term value =
    let val current = !buckets in
      place table (hint (Array.length current) term) term value
    end

  fun clear ({buckets, entries, ...} : 'a table) =
    (Array.modify (fn _ => []) (!buckets); entries := 0)

  fun mark (table as {hint, buckets, ...} : unit table) term =
    let
      val current = !buckets
      val index = hint (Array.length current) term
    in
      case peek (Array.sub (current, index)) term of
        SOME () => false
      | NONE => (place table index term (); true)
    end

  fun size ({entries, ...} : 'a table) = !entries
end
