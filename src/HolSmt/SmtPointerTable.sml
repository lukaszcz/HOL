structure SmtPointerTable :> SmtPointerTable =
struct
  type 'a table =
    {hint : int -> Term.term -> int, ceiling : int,
     buckets : (Term.term * 'a) list Array.array ref, entries : int ref}

  fun new {hint, initial, ceiling} : 'a table =
    {hint = hint, ceiling = ceiling,
     buckets = ref (Array.array (initial, [])), entries = ref 0}

  fun lookup ({hint, buckets, ...} : 'a table) term =
    let val table = !buckets in
      case List.find (fn (saved, _) => Portable.pointer_eq (term, saved))
          (Array.sub (table, hint (Array.length table) term)) of
        NONE => NONE
      | SOME (_, value) => SOME value
    end

  fun insert ({hint, ceiling, buckets, entries} : 'a table) term value =
    let
      val table = !buckets
      val size = Array.length table
      val index = hint size term
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

  fun clear ({buckets, entries, ...} : 'a table) =
    (Array.modify (fn _ => []) (!buckets); entries := 0)

  fun mark table term =
    case lookup table term of
      SOME () => false
    | NONE => (insert table term (); true)

  fun size ({entries, ...} : 'a table) = !entries
end
