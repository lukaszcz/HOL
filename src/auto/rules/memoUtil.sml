structure memoUtil :> memoUtil =
struct

(* A false key comparison costs a recomputation and nothing else, so the
   cache cell needs no more synchronization than the source it is read
   against. *)
fun keyed_memo same compute =
  let
    val cache = ref NONE
    fun recompute key =
      let
        val value = compute key
      in
        cache := SOME (key, value); value
      end
  in
    fn key =>
      case !cache of
          SOME (recorded, value) =>
            if same recorded key then value else recompute key
        | NONE => recompute key
  end

(* The cache is most-recent-first.  A hit is removed from it and put
   back in front. *)
fun bounded_memo n same compute =
  if n < 1 then compute
  else
    let
      val cache = ref (0, [])
      fun without_last (entry :: (rest as _ :: _)) =
            entry :: without_last rest
        | without_last _ = []
      fun extract _ [] = NONE
        | extract key ((entry as (recorded, _)) :: rest) =
            if same recorded key then SOME (entry, rest)
            else
              Option.map (fn (found, others) => (found, entry :: others))
                         (extract key rest)
      fun recompute key =
        let
          val value = compute key
          (* Computing may have made recursive calls to this memo. *)
          val (size, entries) = !cache
          val entry = (key, value)
        in
          cache :=
            (if size < n then (size + 1, entry :: entries)
             else (size, entry :: without_last entries));
          value
        end
    in
      fn key =>
        case !cache of
            state as (size, (first as (recorded, value)) :: rest) =>
              if same recorded key then (cache := state; value)
              else
                (case extract key rest of
                     SOME (entry as (_, value), others) =>
                       (cache := (size, entry :: first :: others); value)
                   | NONE => recompute key)
          | _ => recompute key
    end

end
