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

end
