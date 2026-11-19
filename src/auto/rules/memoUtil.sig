(* Single-entry memos for derivations keyed on immutable values. *)
signature memoUtil =
sig
  (* keyed_memo same compute caches the value compute returned for the
     key it last saw, and reuses it for as long as same reports the key
     has not moved.  The equality is the caller's because not every
     source of a key is an equality type -- a derivation keyed on a
     table of theorems compares them by pointer.  A comparison that
     answers "moved" when it has not costs a recomputation and nothing
     else. *)
  val keyed_memo : ('a -> 'a -> bool) -> ('a -> 'b) -> 'a -> 'b
end
