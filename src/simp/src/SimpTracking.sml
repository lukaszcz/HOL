structure SimpTracking :> SimpTracking =
struct
open HolKernel

(* Which rewrites fired, for a human watching a simplification.  This is
   an interactive convenience, so it is exposed as one bracketing
   function that hands back the list with the result rather than as a
   flag to set and a list to read afterwards.

   The accumulator is per-thread and doubles as the switch: an untouched
   thread, or NONE, means nobody is watching and nothing is recorded.
   Nothing outside `with_tracking` can see it, so there is no flag for a
   caller to leave set and no shared list for a second proof to append
   to.  Nested tracking reports only the inner extent. *)
local
  val slot : thm list option ThreadLocal.t = ThreadLocal.new ()
  fun peek () = case ThreadLocal.get slot of SOME s => s | NONE => NONE
in
  fun note_rewrite th =
      case peek () of
          NONE => ()
        | SOME l => ThreadLocal.set (slot, SOME (th :: l))
  fun with_tracking f x =
      let
        val saved = peek ()
        val () = ThreadLocal.set (slot, SOME [])
        fun stop () =
            let val got = peek ()
            in
              ThreadLocal.set (slot, saved);
              case got of NONE => [] | SOME l => List.rev l
            end
        val res = f x handle e => (ignore (stop ()); raise e)
      in
        (res, stop ())
      end
end
end
