structure Trace :> Trace =
struct
open Feedback boolSyntax Rsyntax Abbrev;

val print_term = Lib.say o Parse.term_to_string
val print_thm = Parse.print_thm
val concl = Thm.concl
val say = Lib.say

   (* ---------------------------------------------------------------------
    * Tracing utilities
    * ---------------------------------------------------------------------*)

    datatype action =
             LZ_TEXT of unit -> string
           | TEXT of string
           | REDUCE of (string * Term.term)
           | REWRITING of (string * Term.term * Thm.thm)
           | SIDECOND_ATTEMPT of Term.term
           | SIDECOND_SOLVED of Thm.thm
           | SIDECOND_NOT_SOLVED of Term.term
           | OPENING of (Term.term * Thm.thm)
           | PRODUCE of (Term.term * string * Thm.thm)
           | IGNORE of (string * Thm.thm)
           | MORE_CONTEXT of Thm.thm;

   val trace_hook : (int * action) Listener.t = Listener.new_listener()

val {flag = trace_flag, get = ambient_level, ...} = HOLFlags.create_trace(
      {group = "simplifier", name = "trace"},
      {max = 7, initial = 0}
    );

fun trace_level_of ctxt = HOLFlags.get_flagC ctxt trace_flag
fun resolve_level (SOME n) = n
  | resolve_level NONE = ambient_level ()

fun tty_trace (LZ_TEXT fs) = (say "  "; say (fs ()); say "\n")
  | tty_trace (TEXT s) = (say "  "; say s; say "\n")
  | tty_trace (REDUCE (s,tm)) = (say "  "; say s; say " "; print_term tm; say "\n")
  | tty_trace (REWRITING (nm,tm,thm)) =
    (say "  rewriting "; print_term tm; say (" with [" ^ nm ^ "]");
     print_thm thm; say "\n")
  | tty_trace (SIDECOND_ATTEMPT tm) =
    (say "  trying to solve: "; print_term tm; say "\n")
  | tty_trace (SIDECOND_SOLVED thm) =
    (say "  solved! "; print_thm thm; say "\n")
  | tty_trace (SIDECOND_NOT_SOLVED tm) =
    (say "  couldn't solve: "; print_term tm; say "\n")
  | tty_trace (OPENING (tm,thm)) =
    (say "  "; print_term tm; say " matches congruence rule "; print_thm thm; say "\n")
  | tty_trace (PRODUCE (tm,s,thm)) =
    (say "  "; print_term tm; say " via "; say s; say " simplifies to: ";
     print_term (rhs (concl thm)) handle HOL_ERR _ => print_thm thm; say "\n")
  | tty_trace (IGNORE (s,thm)) =
    (say "  Ignoring "; say s; say " rewrite\n     "; print_thm thm; say "\n")
  | tty_trace (MORE_CONTEXT thm) =
    (say "  more context: "; print_thm thm; say "\n");

(* hol_clock is sometimes a small amount of time in the future under Poly/ML,
   presumably a consequence of being stored in a heap.
*)
fun fudge t = Time.+(t, Time.fromSeconds 10)

fun print_event a =
    (say "[";
     say ((Arbnum.toString o #usec o Portable.dest_time o fudge)
            (#usr (Timer.checkCPUTimer Globals.hol_clock)));
     say "]: ";
     tty_trace a)

(* Printing is done here rather than by a listener on the hook, because a
   listener sees the event and not the level it is to be judged against.
   What escapes the printer is dropped, as call_listener drops what
   escapes a listener. *)
fun trace_at verbosity (x as (n, a)) =
    ((if n <= verbosity then ignore (Exn.capture print_event a) else ());
     ignore (Listener.call_listener trace_hook x))

fun trace x = trace_at (ambient_level ()) x

end (* struct *)
