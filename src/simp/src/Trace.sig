signature Trace =
sig
  include Abbrev

    datatype action =
             LZ_TEXT             of unit -> string
           | TEXT                of string
           | REDUCE              of (string * term)
           | REWRITING           of (string * term * thm)
           | SIDECOND_ATTEMPT    of term
           | SIDECOND_SOLVED     of thm
           | SIDECOND_NOT_SOLVED of term
           | OPENING             of (term * thm)
           | PRODUCE             of (term * string * thm)
           | IGNORE              of (string * thm)
           | MORE_CONTEXT        of thm

   (* Every event reaches the hook's listeners, whatever its level *)
   val trace_hook  : (int * action) Listener.t

   (* The "simplifier.trace" setting: an event of level n is printed when
      n is at most the setting.  A tactic reads it from the context it is
      run in, with `trace_level_of`, and hands it down; nothing below a tactic
      should consult the ambient setting. *)
   val trace_flag     : HOLFlags.flag
   val trace_level_of : Context.t -> int
   (* SOME n is n; NONE is the ambient setting, for the context-free entry
      points (SIMP_CONV and friends called with a simpset nobody gave a
      level to) *)
   val resolve_level  : int option -> int

   (* trace_at v (n, a) reports event a of level n, printing it if n <= v *)
   val trace_at    : int -> int * action -> unit
   (* trace_at the ambient setting: only for code that has no level to
      hand, which is to say not code run by a tactic *)
   val trace       : int * action -> unit
   val tty_trace   : action -> unit

end
