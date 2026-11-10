(* Persistent lexical-let DATA for the shared outbound dispatcher. *)
signature SmtLib_OutputSchedule =
sig
  type ('region, 'key) state

  (* The caller supplies pure comparisons and a fresh SMT identifier prefix
     disjoint from its other emitted names. Regions and keys are DATA:
     include the query, scoped node, ordered Bound-ID/name environment and
     fixed backend context wherever these affect expression meaning.
     Assertion roots have separate regions. Binder and LET bodies extend
     their lexical region; LET right-hand sides use the incoming region. *)
  val create : {compare_region : 'region * 'region -> order,
                compare_key : 'key * 'key -> order, prefix : string} ->
    ('region, 'key) state

  val find : ('region, 'key) state * 'region * 'key ->
    SmtLib_OutputFragments.doc option

  (* Look up before semantic work. A missing key appends one definition and
     returns its reference; an existing key retains the state and reference.
     Bind dependencies before their users. Counter, memo and definitions are
     immutable parts of the returned state: bundle it with the symbol map
     in the dispatch accumulator so speculative rollback drops all of them.
     Symbol counts used for legacy naming must still count symbols only. *)
  val bind : ('region, 'key) state * 'region * 'key *
    SmtLib_OutputFragments.doc ->
    ('region, 'key) state * SmtLib_OutputFragments.doc

  (* Wrap only definitions reachable from the body's structured references,
     oldest outermost, in nested single-binding SMT lets. Earlier definitions
     are visible to later right-hand sides. Unrelated definitions are omitted.
     Parent-region references stay free. Opaque text is never scanned.
     This retains fragments without rendering/flattening.
     The caller wraps at each lexical boundary; a cached reference by itself
     emits no declaration. Regions confer no proof or scope authority. *)
  val wrap : ('region, 'key) state * 'region *
    SmtLib_OutputFragments.doc -> SmtLib_OutputFragments.doc
end
