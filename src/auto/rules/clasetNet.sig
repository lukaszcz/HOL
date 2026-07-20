signature clasetNet =
sig
  type term = Term.term
  type 'a net

  val empty : 'a net
  val insert : {pat : term, patvars : term HOLset.set} * 'a ->
               'a net -> 'a net
  val match : term -> 'a net -> 'a list
  val unify : {q : term, qvars : term HOLset.set} -> 'a net -> 'a list
  (* Measured lookup is a separate entry point so ordinary claset queries
     do not pay for a callback.  The callback may raise to interrupt the
     traversal; the net is persistent, so every checkpoint is safe. *)
  val unifyMeasured :
    (unit -> unit) ->
    {q : term, qvars : term HOLset.set} -> 'a net -> 'a list
  val vfilter : ('a -> bool) -> 'a net -> 'a net
  val listItems : 'a net -> 'a list
end
