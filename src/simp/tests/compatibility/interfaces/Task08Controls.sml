(* Executable tracked-control boundary, using the real paired matcher.
   This is not a replacement simpset or a source-identity implementation. *)
structure Task08Controls :>
sig
  type entry
  val prepare : string * Thm.thm -> int option -> entry
  val projections : entry ->
    {legacy : (Term.term list -> Term.term -> Thm.thm) ->
                Term.term list -> Abbrev.conv,
     configured :
       {solver : Term.term list -> Term.term -> Thm.thm,
        stack : Term.term list, cond_depth : int option,
        term_ord : Term.term * Term.term -> order} -> Abbrev.conv}
  val same_control : entry * entry -> bool
  val remaining : entry -> int option
  val filter_preserving : (entry -> bool) -> entry list -> entry list
  val reset_prepared : entry list -> entry list
  val with_private_allowances : entry list -> ('a -> 'b) -> 'a -> 'b
end =
struct
  open Abbrev BoundedRewrites
  type config =
    {solver : term list -> term -> thm, stack : term list,
     cond_depth : int option, term_ord : term * term -> order}
  type runners =
    {legacy : (term list -> term -> thm) -> term list -> conv,
     configured : config -> conv}
  datatype entry = Entry of
    {control : control, declared : int option, runners : runners}
  fun prepare nth declared =
    let
      val control = case declared of NONE => UNBOUNDED
        | SOME n => if n < 0 then raise Fail "negative allowance"
                    else BOUNDED (ref n)
      val runners = Cond_rewr.COND_REWR_CONVS nth (Option.isSome declared)
    in Entry {control=control,declared=declared,runners=runners} end
  fun run UNBOUNDED conv tm = conv tm
    | run (BOUNDED r) conv tm =
      if !r = 0 then raise Fail "exhausted"
      else conv tm before r := !r - 1
  fun projections (Entry {control,runners,...}) =
    {legacy=fn solver => fn stack =>
       run control (#legacy runners solver stack),
     configured=fn cfg => run control (#configured runners cfg)}
  fun same_control (Entry {control=BOUNDED a,...},
                    Entry {control=BOUNDED b,...}) = a = b
    | same_control _ = false
  fun remaining (Entry {control=BOUNDED r,...}) = SOME (!r)
    | remaining _ = NONE
  val filter_preserving = List.filter
  (* Prepared events retain their matchers, but reset their declared quotas.
     One old ref maps to one new ref, even across conjunct/view aliases. *)
  fun reset_prepared entries =
    let
      val bindings = ref ([] : (int ref * int ref) list)
      fun rebind (r,n) =
        case List.find (fn (old,_) => old = r) (!bindings) of
            SOME (_,fresh) => fresh
          | NONE => let val fresh = ref n
                    in bindings := (r,fresh) :: !bindings; fresh end
      fun reset (Entry {control=BOUNDED r,declared=SOME n,runners}) =
          Entry {control=BOUNDED (rebind (r,n)),
                 declared=SOME n,runners=runners}
        | reset e = e
    in map reset entries end
  fun with_private_allowances entries f x =
    let
      fun collect (Entry {control=BOUNDED r,declared=SOME n,...},acc) =
          if List.exists (fn (s,_,_) => s = r) acc then acc
          else (r,!r,n) :: acc
        | collect (_,acc) = acc
      val refs = List.foldl collect [] entries
      fun restore () = List.app (fn (r,old,_) => r := old) refs
      val _ = List.app (fn (r,_,declared) => r := declared) refs
      val result = f x handle e => (restore (); raise e)
    in restore (); result end
end
