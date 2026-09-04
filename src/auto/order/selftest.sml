open testutils
open orderLib

fun check (name, predicate) =
  (tprint name;
   if predicate () then OK () else die "failed")

(* None of these goals is a benchmark entry.  Each poses one shape the
   procedure has to read -- a chain longer than a single transitivity
   step, a named order that has to be taken apart, a distinction closed
   by antisymmetry, a negative literal turned round by totality, a
   strict primitive -- and the last two pin what it refuses. *)

fun proves tm = (ORDER_PROVE tm; true) handle Feedback.HOL_ERR _ => false

fun refuses tm = not (proves tm)

val _ =
  check
    ("a chain of weak steps closes on transitivity alone",
     fn () =>
       proves
         ``!R a b c d.
             relation$transitive R ==> R a b ==> R b c ==> R c d ==> R a d``)

val _ =
  check
    ("a named order is taken apart for its axioms",
     fn () =>
       proves
         ``!le a b c.
             relation$WeakLinearOrder le ==> le a b ==> le b c ==> le a c``)

val _ =
  check
    ("two chains meeting head to tail are identified by antisymmetry",
     fn () =>
       proves
         ``!le a b c.
             relation$WeakOrder le ==>
             le a b ==> le b c ==> le c a ==> (a = c)``)

val _ =
  check
    ("a refused weak step is read as a strict one under totality",
     fn () =>
       proves
         ``!le a b c.
             relation$WeakLinearOrder le ==>
             ~le a b ==> le a c ==> le c b ==> F``)

val _ =
  check
    ("an equation joins the chain it stands in",
     fn () =>
       proves
         ``!le a b c.
             relation$WeakOrder le ==> le a b ==> (b = c) ==> le a c``)

val _ =
  check
    ("a strict primitive chains as the strict part of its closure",
     fn () =>
       proves
         ``!lt a b c.
             relation$StrongLinearOrder lt ==>
             lt a b ==> lt b c ==> ~(c = a)``)

val _ =
  check
    ("a strict primitive chains in the spelling the goal uses",
     fn () =>
       proves
         ``!lt a b c.
             relation$StrongOrder lt ==> lt a b ==> lt b c ==> lt a c``)

val _ =
  check
    ("a step the chain does not reach is refused",
     fn () =>
       refuses
         ``!R a b c.
             relation$transitive R ==> R a b ==> R b c ==> R c a``)

val _ =
  check
    ("a relation with no order axiom is refused",
     fn () => refuses ``!R a b c. R a b ==> R b c ==> R a c``)

(* The tactic reads the goal's own assumptions, which is how it is
   reached from inside a search: the axioms and the facts arrive there
   and not as arguments. *)
val _ =
  let
    val relation_type =
      Type.--> (Type.alpha, Type.--> (Type.alpha, Type.bool))
    val le = Term.mk_var ("order_le", relation_type)
    val a = Term.mk_var ("order_a", Type.alpha)
    val b = Term.mk_var ("order_b", Type.alpha)
    val c = Term.mk_var ("order_c", Type.alpha)
    fun apply f x y = Term.mk_comb (Term.mk_comb (f, x), y)
    val goal =
      ([Term.mk_comb
          (Term.prim_mk_const {Thy = "relation", Name = "WeakLinearOrder"},
           le),
        apply le a b, apply le b c],
       apply le a c)
  in
    check
      ("ORDER_TAC takes the order and the facts from the assumptions",
       fn () =>
         let
           val (remaining, validation) = Tactical.VALID (ORDER_TAC []) goal
         in
           List.null remaining andalso
           Term.aconv (Thm.concl (validation [])) (Lib.snd goal)
         end)
  end

(* The decision procedure sees an atom the rewriting has left standing,
   which the tactic cannot: it is asked about the goal's subterms with
   the assumptions as its context. *)
val _ =
  check
    ("ORDER_ss decides an atom in a simplifier context",
     fn () =>
       let
         val ss = simpLib.++ (boolSimps.bool_ss, ORDER_ss)
         val goal =
           ``!le a b c.
               relation$WeakLinearOrder le ==>
               le a b /\ le b c ==> le a c``
       in
         List.null
           (Lib.fst (Tactical.VALID
                   (Tactical.THEN
                      (Tactical.REPEAT Tactic.STRIP_TAC,
                       simpLib.ASM_SIMP_TAC ss []))
                   ([], goal)))
       end)
