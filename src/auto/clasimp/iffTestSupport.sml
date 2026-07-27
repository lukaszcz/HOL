structure iffTestSupport =
struct

open HolKernel

(* Scripts name their own scenario rather than each shadowing [fail]. *)
fun failer scenario message = raise Fail (scenario ^ ": " ^ message)

fun fail message = failer "iff theory test" message

fun fetch_persistent name =
  case String.fields (equal #"$") name of
      [thy, theorem] => DB.fetch thy theorem
    | _ => raise Fail ("malformed persistent theorem name: " ^ name)

fun rewrite_changes name ss =
  let
    val rewrite = Drule.SPEC_ALL (fetch_persistent name)
    val (_, final) = boolSyntax.strip_imp_only (concl rewrite)
    val source =
      if boolSyntax.is_eq final then fst (boolSyntax.dest_eq final)
      else if boolSyntax.is_neg final then boolSyntax.dest_neg final
      else final
    val result = Conv.QCONV (simpLib.SIMP_CONV ss []) source
  in
    not (aconv (snd (boolSyntax.dest_eq (concl result))) source)
  end

fun has_iff_rewrite name =
  rewrite_changes name (BasicProvers.srw_ss ()) andalso
  rewrite_changes name (clasimpLib.clasimp_ss ())

fun has_rule name =
  List.exists
    (fn (_, (name', _)) => name = name')
    (clasetLib.rules_of (clasetLib.the_claset ()))

fun has_named_rule name theorem =
  List.exists
    (fn (_, (name', theorem')) =>
      name = name' andalso aconv (concl theorem) (concl theorem'))
    (clasetLib.rules_of (clasetLib.the_claset ()))

fun has_iff_rules name =
  let val stem = name ^ ".__clasimp_iff"
  in has_rule (stem ^ "_intro") andalso has_rule (stem ^ "_dest")
  end

(* How many fragments of [ss] carry one of the named iff rewrites.  Counting
   by fragment name would not do: ssfrag_names_of de-duplicates, and a
   theory's simp declarations already contribute a fragment of the same
   name as the iff batch. *)
fun iff_fragment_count names ss =
  let
    val wanted =
      map (concl o Drule.SPEC_ALL o fetch_persistent) names
    fun carries fragment =
      List.exists
        (fn rewrite => List.exists (aconv (concl rewrite)) wanted)
        (simpLib.frag_rewrites fragment)
  in
    length (List.filter carries (simpLib.ssfrags_of ss))
  end

fun rewrites_to source target =
  let
    fun changes ss =
      let
        val result = Conv.QCONV (simpLib.SIMP_CONV ss []) source
      in
        aconv (snd (boolSyntax.dest_eq (concl result))) target
      end
  in
    changes (BasicProvers.srw_ss ()) andalso
    changes (clasimpLib.clasimp_ss ())
  end

end
