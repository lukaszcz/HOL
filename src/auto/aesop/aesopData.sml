structure aesopData :> aesopData =
struct

open HolKernel

val ERR = mk_HOL_ERR "aesopData"

fun apply_aesop_simp_delta delta rewrites =
  case delta of
      ThmSetData.ADD (_, theorem) => theorem :: rewrites
    | ThmSetData.REMOVE _ =>
        raise ERR "apply_aesop_simp_delta"
          "aesop_simp is an additive theorem set"

val aesop_simp_data =
  thmTable.register
    {settype = "aesop_simp", initial_value = [],
     apply_delta = apply_aesop_simp_delta,
     apply_to_global = apply_aesop_simp_delta}

fun aesop_simp_rewrites_of ctxt =
  #get_global_value_of aesop_simp_data ctxt

(* A simpset built here is built for nobody in particular -- the first
   proof to want it, as often as not -- so building it reads no
   simplifier.trace setting, and what is built reports at the setting of
   whoever runs it, as the srw_ss it comes from does. *)
fun quietly build ss =
  simpExtLib.unset_trace_level (build (simpExtLib.set_trace_level 0 ss))

(* Start from the lifted srw_ss, NOT clasimp_ss: aesop leaves splitting
   to search.  Replacing rather than appending unsafe solvers is
   essential: a solver installed in the base must not precede aesop's
   choice during safe normalisation's side-condition traversal. *)
fun aesop_base ss =
  simpExtLib.lift_simpset ss
  |> clasimpLib.weaken_cond_congruence
  |> simpExtLib.set_cond_depth clasimpLib.cond_depth
  |> (fn ss' => simpExtLib.++ (ss', simpExtLib.lift_ssfrag boolSimps.ETA_ss))
  |> simpExtLib.set_safe_solvers [clasimpLib.safe_solver]
  |> simpExtLib.set_unsafe_solvers [linarithLib.linarith_solver]

(* The part of the simpset that moves only with srw_ss, derived from it
   independently of clasimp's derivation, and so held, like srw_ss, by
   the context: restoring a context restores this exact simpset. *)
val {get = _, get_of = aesop_base_of} =
  BasicProvers.make_simpset_derived_value
    "aesopData.aesop_ss"
    (fn ss => fn _ =>
       simpExtLib.unset_trace_level
         (aesop_base (simpLib.set_trace_level 0 ss)))
    simpExtLib.empty_ss

(* The aesop_simp rewrites move without srw_ss, so they are added here,
   once for each state of the pair.  Both are immutable values a context
   owns, compared by identity. *)
val with_rewrites =
  linarithData.keyed_memo
    (fn (base, rewrites) => fn (base', rewrites') =>
       Portable.pointer_eq (base, base') andalso
       Portable.pointer_eq (rewrites, rewrites'))
    (fn (base, rewrites) =>
       quietly
         (fn ss => simpExtLib.++ (ss, simpExtLib.rewrites rewrites))
         base)

fun aesop_ss_of ctxt =
  let val base = aesop_base_of ctxt
  in
    case aesop_simp_rewrites_of ctxt of
        [] => base
      | rewrites => with_rewrites (base, rewrites)
  end

fun aesop_ss () = aesop_ss_of (Context.snapshot ())

val {flag = trace, ...} =
    HOLFlags.create_trace ({group = "aesop", name = "trace"},
                           {initial = 0, max = 3})

end
