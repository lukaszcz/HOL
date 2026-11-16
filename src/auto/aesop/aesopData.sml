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

fun aesop_simp_rewrites () =
  #get_global_value aesop_simp_data ()

(* Start from the lifted srw_ss, NOT clasimp_ss: aesop leaves splitting
   to search.  Replacing rather than appending unsafe solvers is
   essential: a solver installed in the base must not precede aesop's
   choice during safe normalisation's side-condition traversal. *)
fun aesop_simpset ss rewrites =
  ss
  |> clasimpLib.weaken_cond_congruence
  |> simpExtLib.set_cond_depth clasimpLib.cond_depth
  |> (fn ss' => simpExtLib.++ (ss', simpExtLib.lift_ssfrag boolSimps.ETA_ss))
  |> simpExtLib.set_safe_solvers [clasimpLib.safe_solver]
  |> simpExtLib.set_unsafe_solvers [linarithLib.linarith_solver]
  |> (fn ss' => simpExtLib.++ (ss', simpExtLib.rewrites rewrites))

type cached_simpset =
  {base : simpExtLib.simpset, rewrites : Thm.thm list,
   simpset : simpExtLib.simpset}

fun derive_aesop_ss ss _ : cached_simpset =
  let
    val base = simpExtLib.lift_simpset ss
    val rewrites = aesop_simp_rewrites ()
  in {base = base, rewrites = rewrites,
      simpset = aesop_simpset base rewrites} end

(* Derived from srw_ss independently of clasimp's derivation. *)
val {get = get_cached_aesop_ss, get_of = _} =
  BasicProvers.make_simpset_derived_value
    "aesopData.aesop_ss" derive_aesop_ss
    {base = simpExtLib.empty_ss, rewrites = [],
     simpset = simpExtLib.empty_ss}

(* The derived value above moves only with srw_ss, so an aesop_simp
   addition alone is derived once here.  Both inputs are context-owned
   immutable values, compared by identity, which also handles
   Context.restore. *)
val latest_aesop_ss : cached_simpset option Context.Data.slot =
  Context.Data.new
    {name = "aesopData.tracked_cache", empty = NONE,
     pp = fn _ => "<aesop tracked cache>"}

fun derive_latest base rewrites =
  let val simpset = aesop_simpset base rewrites
  in
    Context.update
      (Context.Data.put latest_aesop_ss
        (SOME {base = base, rewrites = rewrites, simpset = simpset}));
    simpset
  end

fun aesop_ss () =
  let
    val cached = get_cached_aesop_ss ()
    val base = #base cached
    val rewrites = aesop_simp_rewrites ()
  in
    if Portable.pointer_eq (#rewrites cached, rewrites) then #simpset cached
    else
      case Context.Data.get latest_aesop_ss (Context.snapshot ()) of
          SOME {base = base', rewrites = rewrites', simpset} =>
            if Portable.pointer_eq (base, base') andalso
               Portable.pointer_eq (rewrites, rewrites')
            then simpset
            else derive_latest base rewrites
        | NONE => derive_latest base rewrites
  end

val _ = HOLFlags.create_trace ({group = "aesop", name = "trace"},
                               {initial = 0, max = 3})

end
