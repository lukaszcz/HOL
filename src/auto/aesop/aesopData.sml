structure aesopData :> aesopData =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "aesopData"

val aesop_simp_generation = Sref.new 0

fun apply_aesop_simp_delta delta rewrites =
  case delta of
      ThmSetData.ADD (_, theorem) => theorem :: rewrites
    | ThmSetData.REMOVE _ =>
        raise ERR "apply_aesop_simp_delta"
          "aesop_simp is an additive theorem set"

fun apply_aesop_simp_to_global delta rewrites =
  let
    val rewrites' = apply_aesop_simp_delta delta rewrites
    val _ = Sref.update aesop_simp_generation (fn generation =>
      generation + 1)
  in
    rewrites'
  end

val _ =
  if List.exists (equal "aesop_simp") (ThmSetData.all_set_types ()) orelse
     ThmAttribute.is_attribute "aesop_simp"
  then
    raise ERR "registration"
      "settype or attribute aesop_simp already exists"
  else
    ()

val aesop_simp_data =
  ThmSetData.export_with_ancestry
    {settype = "aesop_simp",
     delta_ops =
       {apply_to_global = apply_aesop_simp_to_global,
        thy_finaliser = NONE,
        uptodate_delta = K true,
        initial_value = [],
        apply_delta = apply_aesop_simp_delta}}

fun aesop_simp_rewrites () =
  #get_global_value aesop_simp_data ()

(* This is the safe side-condition solver used by clasimp.  Keeping the
   solver safe is essential for the normalisation phase: it may discharge
   only goals justified without witness instantiation or unsafe search. *)
val safe_solver =
  simpLib.mk_tactic_solver
    ("clasimp safe",
     Tactical.FIRST
       [Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC,
        Tactic.REFL_TAC,
        Tactic.ACCEPT_TAC boolTheory.TRUTH,
        Tactical.FIRST_ASSUM Tactic.CONTR_TAC])

type cached_simpset = {generation : int, simpset : simpLib.simpset}

fun derive_aesop_ss ss _ : cached_simpset =
  {generation = Sref.value aesop_simp_generation,
   simpset =
     ss
     |> simpLib.set_cond_depth 40
     |> simpLib.set_safe_solvers [safe_solver]
     |> (fn ss' =>
          simpLib.++ (ss', simpLib.rewrites (aesop_simp_rewrites ())))}

val {get = get_cached_aesop_ss, set = set_cached_aesop_ss} =
  BasicProvers.make_simpset_derived_value
    derive_aesop_ss
    {generation = ~1, simpset = simpLib.empty_ss}

fun aesop_ss () =
  let
    val cached = get_cached_aesop_ss ()
  in
    if #generation cached = Sref.value aesop_simp_generation then
      #simpset cached
    else
      let
        val fresh = derive_aesop_ss (BasicProvers.srw_ss ()) cached
        val _ = set_cached_aesop_ss fresh
      in
        #simpset fresh
      end
  end

val aesop_trace = ref 0
val _ = Feedback.register_trace ("aesop", aesop_trace, 3)

end
