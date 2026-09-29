structure aesopData :> aesopData =
struct

open HolKernel

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

val aesop_simp_data =
  thmTable.register
    {settype = "aesop_simp", initial_value = [],
     apply_delta = apply_aesop_simp_delta,
     apply_to_global = apply_aesop_simp_to_global}

fun aesop_simp_rewrites () =
  #get_global_value aesop_simp_data ()

type cached_simpset = {generation : int, simpset : simpLib.simpset}

(* Keeping the final solver safe is essential for the normalisation phase:
   it may discharge only goals justified without witness instantiation or
   unsafe search.  clasimp's safe solver is exactly that stack, so it is
   shared rather than restated here.  The unsafe solvers are not shared:
   traverseconfig_for_ss hands them to every traversal whatever the safe
   solvers are, so one installed here runs inside the normalisation phase
   and has to be this module's choice rather than whatever clasimp's list
   happens to hold.  The list is set rather than appended to, so that a
   solver reaching this simpset through the shared srw_ss base -- an
   augment_srw_ss of a solver_ss fragment -- cannot run there ahead of the
   ones named here.  They remain available only to prove simplifier side
   conditions in safe mode.  The derivation itself is not shared either:
   clasimp_ss also carries split_ss, which the aesop simpset deliberately
   leaves to the search. *)
fun aesop_simpset ss rewrites =
  ss
  (* The conditional congruence is weakened here too; see
     clasimpLib.weaken_cond_congruence for why a recursive equation
     with a conditional right-hand side needs it.  The branch
     reasoning this simpset gives up is the branch reasoning it
     already leaves to the search. *)
  |> clasimpLib.weaken_cond_congruence
  |> simpLib.set_cond_depth clasimpLib.cond_depth
  (* Matched modulo eta, as Isabelle's higher-order patterns are; see
     clasimpLib.derive_clasimp_ss for why a rule and a goal otherwise
     miss each other over an eta step. *)
  |> (fn ss' => simpLib.++ (ss', boolSimps.ETA_ss))
  |> simpLib.set_safe_solvers [clasimpLib.safe_solver]
  |> simpLib.set_unsafe_solvers [linarithLib.linarith_solver]
  |> (fn ss' => simpLib.++ (ss', simpLib.rewrites rewrites))

fun derive_aesop_ss ss _ : cached_simpset =
  {generation = Sref.value aesop_simp_generation,
   simpset = aesop_simpset ss (aesop_simp_rewrites ())}

val {get = get_cached_aesop_ss, get_of = _} =
  BasicProvers.make_simpset_derived_value
    "aesopData.aesop_ss"
    derive_aesop_ss
    {generation = ~1, simpset = simpLib.empty_ss}

(* The derived value above moves only with srw_ss, so an aesop_simp
   addition alone is derived once here.  It is keyed on both inputs by
   identity: a context restore rewinds the rewrites but not the generation
   counter. *)
val latest_aesop_ss :
    {base : simpLib.simpset, rewrites : Thm.thm list,
     simpset : simpLib.simpset} option ref = ref NONE

fun derive_latest base rewrites =
  let val simpset = aesop_simpset base rewrites
  in
    latest_aesop_ss :=
      SOME {base = base, rewrites = rewrites, simpset = simpset};
    simpset
  end

fun aesop_ss () =
  let
    val cached = get_cached_aesop_ss ()
  in
    if #generation cached = Sref.value aesop_simp_generation then
      #simpset cached
    else
      let
        val base = BasicProvers.srw_ss ()
        val rewrites = aesop_simp_rewrites ()
      in
        case !latest_aesop_ss of
            SOME {base = base', rewrites = rewrites', simpset} =>
              if Portable.pointer_eq (base, base') andalso
                 Portable.pointer_eq (rewrites, rewrites')
              then simpset
              else derive_latest base rewrites
          | NONE => derive_latest base rewrites
      end
  end

val aesop_trace = ref 0
val _ = Feedback.register_trace ("aesop", aesop_trace, 3)

end
