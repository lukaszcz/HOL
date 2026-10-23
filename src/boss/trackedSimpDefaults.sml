(* Explicit tracked-default preparation. Ordinary BasicProvers owns its own
   declarations, update log and state; this module neither observes nor
   translates them. Callers supply typed steps before binding sources. *)
structure trackedSimpDefaults :> trackedSimpDefaults =
struct

infix ++ -*
val op ++ = simpExtLib.++
val op -* = simpExtLib.-*

val ERR = Feedback.mk_HOL_ERR "trackedSimpDefaults"

datatype delta = Add of KernelSig.kernelname * Thm.thm | Remove of string
datatype step = TheoryBatch of string * delta list
              | LocalDelta of delta
              | Fragment of simpExtLib.ssfrag
              | TypeInfo of TypeBasePure.tyinfo
              | Update of (simpExtLib.simpset -> simpExtLib.simpset)
type recipe = {seed : unit -> simpExtLib.simpset, steps : step list}
datatype provider = Prepared of simpExtLib.simpset

(* Install from ingredients, rather than copying a compiled bool_ss. This
   also makes each call a fresh installation event for every seed fragment. *)
fun initial_seed () =
    simpExtLib.empty_ss ++ pureSimpsExt.PURE_ss
                       ++ boolSimpsExt.BOOL_ss
                       ++ boolSimpsExt.NOT_ss
                       ++ boolSimpsExt.CONG_ss
                       ++ boolSimpsExt.UNWIND_ss
                       ++ combinSimpsExt.COMBIN_ss
                       ++ boolSimpsExt.NORMEQ_ss
                       ++ boolSimpsExt.ABBREV_ss
                       ++ boolSimpsExt.LABEL_CONG_ss
                       ++ boolSimpsExt.HIDE_ss

fun initial_recipe steps : recipe = {seed = initial_seed, steps = steps}

fun typebase_steps tyb = List.map TypeInfo (TypeBasePure.listItems tyb)

fun apply_delta (Add nth, ss) =
    ss ++ simpExtLib.add_named_rwt nth simpExtLib.empty_ssfrag
  | apply_delta (Remove name, ss) = ss -* [name]

fun apply_batch (thy, deltas) ss =
    let
      (* Partition in declaration order. As in BasicProvers.finaliser,
         reverse only the additions, not the removals. Even an empty batch
         installs its named fragment. *)
      fun partition (Add nth, (adds, rms)) = (nth :: adds, rms)
        | partition (Remove name, (adds, rms)) = (adds, name :: rms)
      val (adds, rms) = List.foldr partition ([], []) deltas
      val frag = simpExtLib.named_rewrites_with_names thy (List.rev adds)
    in
      List.foldl (fn (name, ss) => ss -* [name]) (ss ++ frag) rms
    end

fun apply_step (TheoryBatch batch, ss) = apply_batch batch ss
  | apply_step (LocalDelta d, ss) = apply_delta (d, ss)
  | apply_step (Fragment frag, ss) = ss ++ frag
  | apply_step (TypeInfo tyi, ss) =
      ((ss ++ simpExtLib.tyi_to_ssdata tyi) handle Feedback.HOL_ERR _ => ss)
  | apply_step (Update f, ss) = f ss

fun build ({seed, steps} : recipe) =
    Prepared (List.foldl apply_step (seed ()) steps)

fun value (Prepared ss) = ss
fun map f (p as Prepared ss) = Prepared (f ss) handle Conv.UNCHANGED => p

val provider_slot : provider option Context.Data.slot =
    Context.Data.new {name = "trackedSimpDefaults.provider", empty = NONE,
                      pp = fn _ => "<trackedSimpDefaults.provider>"}

fun install provider = Context.Data.put provider_slot (SOME provider)
val get_of = Context.Data.get provider_slot

fun require_provider origin NONE =
      raise ERR origin
        "Unprepared tracked default provider; explicitly build and install one"
  | require_provider _ (SOME provider) = provider

fun map_of f =
    Context.Data.update provider_slot
      (fn p => SOME (map f (require_provider "map_of" p)))

fun with_updates f g x =
    let
      val provider =
          require_provider "with_updates" (get_of (Context.snapshot ()))
      val updated = map f provider
    in
      Context.Data.with_slot_value provider_slot (SOME updated) g x
    end

end
