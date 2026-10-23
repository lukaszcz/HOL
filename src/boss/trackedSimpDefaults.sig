signature trackedSimpDefaults =
sig
  (* Declaration inputs, never ordinary compiled simpsets or update closures.
     Batches preserve BasicProvers's finaliser order: reversed additions in
     one named fragment, followed by removals in their supplied order. *)
  datatype delta = Add of KernelSig.kernelname * Thm.thm | Remove of string
  datatype step = TheoryBatch of string * delta list
                | LocalDelta of delta
                | Fragment of simpExtLib.ssfrag
                | TypeInfo of TypeBasePure.tyinfo
                | Update of (simpExtLib.simpset -> simpExtLib.simpset)
  type recipe = {seed : unit -> simpExtLib.simpset, steps : step list}
  type provider

  (* A fresh tracked construction of BasicProvers's initial default:
     PURE, BOOL, NOT, CONG, UNWIND, COMBIN, NORMEQ, ABBREV, LABEL_CONG, HIDE.
     No ordinary state, persistent declarations or ambient TypeBase is read. *)
  val initial_seed : unit -> simpExtLib.simpset
  val initial_recipe : step list -> recipe

  (* Ordered TypeInfo steps, for insertion at the caller's chosen point.
     Like BasicProvers's initial TypeBase fold, each TypeInfo ignores HOL_ERR
     from construction/installation; other exceptions propagate. *)
  val typebase_steps : TypeBasePure.typeBase -> step list

  (* Explicit preparation only. A supplied seed may deliberately share an
     existing tracked set's controls; build never resets that seed. *)
  val build : recipe -> provider
  val value : provider -> simpExtLib.simpset
  (* UNCHANGED is a no-op, as in BasicProvers's map/window operations. *)
  val map : (simpExtLib.simpset -> simpExtLib.simpset) -> provider -> provider

  (* The provider, including its installed source/control state, is stored
     together in one opt-in Context slot. Retrieval never constructs a set. *)
  val install : provider -> Context.t -> Context.t
  val get_of : Context.t -> provider option
  (* An absent provider raises HOL_ERR, with this module and operation as
     origin. There is no fallback to ordinary srw_ss or automatic mirror. *)
  val map_of : (simpExtLib.simpset -> simpExtLib.simpset) ->
               Context.t -> Context.t
  val with_updates : (simpExtLib.simpset -> simpExtLib.simpset) ->
                     ('a -> 'b) -> 'a -> 'b
end
