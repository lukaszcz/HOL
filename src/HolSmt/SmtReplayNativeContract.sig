(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayNativeContract =
sig
  (* The actual finite caller contract, separate from metadata policy and
     cumulative Work credit. Capturing it does not admit a native term. *)
  type contract
  type limits =
    {semantic_limits:SmtReplayInvocationWork.limits,import_limit:int,
     type_work_limit:int}
  val capture : SmtReplayInvocationWork.portfolio -> limits -> contract
  val for_work : SmtReplayInvocationWork.portfolio -> contract -> limits
  val validate_for : SmtReplayInvocationWork.portfolio -> contract -> unit
end
