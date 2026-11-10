(* Resource-limit DATA for additive replay APIs. *)
signature SmtReplayResourcePolicy =
sig
  datatype limit = Uncapped | AtMost of IntInf.int
  type semantic_policy =
    {input_limit : limit, output_limit : limit, template_limit : limit}
  type recipe_policy =
    {template_limit : limit, index_limit : limit,
     operand_limit : limit, token_limit : limit}
  type graph_policy =
    {import_limit : limit, literal_limit : limit, binder_limit : limit,
     recipe_limits : recipe_policy}

  (* These adapters describe an existing finite request; they select no
     default and perform no new owner/Scope/epoch or admission operation. *)
  val from_int : int -> limit
  val semantic_from_ints :
    {input_limit : int, output_limit : int, template_limit : int} ->
    semantic_policy
  val recipe_from_ints :
    {template_limit : int, index_limit : int,
     operand_limit : int, token_limit : int} -> recipe_policy
  val graph_from_ints :
    {import_limit : int, literal_limit : int, binder_limit : int,
     recipe_limits :
       {template_limit : int, index_limit : int,
        operand_limit : int, token_limit : int}} -> graph_policy

  (* Entry validation is separate from remaining-budget arithmetic:
     AtMost 0 is valid remaining DATA, but not a positive entry allowance.
     Call sites retain their existing ERR operation/message/retirement. *)
  val positive : limit -> bool
  val allows : limit -> IntInf.int -> bool
  val remaining : limit -> IntInf.int -> limit

  (* Exact arithmetic for Uncapped; finite paths may stop at cap+1.
     This is a model arithmetic bound, not an implicit debit or scan fuel. *)
  val add_up_to : limit -> IntInf.int * IntInf.int -> IntInf.int
  val multiply_up_to : limit -> IntInf.int * IntInf.int -> IntInf.int
end
