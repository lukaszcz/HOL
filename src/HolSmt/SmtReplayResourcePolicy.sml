(* Dependency-free policy algebra only. No ledger, ownership or default. *)
structure SmtReplayResourcePolicy :> SmtReplayResourcePolicy =
struct
  datatype limit = Uncapped | AtMost of IntInf.int
  type semantic_policy =
    {input_limit : limit, output_limit : limit, template_limit : limit}
  type recipe_policy =
    {template_limit : limit, index_limit : limit,
     operand_limit : limit, token_limit : limit}
  type graph_policy =
    {import_limit : limit, literal_limit : limit, binder_limit : limit,
     recipe_limits : recipe_policy}

  fun from_int n = AtMost (IntInf.fromInt n)
  fun semantic_from_ints {input_limit, output_limit, template_limit} =
    {input_limit = from_int input_limit,
     output_limit = from_int output_limit,
     template_limit = from_int template_limit}
  fun recipe_from_ints
      {template_limit, index_limit, operand_limit, token_limit} =
    {template_limit = from_int template_limit,
     index_limit = from_int index_limit,
     operand_limit = from_int operand_limit,
     token_limit = from_int token_limit}
  fun graph_from_ints
      {import_limit, literal_limit, binder_limit, recipe_limits} =
    {import_limit = from_int import_limit,
     literal_limit = from_int literal_limit,
     binder_limit = from_int binder_limit,
     recipe_limits = recipe_from_ints recipe_limits}

  fun positive Uncapped = true
    | positive (AtMost n) = n > 0
  fun allows Uncapped amount = amount >= 0
    | allows (AtMost cap) amount = amount >= 0 andalso amount <= cap
  fun remaining Uncapped charged =
        if charged >= 0 then Uncapped else raise Domain
    | remaining (AtMost cap) charged =
        if charged >= 0 andalso charged <= cap then AtMost (cap - charged)
        else raise Domain

  fun nonnegative (a : IntInf.int, b : IntInf.int) =
    if a >= 0 andalso b >= 0 then () else raise Domain
  fun add_up_to Uncapped pair = (nonnegative pair; #1 pair + #2 pair)
    | add_up_to (AtMost cap) (a, b) =
        (nonnegative (a, b);
         if cap < 0 then raise Domain
         else if a > cap orelse b > cap - a then cap + 1 else a + b)
  fun multiply_up_to Uncapped pair =
        (nonnegative pair; #1 pair * #2 pair)
    | multiply_up_to (AtMost cap) (a, b) =
        (nonnegative (a, b);
         if cap < 0 then raise Domain
         else if a = 0 orelse b = 0 then 0
         else if a > cap div b then cap + 1 else a * b)
end
