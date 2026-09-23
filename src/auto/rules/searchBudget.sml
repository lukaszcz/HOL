structure searchBudget :> searchBudget =
struct

open HolKernel

datatype kind = Candidate | Application | Normalization

type limits =
  {candidates : int option,
   applications : int option,
   normalization : int option}

type usage =
  {candidates : int,
   applications : int,
   normalization : int}

type budget =
  {limits : limits ref,
   candidates : int ref,
   applications : int ref,
   normalization : int ref}

exception LimitReached of kind * usage

val ERR = mk_HOL_ERR "searchBudget"

fun valid NONE = true
  | valid (SOME limit) = limit >= 0

fun create (limits as {candidates, applications, normalization}) =
  if List.all valid [candidates, applications, normalization] then
    {limits = ref limits, candidates = ref 0,
     applications = ref 0, normalization = ref 0}
  else
    raise ERR "create" "work limits must not be negative"

fun unbounded () =
  create
    {candidates = NONE, applications = NONE,
     normalization = NONE}

fun usage ({candidates, applications, normalization, ...} : budget) =
  {candidates = !candidates,
   applications = !applications,
   normalization = !normalization}

fun charge (budget as {limits, candidates, applications,
                      normalization} : budget) kind =
  let
    val (used, limit) =
      case kind of
          Candidate => (candidates, #candidates (!limits))
        | Application => (applications, #applications (!limits))
        | Normalization => (normalization, #normalization (!limits))
  in
    case limit of
        SOME maximum =>
          if !used >= maximum then
            raise LimitReached (kind, usage budget)
          else used := !used + 1
      | NONE => used := !used + 1
  end

fun extend ({limits, ...} : budget) kind extra =
  if extra < 0 then
    raise ERR "extend" "an additional allocation must not be negative"
  else
    let
      val {candidates, applications, normalization} = !limits
      fun grow NONE = NONE
        | grow (SOME maximum) =
            SOME (maximum + extra)
              handle Overflow =>
                raise ERR "extend" "work limit overflow"
    in
      limits :=
        (case kind of
             Candidate =>
               {candidates = grow candidates,
                applications = applications,
                normalization = normalization}
           | Application =>
               {candidates = candidates,
                applications = grow applications,
                normalization = normalization}
           | Normalization =>
               {candidates = candidates,
                applications = applications,
                normalization = grow normalization})
    end

end
