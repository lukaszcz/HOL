structure SmtLib_OutputSchedule :> SmtLib_OutputSchedule =
struct
  structure F = SmtLib_OutputFragments

  type 'key region_data =
    {references : ('key, F.doc) Redblackmap.dict,
     definitions : (string * F.doc) list}

  datatype ('region, 'key) state = State of
    {regions : ('region, 'key region_data) Redblackmap.dict,
     compare_key : 'key * 'key -> order, prefix : string, next : IntInf.int}

  fun create {compare_region, compare_key, prefix} =
    State {regions = Redblackmap.mkDict compare_region,
           compare_key = compare_key, prefix = prefix, next = 0}

  fun find (State {regions, ...}, region, key) =
    case Redblackmap.peek (regions, region) of
      NONE => NONE
    | SOME {references, ...} => Redblackmap.peek (references, key)

  fun bind (state as State {regions, compare_key, prefix, next},
      region, key, expression) =
    case find (state, region, key) of
      SOME reference => (state, reference)
    | NONE =>
        let
          val {references, definitions} =
            case Redblackmap.peek (regions, region) of
              SOME data => data
            | NONE => {references = Redblackmap.mkDict compare_key,
                       definitions = []}
          val name = prefix ^ IntInf.toString next
          val reference = F.reference name
          val data =
            {references = Redblackmap.insert (references, key, reference),
             definitions = (name, expression) :: definitions}
          val updated = State
            {regions = Redblackmap.insert (regions, region, data),
             compare_key = compare_key, prefix = prefix, next = next + 1}
        in
          (updated, reference)
        end

  fun wrap (State {regions, ...}, region, body) =
    case Redblackmap.peek (regions, region) of
      NONE => body
    | SOME {definitions, ...} =>
        List.foldl
          (fn ((name, expression), inner) =>
            if F.mentions_reference (inner,name) then
              F.let_binding (name,expression,inner)
            else inner)
          body definitions
end
