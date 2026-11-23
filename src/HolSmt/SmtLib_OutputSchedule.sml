structure SmtLib_OutputSchedule :> SmtLib_OutputSchedule =
struct
  structure F = SmtLib_OutputFragments

  type definition = {name : string, expression : F.doc, index : IntInf.int}

  (* Each completed bucket indexes its newest definition. The suffix
     shares the descending list used by dense wraps. *)
  fun bucket (index : IntInf.int) = index div 32

  fun extend_index index (definitions:definition list) buckets =
    case definitions of
      [] => buckets
    | {index=last,...} :: _ =>
        let val previous = bucket last in
          if previous = bucket index then buckets
          else Redblackmap.insert (buckets,previous,definitions)
        end

  fun lookup_index index (definitions:definition list) buckets =
    let
      val key = bucket index
      fun seek ([]:definition list) = []
        | seek (suffix as {index=current,...} :: older) =
            if current > index then seek older
            else if current = index then suffix
            else []
    in
      case definitions of
        [] => []
      | {index=latest,...} :: _ =>
          if key = bucket latest then seek definitions
          else case Redblackmap.peek (buckets,key) of
            SOME suffix => seek suffix
          | NONE => []
    end

  type 'key region_data =
    {references : ('key, F.doc) Redblackmap.dict,
     definitions : definition list,
     buckets : (IntInf.int, definition list) Redblackmap.dict}

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
          val {references, definitions, buckets} =
            case Redblackmap.peek (regions, region) of
              SOME data => data
            | NONE => {references = Redblackmap.mkDict compare_key,
                       definitions = [],
                       buckets = Redblackmap.mkDict IntInf.compare}
          val name = prefix ^ IntInf.toString next
          val reference = F.reference name
          val data =
            {references = Redblackmap.insert (references, key, reference),
             definitions =
               {name=name,expression=expression,index=next} :: definitions,
             buckets = extend_index next definitions buckets}
          val updated = State
            {regions = Redblackmap.insert (regions, region, data),
             compare_key = compare_key, prefix = prefix, next = next + 1}
        in
          (updated, reference)
        end

  fun wrap (State {regions, prefix, ...}, region, body) =
    case Redblackmap.peek (regions, region) of
      NONE => body
    | SOME {definitions, buckets, ...} =>
        let
          (* Find the newest referenced definition in the unvisited suffix.
             A value may introduce references to earlier definitions or
             to names outside this suffix, which remain free. *)
          fun jump limit inner =
            let
              val prefix_size = String.size prefix
              val max_digits = String.size (IntInf.toString limit)
              fun choose (name,found as (best,_)) =
                if String.size name - prefix_size <= max_digits andalso
                    String.isPrefix prefix name then
                  case IntInf.fromString
                      (String.extract (name,prefix_size,NONE)) of
                    SOME index =>
                      if index > best andalso index <= limit then
                        (case lookup_index index definitions buckets of
                           entry as {name=stored,...}::_ =>
                             if stored=name then (index,entry) else found
                         | [] => found)
                      else found
                  | NONE => found
                else found
            in
              #2 (F.fold_references choose (~1,[]) inner)
            end
          (* Keep a linear pass for dense runs. After enough misses to
             justify looking up the current references, jump over the
             remaining unused definitions. *)
          fun scan [] _ inner = inner
            | scan ({name,expression,index} :: older) misses inner =
                if F.mentions_reference (inner,name) then
                  scan older 0 (F.let_binding (name,expression,inner))
                else if misses >= 8 andalso
                    misses >= F.reference_count inner then
                  scan (jump index inner) 0 inner
                else scan older (misses + 1) inner
        in
          if F.reference_count body = 0 then body else scan definitions 0 body
        end
end
