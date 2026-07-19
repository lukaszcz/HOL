(* ========================================================================= *)
(* FILE          : hhSlice.sml                                               *)
(* DESCRIPTION   : HolyHammer slice schedule construction                    *)
(* ========================================================================= *)

structure hhSlice :> hhSlice =
struct

val rotation =
  ["vampire", "e", "zipperposition", "vampire", "e", "vampire",
   "zipperposition", "vampire", "e", "vampire", "vampire"]

fun member item = List.exists (fn other => item = other)

fun distinct items =
  let
    fun collect _ [] = []
      | collect seen (item :: rest) =
          if member item seen then collect seen rest
          else item :: collect (item :: seen) rest
  in
    collect [] items
  end

fun take 0 _ = []
  | take _ [] = []
  | take n (item :: rest) = item :: take (n - 1) rest

fun round_robin count items =
  let
    fun loop 0 _ result = List.rev result
      | loop _ [] result = List.rev result
      | loop n (item :: rest) result =
          loop (n - 1) (if null rest then items else rest) (item :: result)
  in
    loop count items []
  end

fun schedule_of_provers requested count =
  if count <= 0 then []
  else
    let
      val requested' = distinct requested
      val initial = List.filter (fn name => member name requested') rotation
      val initial_count = length initial
    in
      if count <= initial_count then take count initial
      else initial @ round_robin (count - initial_count) requested'
    end

fun cap NONE nfacts = nfacts
  | cap (SOME maximum) nfacts = Int.min (maximum, nfacts)

fun adjust_slice (options : hhConfig.hh_options)
    (slice : hhProver.slice) : hhProver.slice =
  {prover = #prover slice, format = #format slice,
   type_enc = #type_enc slice, lam_trans = #lam_trans slice,
   nfacts = cap (#max_facts options) (#nfacts slice),
   filter = #filter options, extra_opts = #extra_opts slice,
   slice_size = #slice_size slice}

fun same_slice (left : hhProver.slice) (right : hhProver.slice) =
  #prover left = #prover right andalso #format left = #format right andalso
  #type_enc left = #type_enc right andalso
  #lam_trans left = #lam_trans right andalso
  #nfacts left = #nfacts right andalso #filter left = #filter right andalso
  #extra_opts left = #extra_opts right andalso
  #slice_size left = #slice_size right

fun mk_schedule (options : hhConfig.hh_options) =
  let
    val requested = distinct (#provers options)
    val configs = List.mapPartial hhProver.lookup requested
    val tables = map (fn config => (#name config, config, #slices config ()))
      configs
    val names = schedule_of_provers requested (#slices options)

    fun consume _ [] = NONE
      | consume name ((entry as (other, config, slices)) :: rest) =
          if name = other then
            (case slices of
                 [] => NONE
               | slice :: tail =>
                   SOME (config, slice, (other, config, tail) :: rest))
          else
            case consume name rest of
                NONE => NONE
              | SOME (config', slice, rest') =>
                  SOME (config', slice, entry :: rest')

    fun walk _ _ [] result = List.rev result
      | walk tables seen (name :: rest) result =
          case consume name tables of
              NONE => walk tables seen rest result
            | SOME (config, slice, tables') =>
                let val adjusted = adjust_slice options slice in
                  if List.exists (same_slice adjusted) seen then
                    walk tables' seen rest result
                  else
                    walk tables' (adjusted :: seen) rest
                      ((config, adjusted) :: result)
                end
  in
    walk tables [] names []
  end

fun slice_budget schedule_len (options : hhConfig.hh_options)
    (slice : hhProver.slice) =
  if schedule_len <= 0 orelse #cores options <= 0 then 0.0
  else
    let
      (* Deliberately use the actual schedule length.  Unlike Sledgehammer's
         requested-count formula, this does not starve short slice tables. *)
      val batches = (schedule_len + #cores options - 1) div #cores options
    in
      Real.fromInt (#slice_size slice) * Real.fromInt (#timeout options) /
      Real.fromInt batches
    end

end
