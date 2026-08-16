(* ========================================================================= *)
(* FILE          : hhSlice.sml                                               *)
(* DESCRIPTION   : HolyHammer slice schedule construction                    *)
(* ========================================================================= *)

structure hhSlice :> hhSlice =
struct

(* The first eight entries are the frozen Phase 1 gate anchors.  The final
   eight consume the Phase 2 table order in hhProver exactly. *)
val rotation =
  ["vampire", "e", "zipperposition", "vampire", "e", "vampire",
   "zipperposition", "vampire",
   "vampire", "e", "zipperposition", "e", "vampire", "e", "vampire",
   "zipperposition"]

val distinct = aiLib.mk_sameorder_set String.compare

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
      val initial = List.filter (fn name => Lib.mem name requested') rotation
      val initial_count = length initial
    in
      if count <= initial_count then aiLib.first_n count initial
      else initial @ round_robin (count - initial_count) requested'
    end

fun cap NONE nfacts = nfacts
  | cap (SOME maximum) nfacts = Int.min (maximum, nfacts)

fun overridden override value = if override = "" then value else override

fun validate_slice (config : hhProver.prover_config)
    (slice : hhProver.slice) =
  let
    val format = #format slice
    val type_enc = #type_enc slice
    val lam_trans = #lam_trans slice
    val _ = ignore (hhTypeEnc.adjust_type_enc
      (hhTypeEnc.format_of_string format) (hhTypeEnc.of_string type_enc))
    val _ =
      if List.exists (fn supported => supported = format) (#supported_formats config)
      then ()
      else raise Fail ("HolyHammer prover '" ^ #name config ^
        "' does not support format '" ^ format ^ "'")
    val legacy = format = "fof" andalso type_enc = ""
    val _ =
      if legacy andalso lam_trans = "" orelse
         not legacy andalso hhLamTrans.valid_mode lam_trans then ()
      else raise Fail ("invalid HolyHammer lambda translation '" ^ lam_trans ^
        "' for (" ^ format ^ ", " ^ type_enc ^ ")")
  in
    slice
  end

fun adjust_slice (options : hhConfig.hh_options)
    (slice : hhProver.slice) : hhProver.slice =
  {prover = #prover slice,
   format = overridden (#format options) (#format slice),
   type_enc = overridden (#type_enc options) (#type_enc slice),
   lam_trans = overridden (#lam_trans options) (#lam_trans slice),
   nfacts = cap (#max_facts options) (#nfacts slice),
   filter = #filter options, extra_opts = #extra_opts slice,
   slice_size = #slice_size slice}

val same_slice = hhProver.same_slice

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
                let
                  val adjusted = validate_slice config (adjust_slice options slice)
                in
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
