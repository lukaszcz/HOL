(* ========================================================================= *)
(* FILE          : hhCache.sml                                               *)
(* DESCRIPTION   : Persistent HolyHammer prover-result cache                  *)
(* ========================================================================= *)

structure hhCache :> hhCache =
struct

type key_parts =
  {prover : string, version : string option, argv : string list,
   problem : string}

fun join a b = OS.Path.concat (a, b)

fun sha1_text text =
  let
    val bytes = Byte.stringToBytes text
    val length = Word8Vector.length bytes
    fun read (offset, requested) =
      let
        val count = Int.min (requested, length - offset)
        val chunk = Word8Vector.tabulate
          (count, fn index => Word8Vector.sub (bytes, offset + index))
      in
        (chunk, offset + count)
      end
  in
    SHA1.sha1String read 0
  end

fun frame text = Int.toString (String.size text) ^ ":" ^ text

fun normalized_argument problem content_hash argument =
  if argument = problem then content_hash
  else
    let
      val prefix = "-file:"
    in
      if String.isPrefix prefix argument andalso
         String.extract (argument, String.size prefix, NONE) = problem
      then prefix ^ content_hash
      else argument
    end

fun key_of ({prover, version, argv, problem} : key_parts) =
  let
    val content_hash = SHA1.sha1_file {filename = problem}
    val normalized = map (normalized_argument problem content_hash) argv
    val version_string = case version of NONE => "" | SOME text => text
    val material =
      String.concat
        (map frame
          (prover :: version_string :: Int.toString (length normalized) ::
           normalized @ [content_hash]))
  in
    sha1_text material
  end

fun szs_string hhProver.SzsTheorem = "Theorem"
  | szs_string hhProver.SzsCounterSat = "CounterSatisfiable"
  | szs_string hhProver.SzsSatisfiable = "Satisfiable"
  | szs_string hhProver.SzsGaveUp = "GaveUp"
  | szs_string hhProver.SzsTimeout = "Timeout"
  | szs_string hhProver.SzsResourceOut = "ResourceOut"
  | szs_string hhProver.SzsInappropriate = "Inappropriate"
  | szs_string (hhProver.SzsUnknown text) = "Unknown:" ^ text
  | szs_string (hhProver.RunFailure text) = "RunFailure:" ^ text

fun szs_of_string "Theorem" = hhProver.SzsTheorem
  | szs_of_string "CounterSatisfiable" = hhProver.SzsCounterSat
  | szs_of_string "Satisfiable" = hhProver.SzsSatisfiable
  | szs_of_string "GaveUp" = hhProver.SzsGaveUp
  | szs_of_string "Timeout" = hhProver.SzsTimeout
  | szs_of_string "ResourceOut" = hhProver.SzsResourceOut
  | szs_of_string "Inappropriate" = hhProver.SzsInappropriate
  | szs_of_string text =
      if String.isPrefix "Unknown:" text then
        hhProver.SzsUnknown (String.extract (text, 8, NONE))
      else if String.isPrefix "RunFailure:" text then
        hhProver.RunFailure (String.extract (text, 11, NONE))
      else raise Fail ("invalid cached SZS status " ^ text)

fun json_string_option NONE = JSON.NULL
  | json_string_option (SOME text) = JSON.STRING text

fun json_string_list_option NONE = JSON.NULL
  | json_string_list_option (SOME values) =
      JSON.ARRAY (map JSON.STRING values)

fun result_json ({szs, used_axioms, time, version, ...}
                 : hhProver.run_result) =
  JSON.OBJECT
    [("szs", JSON.STRING (szs_string szs)),
     ("used_axioms", json_string_list_option used_axioms),
     ("time", JSON.FLOAT time),
     ("version", json_string_option version)]

fun field name value = JSONUtil.lookupField value name

fun optional decoder JSON.NULL = NONE
  | optional decoder value = SOME (decoder value)

fun result_of_json value : hhProver.run_result =
  {szs = szs_of_string (JSONUtil.asString (field "szs" value)),
   used_axioms =
     optional (JSONUtil.arrayMap JSONUtil.asString)
       (field "used_axioms" value),
   time = JSONUtil.asNumber (field "time" value),
   version = optional JSONUtil.asString (field "version" value),
   output_file = ""}

fun cache_path (options : hhConfig.hh_options) parts =
  join (#cache_dir options) (key_of parts)

fun remove path = OS.FileSys.remove path handle OS.SysErr _ => ()

fun read_result path = result_of_json (JSONParser.parseFile path)

val temp_counter = Portable.make_counter {init = 0, inc = 1}

fun temp_path path =
  path ^ "." ^ Portable.unique_tmp_suffix () ^ "." ^
  Int.toString (temp_counter ()) ^ ".tmp"

fun commit {temporary, final} =
  OS.FileSys.rename {old = temporary, new = final}
  handle OS.SysErr _ =>
    (remove final; OS.FileSys.rename {old = temporary, new = final})

fun write_result path result =
  let
    val temporary = temp_path path
    val output = TextIO.openOut temporary
    fun abort exn =
      ((TextIO.closeOut output handle _ => ()); remove temporary;
       raise exn)
    val _ =
      (JSONPrinter.print (output, result_json result);
       TextIO.closeOut output)
      handle exn => abort exn
  in
    commit {temporary = temporary, final = path}
    handle exn => (remove temporary; raise exn)
  end

fun lookup (options : hhConfig.hh_options) parts =
  if not (#cache options) then NONE
  else
    (let
       val path = cache_path options parts
     in
       if not (OS.FileSys.access (path, [OS.FileSys.A_READ])) then NONE
       else
         ((let
             val result = read_result path
             val _ = OS.FileSys.setTime (path, NONE) handle OS.SysErr _ => ()
           in
             SOME result
           end)
          handle Interrupt => raise Interrupt
               | _ => (remove path; NONE))
     end
     handle Interrupt => raise Interrupt
          | _ => NONE)

fun store (options : hhConfig.hh_options) parts result =
  if not (#cache options) then ()
  else
    ((hhConfig.ensure_dir (#cache_dir options);
      write_result (cache_path options parts) result)
     handle Interrupt => raise Interrupt
          | _ => ())

fun is_hex character =
  Char.isDigit character orelse
  (#"a" <= character andalso character <= #"f")

fun is_entry_name name =
  String.size name = 40 andalso List.all is_hex (String.explode name)

fun cache_entries directory =
  let
    fun entry name =
      if not (is_entry_name name) then NONE
      else
        let val path = join directory name in
          if hhConfig.is_dir path then NONE
          else SOME (OS.FileSys.modTime path, name, path)
        end
        handle OS.SysErr _ => NONE
  in
    List.mapPartial entry (hhConfig.directory_names directory)
  end

fun entry_before (time1, name1, _) (time2, name2, _) =
  case Time.compare (time1, time2) of
      LESS => true
    | GREATER => false
    | EQUAL => String.compare (name1, name2) <> GREATER

fun ninety_percent maximum =
  if maximum <= 0 then 0
  else (maximum div 10) * 9 + ((maximum mod 10) * 9) div 10

fun prune (options : hhConfig.hh_options) =
  if not (#cache options) then ()
  else
    ((let
        val entries = cache_entries (#cache_dir options)
        val maximum = #cache_max_entries options
      in
        if length entries <= maximum then ()
        else
          let
            val target = ninety_percent maximum
            val oldest = aiLib.first_n (length entries - target)
              (Portable.sort entry_before entries)
          in
            List.app (remove o #3) oldest
          end
      end)
     handle Interrupt => raise Interrupt
          | _ => ())

end
