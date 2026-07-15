(* ========================================================================= *)
(* FILE          : hhConfig.sml                                              *)
(* DESCRIPTION   : HolyHammer configuration and executable discovery         *)
(* ========================================================================= *)

structure hhConfig :> hhConfig =
struct

fun join a b = OS.Path.concat (a, b)

fun is_dir path = OS.FileSys.isDir path handle OS.SysErr _ => false

fun readable path =
  OS.FileSys.access (path, [OS.FileSys.A_READ])
  handle OS.SysErr _ => false

fun executable path =
  OS.FileSys.access (path, [OS.FileSys.A_READ, OS.FileSys.A_EXEC]) andalso
  not (is_dir path)
  handle OS.SysErr _ => false

fun ensure_dir path =
  if is_dir path then ()
  else
    let
      val parent = OS.Path.dir path
      val _ =
        if parent = "" orelse parent = path then () else ensure_dir parent
    in
      OS.FileSys.mkDir path
      handle OS.SysErr _ =>
        if is_dir path then () else raise Fail ("cannot create " ^ path)
    end

(* HHCONFIG_TEST_ROOT is used only by the hermetic selftest. *)
fun test_root () = OS.Process.getEnv "HHCONFIG_TEST_ROOT"

fun home_dir () =
  case test_root () of
      SOME root => join root "home"
    | NONE =>
      (case OS.Process.getEnv "HOME" of
           SOME home => home
         | NONE => raise Fail "HOME is not set")

fun holdir () =
  case test_root () of
      SOME root => SOME (join root "holdir")
    | NONE => OS.Process.getEnv "HOLDIR"

fun state_dir () =
  let
    val dir =
      case OS.Process.getEnv "HOL4_HAMMER_DIR" of
          SOME path => path
        | NONE => join (join (home_dir ()) ".hol4") "hammer"
    val _ = ensure_dir dir
  in
    dir
  end

fun trim_left s =
  let
    fun loop i =
      if i < String.size s andalso Char.isSpace (String.sub (s, i)) then
        loop (i + 1)
      else i
    val i = loop 0
  in
    String.extract (s, i, NONE)
  end

fun trim_right s =
  let
    fun loop i =
      if i > 0 andalso Char.isSpace (String.sub (s, i - 1)) then
        loop (i - 1)
      else i
    val i = loop (String.size s)
  in
    String.substring (s, 0, i)
  end

fun trim s = trim_right (trim_left s)

fun before_comment s =
  let
    fun find i =
      if i = String.size s then i
      else if String.sub (s, i) = #"#" then i else find (i + 1)
    val i = find 0
  in
    String.substring (s, 0, i)
  end

fun split_assignment s =
  let
    fun find i =
      if i = String.size s then NONE
      else if String.sub (s, i) = #"=" then SOME i else find (i + 1)
  in
    case find 0 of
        NONE => NONE
      | SOME i =>
        let
          val key = trim (String.substring (s, 0, i))
          val value = trim (String.extract (s, i + 1, NONE))
        in
          if key = "" then NONE else SOME (key, value)
        end
  end

fun read_config path =
  if not (readable path) then []
  else
    let
      val input = TextIO.openIn path
      fun loop acc =
        case TextIO.inputLine input of
            NONE => List.rev acc
          | SOME line =>
            let
              val item = split_assignment (before_comment line)
            in
              loop (case item of NONE => acc | SOME x => x :: acc)
            end
      val result = loop []
      val _ = TextIO.closeIn input
    in
      result
    end

fun lookup key [] = NONE
  | lookup key ((key', value) :: rest) =
      if key = key' then SOME value else lookup key rest

fun member key entries = Option.isSome (lookup key entries)

fun first_hits entries =
  let
    fun loop seen [] = List.rev seen
      | loop seen ((key, value) :: rest) =
          if member key seen then loop seen rest
          else loop (seen @ [(key, value)]) rest
  in
    loop [] entries
  end

fun config_entries () =
  let
    val user = join (join (home_dir ()) ".hol4") "hammer/config"
    val system =
      case holdir () of
          NONE => []
        | SOME dir => read_config (join (join dir "etc") "hammer-config")
  in
    first_hits (read_config user @ system)
  end

val defaults = [("eval.dir", fn () => join (state_dir ()) "eval")]

fun default key =
  case List.find (fn (key', _) => key = key') defaults of
      NONE => NONE
    | SOME (_, value) => SOME (value ())

fun env_name key =
  "HOL4_HAMMER_" ^
  String.map (fn c =>
    if c = #"." then #"_" else Char.toUpper c) key

fun value_with_source key =
  case lookup key (config_entries ()) of
      SOME value => SOME (value, "config")
    | NONE =>
      (case OS.Process.getEnv (env_name key) of
           SOME value => SOME (value, "environment")
         | NONE =>
           (case default key of
                SOME value => SOME (value, "default")
              | NONE => NONE))

val queried = ref ([] : string list)

fun remember key =
  if List.exists (fn key' => key = key') (!queried) then ()
  else queried := !queried @ [key]

fun get key =
  let val _ = remember key
  in Option.map #1 (value_with_source key) end

fun get_int key =
  case get key of
      NONE => NONE
    | SOME value => Int.fromString (trim value)

fun get_bool key =
  let
    val lower = String.map Char.toLower
  in
    case Option.map lower (get key) of
        SOME "true" => SOME true
      | SOME "yes" => SOME true
      | SOME "on" => SOME true
      | SOME "1" => SOME true
      | SOME "false" => SOME false
      | SOME "no" => SOME false
      | SOME "off" => SOME false
      | SOME "0" => SOME false
      | _ => NONE
  end

fun get_path key =
  case get key of
      SOME "~" => SOME (home_dir ())
    | SOME value =>
      if String.isPrefix "~/" value then
        SOME (join (home_dir ())
                    (String.extract (value, 2, NONE)))
      else SOME value
    | NONE => NONE

fun unique [] = []
  | unique (x :: xs) =
      if List.exists (fn y => x = y) xs then unique xs else x :: unique xs

fun dump () =
  let
    val config_keys = map #1 (config_entries ())
    val default_keys = map #1 defaults
    val keys = unique (config_keys @ default_keys @ !queried)
    fun render key =
      case value_with_source key of
          NONE => NONE
        | SOME (value, source) => SOME (key, source ^ ": " ^ value)
  in
    List.mapPartial render keys
  end

fun uname key =
  case List.find (fn (key', _) => key = key') (Posix.ProcEnv.uname ()) of
      SOME (_, value) => value
    | NONE => ""

fun lower s = String.map Char.toLower s

fun platform () =
  let
    val machine = lower (uname "machine")
    val system = lower (uname "sysname")
    val arch =
      if machine = "x86_64" orelse machine = "amd64" then "x86_64"
      else if machine = "aarch64" orelse machine = "arm64" then "arm64"
      else machine
    val os =
      if system = "linux" then "linux"
      else if system = "darwin" then "darwin"
      else system
  in
    arch ^ "-" ^ os
  end

fun first_some f [] = NONE
  | first_some f (x :: xs) =
      case f x of NONE => first_some f xs | result => result

fun path_exec names =
  let
    fun direct name =
      if String.isSubstring "/" name then
        if executable name then SOME name else NONE
      else NONE
    fun in_dir dir name =
      let val path = join dir name
      in if executable path then SOME path else NONE end
    fun on_path name =
      case direct name of
          SOME path => SOME path
        | NONE =>
          (case OS.Process.getEnv "PATH" of
               NONE => NONE
             | SOME path =>
               first_some (fn dir => in_dir
                 (if dir = "" then "." else dir) name)
                 (String.fields (fn c => c = #":") path))
  in
    first_some on_path names
  end

fun all_digits s =
  String.size s > 0 andalso
  List.all Char.isDigit (String.explode s)

fun without_zeroes s =
  let
    fun first i =
      if i + 1 < String.size s andalso String.sub (s, i) = #"0" then
        first (i + 1)
      else i
  in
    String.extract (s, first 0, NONE)
  end

fun token_compare (left, right) =
  if all_digits left andalso all_digits right then
    let
      val left' = without_zeroes left
      val right' = without_zeroes right
    in
      case Int.compare (String.size left', String.size right') of
          EQUAL => String.compare (left', right')
        | order => order
    end
  else String.compare (left, right)

fun version_compare (left, right) =
  let
    val left_tokens = String.tokens (not o Char.isAlphaNum) left
    val right_tokens = String.tokens (not o Char.isAlphaNum) right
    fun compare [] [] = EQUAL
      | compare [] _ = LESS
      | compare _ [] = GREATER
      | compare (x :: xs) (y :: ys) =
          case token_compare (x, y) of
              EQUAL => compare xs ys
            | order => order
  in
    compare left_tokens right_tokens
  end

fun insert_version item [] = [item]
  | insert_version (item as (version, _))
      ((head as (head_version, _)) :: rest) =
      if version_compare (version, head_version) = GREATER then
        item :: head :: rest
      else head :: insert_version item rest

fun sort_versions versions =
  List.foldl (fn (item, result) => insert_version item result) [] versions

fun directory_names path =
  let
    val stream = OS.FileSys.openDir path
    fun loop names =
      case OS.FileSys.readDir stream of
          NONE => List.rev names
        | SOME name => loop (name :: names)
    val names = loop []
    val _ = OS.FileSys.closeDir stream
  in
    names
  end
  handle OS.SysErr _ => []

fun install_exec root prover names =
  let
    val prefix = prover ^ "-"
    fun candidate name =
      String.isPrefix prefix name andalso is_dir (join root name)
    fun version name = String.extract (name, String.size prefix, NONE)
    val versions =
      sort_versions (map (fn name => (version name, name))
                         (List.filter candidate (directory_names root)))
    val plat = platform ()
    fun in_version (_, name) = path_exec_in (join (join root name) plat) names
  in
    first_some in_version versions
  end

and path_exec_in dir names =
  if is_dir dir then
    first_some (fn name =>
      let val path = join dir name
      in if executable path then SOME path else NONE end) names
  else NONE

fun prover_env prover =
  case prover of
      "e" => "HOL4_EPROVER_EXECUTABLE"
    | "eprover" => "HOL4_EPROVER_EXECUTABLE"
    | _ => "HOL4_" ^
      String.map (fn c =>
        if c = #"." orelse c = #"-" then #"_" else Char.toUpper c) prover ^
      "_EXECUTABLE"

fun find_exec prover names =
  let
    val config_key = "prover." ^ prover ^ ".executable"
    fun configured () =
      case lookup config_key (config_entries ()) of
          SOME path => if executable path then SOME path else NONE
        | NONE => NONE
    fun environment () =
      case OS.Process.getEnv (prover_env prover) of
          SOME path => if executable path then SOME path else NONE
        | NONE => NONE
    fun installed root = install_exec root prover names
    fun system_install () =
      case holdir () of
          NONE => NONE
        | SOME dir => installed (join (join (join dir "src") "holyhammer")
                                   "provers")
    fun user_install () =
      installed (join (join (join (home_dir ()) ".hol4") "hammer")
                 "provers")
  in
    case configured () of
        SOME path => SOME path
      | NONE =>
        (case environment () of
             SOME path => SOME path
           | NONE =>
             (case path_exec names of
                  SOME path => SOME path
                | NONE =>
                  (case system_install () of
                       SOME path => SOME path
                     | NONE => user_install ())))
  end

val find_executable = find_exec

end
