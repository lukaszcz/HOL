(* Unit tests for HolSmtLib *)

structure Unittest :> Unittest =
struct

open HolKernel Parse boolLib bossLib

(*****************************************************************************)
(* helper functions                                                          *)
(*****************************************************************************)

fun die s =
  if !Globals.interactive then
    raise (Fail s)
  else (
    print ("\n" ^ s ^ "\n");
    OS.Process.exit OS.Process.failure
  )

fun assert (x, msg) = if x then () else die ("FAIL: " ^ msg)

(* Make sure two theorems are identical *)
fun compare_thms thm_pair =
let
  val hyps_pair = Lib.pair_map Thm.hypset thm_pair
  val (concl1, concl2) = Lib.pair_map Thm.concl thm_pair
  val () = assert (HOLset.equal hyps_pair,
    "theorem hypotheses are different")
  val () = assert (Term.term_eq concl1 concl2,
    "theorem conclusions are different")
in
  ()
end

(*****************************************************************************)
(* test definitions                                                          *)
(*****************************************************************************)

(* Test: `Z3_ProofReplay.remove_definitions` works without any definitions *)
fun remove_defs_no_defs () = ([], [])

(* Test: `Z3_ProofReplay.remove_definitions` works with a duplicate definition *)
fun remove_defs_dup () = ([
  ``(z1:num) = x + 1``,
  ``(z2:num) = z1 + 2``,
  ``(z2:num) = (x + 1) + 2``
], [``(z1:num)``, ``(z2:num)``])

(* Test: `Z3_ProofReplay.remove_definitions` works with the following set of
   (tricky) definitions, which can cause an exponential term blow-up in a
   naive implementation of `remove_definitions`:

   a1 = 1
   b1 = 1
   a2 = a1 + a1
   b2 = b1 + b1
   ...
   x = an
   x = bn

   Credit: Tjark Weber for coming up with this scenario. *)
fun remove_defs_tricky1 () =
let
  val asl = [
    ``(a1:num) = 1``,
    ``(b1:num) = 1``,
    ``(x:num) = a128``,
    ``(x:num) = b128``
  ]
  val varl = [``(a1:num)``, ``(b1:num)``, ``(a128:num)``, ``(b128:num)``,
    ``(x:num)``]

  (* `gen_def` creates a definition of the form ``si = s(i-1) + s(i-1)`` *)
  fun gen_def (i, s) =
  let
    val si = Term.mk_var (s ^ Int.toString i, numSyntax.num)
    val si_1 = Term.mk_var (s ^ Int.toString (i - 1), numSyntax.num)
  in
    (si, boolSyntax.mk_eq (si, numSyntax.mk_plus (si_1, si_1)))
  end

  (* Add ``ai = a(i-1) + a(i-1)`` and the same for ``bi``, for all 1 < i <= n *)
  fun add_defs (n, asl, varl) =
    if n = 1 then
      (asl, varl)
    else
      let
        val (an, an_def) = gen_def (n, "a")
        val (bn, bn_def) = gen_def (n, "b")
      in
        add_defs (n - 1, an_def :: bn_def :: asl, an :: bn :: varl)
      end
in
  add_defs (128, asl, varl)
end

(* Test: `Z3_ProofReplay.remove_definitions` works with the following set of
   (tricky) definitions, which can cause an exponential term blow-up in a
   naive implementation of `remove_definitions`:

   x = 1000
   y = 2000
   z1 = x + 1
   z2 = y + 1

   z3 =   z2    + (y + 1) +   z1
   z3 = (y + 1) +    z2   + (x + 1)

   z4 =          z3         + (z2 + z2 + z1) +   z1
   z4 = (z2 + z2 + (x + 1)) +       z3       + (x + 1)

   (...)

   z64 =          z63          + (z62 + z62 + z1) +   z1
   z64 = (z62 + z62 + (x + 1)) +        z63       + (x + 1)

   ... except we'll go all the way up to z128 instead of z64 *)
fun remove_defs_tricky2 () =
let
  val asl = [
    ``(x:num) = 1000``,
    ``(y:num) = 2000``,
    ``(z1:num) = x + 1``,
    ``(z2:num) = y + 1``,
    ``(z3:num) = z2 + (y + 1) + z1``,
    ``(z3:num) = (y + 1) + z2 + (x + 1)``
  ]
  val varl = List.map (fn t => Lib.fst (boolSyntax.dest_eq t)) asl

  fun add3 (a, b, c) = numSyntax.mk_plus (numSyntax.mk_plus (a, b), c)

  (* `gen_def1` creates a definition of the form:
       ``zi = z(i-1) + (z(i-2) + z(i-2) + z1) + z1`` *)
  fun gen_def1 i =
  let
    val z1 = Term.mk_var ("z1", numSyntax.num)
    val zi = Term.mk_var ("z" ^ Int.toString i, numSyntax.num)
    val zi_1 = Term.mk_var ("z" ^ Int.toString (i - 1), numSyntax.num)
    val zi_2 = Term.mk_var ("z" ^ Int.toString (i - 2), numSyntax.num)
    val middle_addend = add3 (zi_2, zi_2, z1)
    val sum = add3 (zi_1, middle_addend, z1)
  in
    (zi, boolSyntax.mk_eq (zi, sum))
  end

  (* `gen_def2` creates a definition of the form:
       ``zi = (z(i-2) + z(i-2) + (x + 1)) + z(i-1) + (x + 1) *)
  fun gen_def2 i =
  let
    val xp1 = ``(x:num) + 1``
    val zi = Term.mk_var ("z" ^ Int.toString i, numSyntax.num)
    val zi_1 = Term.mk_var ("z" ^ Int.toString (i - 1), numSyntax.num)
    val zi_2 = Term.mk_var ("z" ^ Int.toString (i - 2), numSyntax.num)
    val first_addend = add3 (zi_2, zi_2, xp1)
    val sum = add3 (first_addend, zi_1, xp1)
  in
    (zi, boolSyntax.mk_eq (zi, sum))
  end

  (* Add the definitions `gen_def1 i` and `gen_def2 i`, for all 3 < i <= n *)
  fun add_defs (n, asl, varl) =
    if n = 3 then
      (asl, varl)
    else
      let
        val (v1, def1) = gen_def1 n
        val (v2, def2) = gen_def2 n
      in
        add_defs (n - 1, def1 :: def2 :: asl, v1 :: v2 :: varl)
      end
in
  add_defs (128, asl, varl)
end

(* Test: `Z3_ProofReplay.remove_definitions` works with the following set of
   definitions which are not originally circular, but can become circular due
   to term unification. Credit: Tjark Weber *)
fun remove_defs_circular1 () = ([
    ``(a:num) = 1``,
    ``(b:num) = a``,
    ``(x:num) = a``,
    ``(x:num) = b``
], [``(a:num)``, ``(b:num)``, ``(x:num)``])

(* Test: `Z3_ProofReplay.remove_definitions` works with the following set of
   definitions which are not originally circular, but can become circular due
   to term unification. Credit: Tjark Weber *)
fun remove_defs_circular2 () = ([
    ``(a:num) = 1``,
    ``(b:num) = a``,
    ``(x:num) = b``,
    ``(x:num) = a``
], [``(a:num)``, ``(b:num)``, ``(x:num)``])

(* Wrapper for `Z3_ProofReplay.remove_definitions` unit tests *)
fun remove_defs_test get_definitions_fn =
let
  (* Create a simple theorem *)
  val thm = Thm.REFL ``i:num``
  (* Add a few hypotheses that should not be removed, and which coincidentally
     look like definitions *)
  val thm = Drule.ADD_ASSUM ``(i:num) = 7`` thm
  val thm = Drule.ADD_ASSUM ``(j:num) = i + 3`` thm
  (* Add definitions (which should be removed) *)
  val (asl, varl) = get_definitions_fn ()
  val vars = List.foldl (Lib.flip HOLset.add) Term.empty_tmset varl
  (* Let's orient definitions in the same way we do during proof replay *)
  val orient = boolSyntax.mk_eq o (Library.orient_def vars) o boolSyntax.dest_eq
  val asl = List.map orient asl
  val defs = List.foldl (Lib.flip HOLset.add) Term.empty_tmset asl
  val thm_with_defs = List.foldl (Lib.uncurry Drule.ADD_ASSUM) thm asl
  (* Remove definitions *)
  val final_thm = Z3_ProofReplay.remove_definitions (defs, vars, thm_with_defs)
in
  (* Make sure the resulting theorem is equal to the one before definitions
     were added *)
  compare_thms (thm, final_thm)
end

(*****************************************************************************)
(* SMT-LIB script AST parser tests                                           *)
(*****************************************************************************)

fun span_start_line_column span =
  case span of
    SmtLib_Parser.SourceSpan {start = {line, column, ...}, ...} =>
      (line, column)

fun contains needle haystack =
let
  val n = String.size needle
  val h = String.size haystack
  fun loop i =
    i + n <= h andalso
    (String.substring (haystack, i, n) = needle orelse loop (i + 1))
in
  n = 0 orelse loop 0
end

fun script_ast_locations_success () =
let
  val script =
    SmtLib_Parser.parse_script_string
      "(set-logic QF_UF)\n(assert true)\n"
in
  case script of
    [cmd1, cmd2] =>
      let
        val (cmd1_line, cmd1_col) =
          span_start_line_column (SmtLib_Parser.loc_of cmd1)
        val () = assert (cmd1_line = 1 andalso cmd1_col = 1,
          "set-logic command location was not preserved")
      in
        case SmtLib_Parser.node_of cmd2 of
          SmtLib_Parser.CmdAssert term =>
            let
              val (term_line, term_col) =
                span_start_line_column (SmtLib_Parser.loc_of term)
            in
              assert (term_line = 2 andalso term_col = 9,
                "asserted term location was not preserved")
            end
        | _ => die "second parsed command was not an assert"
      end
  | _ => die "script AST parser returned the wrong number of commands"
end

fun script_ast_locations_syntax_error () =
  let
    val _ = SmtLib_Parser.parse_script_string "(set-logic QF_UF"
  in
    die "script AST parser accepted a malformed command"
  end
  handle Feedback.HOL_ERR holerr =>
    let
      val msg = Feedback.message_of holerr
    in
      assert (contains "line 1, column 12" msg,
        "syntax error did not include the source location: " ^ msg)
    end

fun located_string x =
  SmtLib_Parser.node_of x

fun located_sort_identifier x =
  case SmtLib_Parser.node_of x of
    SmtLib_Parser.SortIdentifier name => name
  | _ => die "expected sort identifier"

fun located_term_annotation_count x =
  case SmtLib_Parser.node_of x of
    SmtLib_Parser.TermAnnotated (_, attrs) => List.length attrs
  | _ => die "expected annotated term"

fun script_ast_metadata_decls_success () =
let
  val script =
    SmtLib_Parser.parse_script_string
      ("(set-logic QF_UF)\n" ^
       "(set-info :source \"unit\")\n" ^
       "(set-option :produce-models true)\n" ^
       "(get-info :name)\n" ^
       "(get-option :produce-models)\n" ^
       "(declare-sort |U sort| 0)\n" ^
       "(define-sort |Box sort| (A) A)\n" ^
       "(declare-const |x value| |U sort|)\n" ^
       "(declare-fun |f fun| (|U sort| Bool) |U sort|)\n" ^
       "(define-const |c const| Bool (! true :named |truth attr|))\n" ^
       "(define-fun |g fun| ((|arg 1| Bool)) Bool (! |arg 1| :named |id attr|))\n")
in
  case script of
    [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] =>
      let
        val () = (case SmtLib_Parser.node_of c1 of
            SmtLib_Parser.CmdSetLogic logic =>
              assert (located_string logic = "QF_UF", "set-logic name mismatch")
          | _ => die "set-logic did not parse to CmdSetLogic")
        val () = (case SmtLib_Parser.node_of c2 of
            SmtLib_Parser.CmdSetInfo items =>
              assert (List.length items = 2, "set-info payload mismatch")
          | _ => die "set-info did not parse to CmdSetInfo")
        val () = (case SmtLib_Parser.node_of c3 of
            SmtLib_Parser.CmdSetOption items =>
              assert (List.length items = 2, "set-option payload mismatch")
          | _ => die "set-option did not parse to CmdSetOption")
        val () = (case SmtLib_Parser.node_of c4 of
            SmtLib_Parser.CmdGetInfo keyword =>
              assert (located_string keyword = ":name", "get-info keyword mismatch")
          | _ => die "get-info did not parse to CmdGetInfo")
        val () = (case SmtLib_Parser.node_of c5 of
            SmtLib_Parser.CmdGetOption keyword =>
              assert (located_string keyword = ":produce-models",
                "get-option keyword mismatch")
          | _ => die "get-option did not parse to CmdGetOption")
        val () = (case SmtLib_Parser.node_of c6 of
            SmtLib_Parser.CmdDeclareSort (name, arity) =>
              assert (located_string name = "U sort" andalso
                located_string arity = "0", "declare-sort fields mismatch")
          | _ => die "declare-sort did not parse to CmdDeclareSort")
        val () = (case SmtLib_Parser.node_of c7 of
            SmtLib_Parser.CmdDefineSort (name, params, body) =>
              assert (located_string name = "Box sort" andalso
                List.map located_string params = ["A"] andalso
                located_sort_identifier body = "A",
                "define-sort fields mismatch")
          | _ => die "define-sort did not parse to CmdDefineSort")
        val () = (case SmtLib_Parser.node_of c8 of
            SmtLib_Parser.CmdDeclareConst (name, sort) =>
              assert (located_string name = "x value" andalso
                located_sort_identifier sort = "U sort",
                "declare-const fields mismatch")
          | _ => die "declare-const did not parse to CmdDeclareConst")
        val () = (case SmtLib_Parser.node_of c9 of
            SmtLib_Parser.CmdDeclareFun (name, domain, range) =>
              assert (located_string name = "f fun" andalso
                List.length domain = 2 andalso
                located_sort_identifier range = "U sort",
                "declare-fun fields mismatch")
          | _ => die "declare-fun did not parse to CmdDeclareFun")
        val () = (case SmtLib_Parser.node_of c10 of
            SmtLib_Parser.CmdDefineConst (name, sort, body) =>
              assert (located_string name = "c const" andalso
                located_sort_identifier sort = "Bool" andalso
                located_term_annotation_count body = 2,
                "define-const fields mismatch")
          | _ => die "define-const did not parse to CmdDefineConst")
        val () = (case SmtLib_Parser.node_of c11 of
            SmtLib_Parser.CmdDefineFun (name, vars, range, body) =>
              assert (located_string name = "g fun" andalso
                List.length vars = 1 andalso
                located_sort_identifier range = "Bool" andalso
                located_term_annotation_count body = 2,
                "define-fun fields mismatch")
          | _ => die "define-fun did not parse to CmdDefineFun")
      in
        ()
      end
  | _ => die "metadata/declaration script parsed to the wrong command count"
end

fun script_ast_command_syntax_error () =
  let
    val _ = SmtLib_Parser.parse_script_string
      "(define-sort Alias (A) Bool extra)"
  in
    die "script AST parser accepted a malformed define-sort command"
  end
  handle Feedback.HOL_ERR holerr =>
    let
      val msg = Feedback.message_of holerr
    in
      assert (contains "define-sort" msg,
        "syntax error did not include the command name: " ^ msg);
      assert (contains "line 1, column 29" msg,
        "syntax error did not include the source location: " ^ msg)
    end

(*****************************************************************************)
(* actually perform tests                                                    *)
(*****************************************************************************)

fun run_test (name, f) =
let
  val () = print ("test " ^ name ^ "...")
  val () = Profile.reset_all ()
  val () = Profile.profile name f ()
  val results = Profile.results ()
  val result = Lib.assoc name results
  val elapsed = #real result
  val elapsed_str = Time.fmt 2 elapsed
  val () = print (" OK (elapsed: " ^ elapsed_str ^ "s)\n")
  val () = Profile.reset_all ()
in
  ()
end

fun run_unittests () =
let
  val () = print "Running unit tests...\n\n"
  val tests = [
    ("remove_definitions_no_defs", fn () => remove_defs_test remove_defs_no_defs),
    ("remove_definitions_dup", fn () => remove_defs_test remove_defs_dup),
    ("remove_definitions_tricky1", fn () => remove_defs_test remove_defs_tricky1),
    ("remove_definitions_tricky2", fn () => remove_defs_test remove_defs_tricky2),
    ("remove_definitions_circular1", fn () => remove_defs_test remove_defs_circular1),
    ("remove_definitions_circular2", fn () => remove_defs_test remove_defs_circular2),
    ("script_ast_locations_success", script_ast_locations_success),
    ("script_ast_locations_syntax_error", script_ast_locations_syntax_error),
    ("script_ast_metadata_decls_success", script_ast_metadata_decls_success),
    ("script_ast_command_syntax_error", script_ast_command_syntax_error)
  ]
  val () = List.app run_test tests
  val () = print "\ndone, all unit tests successful.\n"
in
  ()
end

end (* struct *)
