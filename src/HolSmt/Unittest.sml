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

fun with_temp_file contents f =
let
  val path = OS.FileSys.tmpName ()
  val outstream = TextIO.openOut path
  val _ = TextIO.output (outstream, contents)
  val _ = TextIO.closeOut outstream
  fun cleanup () = OS.FileSys.remove path handle _ => ()
  val result = f path handle e => (cleanup (); raise e)
  val _ = cleanup ()
in
  result
end

fun read_text_file path =
let
  val instream = TextIO.openIn path
  val contents = TextIO.inputAll instream
  val _ = TextIO.closeIn instream
in
  contents
end

fun parse_smtlib_assertions contents =
  with_temp_file contents
    (fn path =>
      let
        val (_, _, _, assertions) = SmtLib_Parser.parse_file path
      in
        assertions
      end)

fun parse_smtlib_state contents =
  with_temp_file contents SmtLib_Parser.parse_file_state

fun inferred_logic tm =
let
  val (translation, strings) = SmtLib.goal_to_SmtLib_translation NONE ([], tm)
  val set_logic =
    case strings of
      first :: _ => first
    | [] => die "SMT-LIB translation emitted no commands"
in
  (SmtLib.translation_logic translation, set_logic,
   SmtLib.translation_records translation, translation)
end

fun term_with_types t =
  Lib.with_flag (show_types, true) Hol_pp.term_to_string t

fun string_get_char text =
let
  val pos = ref 0
  val len = String.size text
in
  fn () =>
    if !pos < len then
      let
        val c = String.sub (text, !pos)
      in
        pos := !pos + 1;
        c
      end
    else
      raise Feedback.mk_HOL_ERR "Unittest" "string_get_char"
        "end of string"
end

fun assert_body s =
  if String.isPrefix "(assert " s then
    let
      val prefix_len = String.size "(assert "
      val suffix_len = String.size ")\n"
      val body_len = String.size s - prefix_len - suffix_len
    in
      SOME (String.substring (s, prefix_len, body_len))
    end
  else
    NONE

fun parse_roundtrip_term test_name smt_term dicts =
  SmtLib_Parser.parse_term (Library.get_token (string_get_char smt_term)) dicts
  handle Feedback.HOL_ERR holerr =>
    die ("FAIL: round-trip test '" ^ test_name ^
      "' failed to parse SMT-LIB term '" ^ smt_term ^ "': " ^
      top_structure_of holerr ^ "." ^ top_function_of holerr ^
      ", message: " ^ message_of holerr)

fun assert_roundtrip_assertion test_name idx smt_term expected parsed =
  assert (Term.aconv expected parsed,
    "round-trip test '" ^ test_name ^ "' assertion " ^
    Int.toString idx ^ " mismatch for SMT-LIB term '" ^ smt_term ^
    "'\nexpected: " ^ term_with_types expected ^
    "\nparsed: " ^ term_with_types parsed)

fun assert_goal_roundtrip test_name (goal as (assumptions, conclusion)) =
let
  val (translation, strings) = SmtLib.goal_to_SmtLib_translation NONE goal
  val dicts = SmtLib.parser_dicts_for_translation translation
  val smt_assertions = List.mapPartial assert_body strings
  val expected_assertions = assumptions @ [boolSyntax.mk_neg conclusion]
  val parsed_assertions =
    List.map (fn smt => parse_roundtrip_term test_name smt dicts)
      smt_assertions
  val _ = assert (List.length smt_assertions = List.length expected_assertions,
    "round-trip test '" ^ test_name ^ "' emitted " ^
    Int.toString (List.length smt_assertions) ^ " assertion(s), expected " ^
    Int.toString (List.length expected_assertions))
  fun compare_one (idx, (smt_term, (expected, parsed))) =
    assert_roundtrip_assertion test_name idx smt_term expected parsed
in
  List.app compare_one
    (ListPair.zipEq
      (List.tabulate (List.length smt_assertions, fn n => n + 1),
       ListPair.zipEq (smt_assertions,
         ListPair.zipEq (expected_assertions, parsed_assertions))))
end

fun term_is_var_named name tm =
  let val (var_name, _) = Term.dest_var tm
  in var_name = name end
  handle HOL_ERR _ => false

fun find_symbol_metadata theory kind name metadata =
  case List.find
      (fn ({theory = t, kind = k, name = n, ...}
             : SmtLib_Theories.symbol_metadata) =>
        t = theory andalso k = kind andalso n = name)
      metadata of
    SOME item => item
  | NONE => die ("missing symbol metadata for " ^ theory ^ "." ^ name)

fun find_symbol_metadata_source theory kind name source_pred metadata =
  case List.find
      (fn (item as {theory = t, kind = k, name = n, ...}
             : SmtLib_Theories.symbol_metadata) =>
        t = theory andalso k = kind andalso n = name andalso source_pred item)
      metadata of
    SOME item => item
  | NONE => die ("missing symbol metadata for " ^ theory ^ "." ^ name)

fun metadata_is_official
    ({source = SmtLib_Theories.Official, ...}
       : SmtLib_Theories.symbol_metadata) = true
  | metadata_is_official _ = false

fun metadata_is_extension
    ({source = SmtLib_Theories.Extension _, ...}
       : SmtLib_Theories.symbol_metadata) = true
  | metadata_is_extension _ = false

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

fun expect_hol_error_contains label expected f =
  let
    val _ = f ()
  in
    die ("expected HOL error for " ^ label)
  end
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (contains expected msg,
        label ^ " diagnostic did not include '" ^ expected ^ "': " ^ msg)
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

fun located_datatype_decl_counts x =
  case SmtLib_Parser.node_of x of
    SmtLib_Parser.DatatypeDecl (params, constructors) =>
      (List.length params, List.length constructors)

fun constructor_selector_count x =
  case SmtLib_Parser.node_of x of
    SmtLib_Parser.DatatypeConstructor (_, tester, selectors) =>
      (case SmtLib_Parser.node_of tester of
         SmtLib_Parser.DatatypeTester constructor_name =>
           (located_string constructor_name, List.length selectors))

fun function_signature_name x =
  case SmtLib_Parser.node_of x of
    SmtLib_Parser.FunctionSignature (name, _, _) => located_string name

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

fun script_ast_stack_and_query_success () =
let
  val script =
    SmtLib_Parser.parse_script_string
      ("(set-logic QF_UF)\n" ^
       "(declare-const a Bool)\n" ^
       "(assert (! a :named A))\n" ^
       "(push 1)\n" ^
       "(pop)\n" ^
       "(reset-assertions)\n" ^
       "(check-sat)\n" ^
       "(check-sat-assuming (a))\n" ^
       "(get-proof)\n" ^
       "(get-unsat-assumptions)\n" ^
       "(get-unsat-core)\n" ^
       "(get-model)\n" ^
       "(get-value (a true))\n" ^
       "(get-assignment)\n" ^
       "(get-assertions)\n" ^
       "(reset)\n" ^
       "(exit)\n")
in
  case script of
    [_, _, _, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17] =>
      let
        val () = (case SmtLib_Parser.node_of c4 of
            SmtLib_Parser.CmdPush (SOME level) =>
              assert (located_string level = "1", "push level mismatch")
          | _ => die "push did not parse to CmdPush")
        val () = (case SmtLib_Parser.node_of c5 of
            SmtLib_Parser.CmdPop NONE => ()
          | _ => die "pop did not parse to CmdPop")
        val () = (case SmtLib_Parser.node_of c6 of
            SmtLib_Parser.CmdResetAssertions => ()
          | _ => die "reset-assertions did not parse")
        val () = (case SmtLib_Parser.node_of c7 of
            SmtLib_Parser.CmdCheckSat => ()
          | _ => die "check-sat did not parse")
        val () = (case SmtLib_Parser.node_of c8 of
            SmtLib_Parser.CmdCheckSatAssuming assumptions =>
              assert (List.length assumptions = 1,
                "check-sat-assuming assumption count mismatch")
          | _ => die "check-sat-assuming did not parse")
        val () = (case SmtLib_Parser.node_of c9 of
            SmtLib_Parser.CmdGetProof => ()
          | _ => die "get-proof did not parse")
        val () = (case SmtLib_Parser.node_of c10 of
            SmtLib_Parser.CmdGetUnsatAssumptions => ()
          | _ => die "get-unsat-assumptions did not parse")
        val () = (case SmtLib_Parser.node_of c11 of
            SmtLib_Parser.CmdGetUnsatCore => ()
          | _ => die "get-unsat-core did not parse")
        val () = (case SmtLib_Parser.node_of c12 of
            SmtLib_Parser.CmdGetModel => ()
          | _ => die "get-model did not parse")
        val () = (case SmtLib_Parser.node_of c13 of
            SmtLib_Parser.CmdGetValue terms =>
              assert (List.length terms = 2, "get-value term count mismatch")
          | _ => die "get-value did not parse")
        val () = (case SmtLib_Parser.node_of c14 of
            SmtLib_Parser.CmdGetAssignment => ()
          | _ => die "get-assignment did not parse")
        val () = (case SmtLib_Parser.node_of c15 of
            SmtLib_Parser.CmdGetAssertions => ()
          | _ => die "get-assertions did not parse")
        val () = (case SmtLib_Parser.node_of c16 of
            SmtLib_Parser.CmdReset => ()
          | _ => die "reset did not parse")
        val () = (case SmtLib_Parser.node_of c17 of
            SmtLib_Parser.CmdExit => ()
          | _ => die "exit did not parse")
      in
        ()
      end
  | _ => die "stack/query script parsed to the wrong command count"
end

fun script_ast_datatype_recursive_remaining_success () =
let
  val script =
    SmtLib_Parser.parse_script_string
      ("(set-logic ALL)\n" ^
       "(define-fun-rec fact ((n Int)) Int (ite (= n 0) 1 (* n (fact (- n 1)))))\n" ^
       "(define-funs-rec ((even ((n Int)) Bool) (odd ((n Int)) Bool)) " ^
         "((ite (= n 0) true (odd (- n 1))) (ite (= n 0) false (even (- n 1)))))\n" ^
       "(declare-datatype Color ((red) (green) (blue)))\n" ^
       "(declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))\n" ^
       "(declare-datatypes ((Tree 1) (Forest 1)) " ^
         "((par (T) ((leaf (value T)) (node (children (Forest T))))) " ^
          "(par (T) ((empty) (insert (first (Tree T)) (rest (Forest T)))))))\n" ^
       "(assert ((_ is cons) xs))\n" ^
       "(echo \"datatype examples parsed\")\n" ^
       "(exit)\n")
in
  case script of
    [_, c2, c3, c4, c5, c6, c7, c8, c9] =>
      let
        val () = (case SmtLib_Parser.node_of c2 of
            SmtLib_Parser.CmdDefineFunRec (name, vars, range, _) =>
              assert (located_string name = "fact" andalso
                List.length vars = 1 andalso
                located_sort_identifier range = "Int",
                "define-fun-rec fields mismatch")
          | _ => die "define-fun-rec did not parse")
        val () = (case SmtLib_Parser.node_of c3 of
            SmtLib_Parser.CmdDefineFunsRec (sigs, bodies) =>
              assert (List.map function_signature_name sigs = ["even", "odd"] andalso
                List.length bodies = 2,
                "define-funs-rec fields mismatch")
          | _ => die "define-funs-rec did not parse")
        val () = (case SmtLib_Parser.node_of c4 of
            SmtLib_Parser.CmdDeclareDatatype (name, decl) =>
              assert (located_string name = "Color" andalso
                located_datatype_decl_counts decl = (0, 3),
                "declare-datatype enum fields mismatch")
          | _ => die "enum declare-datatype did not parse")
        val () = (case SmtLib_Parser.node_of c5 of
            SmtLib_Parser.CmdDeclareDatatype (name, decl) =>
              assert (located_string name = "List" andalso
                located_datatype_decl_counts decl = (1, 2),
                "parametric declare-datatype fields mismatch")
          | _ => die "parametric declare-datatype did not parse")
        val () = (case SmtLib_Parser.node_of c6 of
            SmtLib_Parser.CmdDeclareDatatypes (bindings, decls) =>
              assert (List.length bindings = 2 andalso
                List.map located_datatype_decl_counts decls = [(1, 2), (1, 2)],
                "declare-datatypes fields mismatch")
          | _ => die "declare-datatypes did not parse")
        val () = (case SmtLib_Parser.node_of c5 of
            SmtLib_Parser.CmdDeclareDatatype (_, decl) =>
              (case SmtLib_Parser.node_of decl of
                 SmtLib_Parser.DatatypeDecl (_, [_, cons_ctor]) =>
                   assert (constructor_selector_count cons_ctor = ("cons", 2),
                     "constructor selectors/tester were not represented")
               | _ => die "unexpected datatype declaration shape")
          | _ => die "parametric declare-datatype did not parse")
        val () = (case SmtLib_Parser.node_of c7 of
            SmtLib_Parser.CmdAssert term =>
              (case SmtLib_Parser.node_of term of
                 SmtLib_Parser.TermApply (head, _) =>
                   (case SmtLib_Parser.node_of head of
                      SmtLib_Parser.TermIndexed (index_head, indices) =>
                        assert (located_string index_head = "is" andalso
                          List.length indices = 1,
                          "tester term did not parse as indexed identifier")
                    | _ => die "tester assert head was not indexed")
               | _ => die "tester assert was not an application")
          | _ => die "tester assert did not parse")
        val () = (case SmtLib_Parser.node_of c8 of
            SmtLib_Parser.CmdEcho msg =>
              assert (located_string msg = "datatype examples parsed",
                "echo string mismatch")
          | _ => die "echo did not parse")
        val () = (case SmtLib_Parser.node_of c9 of
            SmtLib_Parser.CmdExit => ()
          | _ => die "exit did not parse")
      in
        ()
      end
  | _ => die "datatype/recursive script parsed to the wrong command count"
end

fun parse_file_datatype_command_success () =
  let
    fun expect_datatype_success label script =
      let
        val state = SmtLib_Parser.typecheck_script_string script
      in
        assert (#logic state = "ALL", label ^ " script changed logic");
        assert (List.null (#assertions state),
          label ^ " command-only script produced assertions")
      end
    val _ = expect_datatype_success "recursive datatype"
      ("(set-logic ALL)\n" ^
       "(declare-datatype List ((nil) (cons (head Int) (tail List))))\n" ^
       "(check-sat)\n")
    val _ = expect_datatype_success "parametric datatype"
      ("(set-logic ALL)\n" ^
       "(declare-datatype Box (par (T) ((box (value T)))))\n" ^
       "(check-sat)\n")
    val _ = expect_datatype_success "mutual datatype"
      ("(set-logic ALL)\n" ^
       "(declare-datatypes ((Tree 0) (Forest 0))\n" ^
       "  (((leaf) (node (children Forest)))\n" ^
       "   ((nilF) (consF (head Tree) (tail Forest)))))\n" ^
       "(check-sat)\n")
  in
    ()
  end

fun parse_file_datatype_dictionary_success () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic ALL)\n" ^
       "(declare-datatype Pair ((mk-pair (left Int) (right Bool))))\n" ^
       "(declare-const p Pair)\n" ^
       "(assert (and ((_ is mk-pair) p) " ^
       "(= (left (mk-pair 3 true)) 3) (right p)))\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1,
    "datatype dictionary script produced the wrong assertion count");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "datatype dictionary assertion did not parse as Bool")
end

fun parse_file_parametric_datatype_dictionary_success () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic ALL)\n" ^
       "(declare-datatype Box (par (T) ((box (value T)))))\n" ^
       "(declare-const bi (Box Int))\n" ^
       "(assert (and (= (value (box 1)) 1) ((_ is box) bi)))\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1,
    "parametric datatype dictionary script produced the wrong assertion count");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "parametric datatype assertion did not parse as Bool")
end

fun parse_legacy_datatype_mutual_dictionary_success () =
let
  val (_, _, _, assertions) =
    SmtLib_Parser.parse_benchmark
      (Library.get_token (string_get_char
        ("(set-logic ALL)\n" ^
         "(declare-datatypes ((Tree 0) (Forest 0))\n" ^
         "  (((leaf) (node (children Forest)))\n" ^
         "   ((nilF) (consF (head Tree) (tail Forest)))))\n" ^
         "(assert (and ((_ is node) (node nilF)) " ^
         "(= (head (consF leaf nilF)) leaf)))\n" ^
         "(exit)\n")))
in
  assert (List.length assertions = 1,
    "legacy datatype parser produced the wrong assertion count");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "legacy datatype parser assertion did not parse as Bool")
end

fun parse_file_echo_success () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic QF_UF)\n" ^
       "(echo \"hello\")\n" ^
       "(assert true)\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1, "echo changed assertion state")
end

fun parse_file_push_pop_assertion_scoping () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic QF_UF)\n" ^
       "(declare-const a Bool)\n" ^
       "(assert a)\n" ^
       "(push 1)\n" ^
       "(declare-const b Bool)\n" ^
       "(assert b)\n" ^
       "(pop 1)\n" ^
       "(assert true)\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 2, "push/pop assertion count mismatch");
  assert (List.exists (term_is_var_named "a") assertions,
    "base assertion was not retained");
  assert (List.exists (fn tm => Term.term_eq tm boolSyntax.T) assertions,
    "post-pop assertion was not retained");
  assert (not (List.exists (term_is_var_named "b") assertions),
    "popped assertion remained visible")
end

fun parse_file_push_pop_declaration_scoping () =
  let
    val _ =
      parse_smtlib_assertions
        ("(set-logic QF_UF)\n" ^
         "(push 1)\n" ^
         "(declare-const b Bool)\n" ^
         "(pop 1)\n" ^
         "(assert b)\n" ^
         "(exit)\n")
  in
    die "popped declaration remained visible"
  end
  handle Feedback.HOL_ERR _ => ()

fun parse_file_reset_assertions_state () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic QF_UF)\n" ^
       "(declare-const a Bool)\n" ^
       "(declare-const b Bool)\n" ^
       "(assert a)\n" ^
       "(push 1)\n" ^
       "(assert false)\n" ^
       "(reset-assertions)\n" ^
       "(assert b)\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1,
    "reset-assertions did not clear assertion stack");
  assert (List.exists (term_is_var_named "b") assertions,
    "reset-assertions did not preserve declarations");
  assert (not (List.exists (term_is_var_named "a") assertions),
    "reset-assertions retained an old assertion")
end

fun parse_file_reset_state () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic QF_UF)\n" ^
       "(declare-const a Bool)\n" ^
       "(assert a)\n" ^
       "(reset)\n" ^
       "(set-logic QF_UF)\n" ^
       "(declare-const b Bool)\n" ^
       "(assert b)\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1, "reset did not clear old assertions");
  assert (List.exists (term_is_var_named "b") assertions,
    "reset did not permit rebuilding state");
  assert (not (List.exists (term_is_var_named "a") assertions),
    "reset retained pre-reset assertions or declarations")
end

fun parse_file_query_commands_success () =
let
  val {assertions, named_assertions, queries, ...} =
    parse_smtlib_state
      ("(set-logic QF_UF)\n" ^
       "(declare-const a Bool)\n" ^
       "(assert (! a :named A))\n" ^
       "(get-info :version)\n" ^
       "(get-option :print-success)\n" ^
       "(check-sat)\n" ^
       "(check-sat-assuming (a))\n" ^
       "(get-model)\n" ^
       "(get-value (a true))\n" ^
       "(get-assignment)\n" ^
       "(get-assertions)\n" ^
       "(get-unsat-assumptions)\n" ^
       "(get-unsat-core)\n" ^
       "(get-proof)\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1, "query commands changed assertions");
  assert (List.exists (term_is_var_named "a") assertions,
    "named assertion was not preserved through query commands");
  assert (List.length named_assertions = 1,
    "named assertion metadata was not preserved");
  assert (List.exists (fn (name, tm) =>
      name = "A" andalso term_is_var_named "a" tm) named_assertions,
    "named assertion metadata is incorrect");
  assert (List.exists (fn query =>
      case query of
        SmtLib_Parser.QueryCheckSat {assumptions, assertions, ...} =>
          List.length assumptions = 1 andalso
          List.exists (term_is_var_named "a") assumptions andalso
          List.length assertions = 1 andalso
          List.exists (term_is_var_named "a") assertions
      | _ => false) queries,
    "check-sat-assuming state snapshot was not preserved");
  assert (List.exists (fn query =>
      case query of
        SmtLib_Parser.QueryGetInfo keyword => keyword = ":version"
      | _ => false) queries,
    "get-info query was not recorded in the state snapshot");
  assert (List.exists (fn query =>
      case query of
        SmtLib_Parser.QueryGetOption keyword => keyword = ":print-success"
      | _ => false) queries,
    "get-option query was not recorded in the state snapshot")
end

fun parse_file_define_fun_fragment_scope_success () =
let
  val {assertions, local_definitions, queries, ...} =
    parse_smtlib_state
      ("(set-logic QF_UF)\n" ^
       "(define-fun id ((p Bool)) Bool p)\n" ^
       "(assert (id true))\n" ^
       "(check-sat)\n")
in
  assert (List.length assertions = 1,
    "define-fun command changed user assertion count");
  assert (List.length local_definitions = 1,
    "define-fun definition was not tracked as a local definition");
  assert (SmtLib_Logics.fragment_violation_diagnostic "QF_UF" assertions =
          NONE,
    "define-fun local definition leaked into QF_UF assertion fragment check");
  assert (List.exists (fn query =>
      case query of
        SmtLib_Parser.QueryCheckSat
          {assertions = query_assertions, local_definitions = query_defs,
           assumptions = []} =>
          List.length query_assertions = 1 andalso
          List.length query_defs = 1
      | _ => false) queries,
    "check-sat query did not preserve define-fun state snapshot")
end

fun parse_file_define_funs_rec_fragment_scope_success () =
let
  val {assertions, local_definitions, queries, ...} =
    parse_smtlib_state
      ("(set-logic QF_UF)\n" ^
       "(define-funs-rec ((f ((p Bool)) Bool)) ((not p)))\n" ^
       "(assert (f false))\n" ^
       "(check-sat)\n")
in
  assert (List.length assertions = 1,
    "define-funs-rec command changed user assertion count");
  assert (List.length local_definitions = 1,
    "define-funs-rec definition was not tracked as a local definition");
  assert (SmtLib_Logics.fragment_violation_diagnostic "QF_UF" assertions =
          NONE,
    "define-funs-rec local definition leaked into QF_UF assertion fragment check");
  assert (List.exists (fn query =>
      case query of
        SmtLib_Parser.QueryCheckSat
          {assertions = query_assertions, local_definitions = query_defs,
           assumptions = []} =>
          List.length query_assertions = 1 andalso
          List.length query_defs = 1
      | _ => false) queries,
    "check-sat query did not preserve define-funs-rec state snapshot")
end

fun smtlib_soundness_audit_scope_success () =
let
  val {assertions, local_definitions, ...} =
    parse_smtlib_state
      ("(set-logic ALL)\n" ^
       "(declare-const |quoted symbol| Bool)\n" ^
       "(declare-const x Int)\n" ^
       "(define-const c Bool |quoted symbol|)\n" ^
       "(define-fun same ((x Bool)) Bool x)\n" ^
       "(assert (and (and " ^
       "(forall ((x Bool)) x) " ^
       "(let ((x true)) x)) " ^
       "(and (same |quoted symbol|) " ^
       "(= (div 7 0) (div 7 0)))))\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1,
    "soundness-audit script should retain one user assert");
  assert (List.length local_definitions = 2,
    "define-const/define-fun local definitions were not tracked");
  assert (Term.type_of (List.last assertions) = Type.bool,
    "binder/let/quoted/division audit assertion did not parse as Bool")
end

fun smtlib_indexed_parametric_sort_reconstruction_success () =
let
  val {assertions = array_assertions, ...} =
    parse_smtlib_state
      ("(set-logic ALL)\n" ^
       "(define-sort WordPair (T) (Array T (_ BitVec 8)))\n" ^
       "(declare-const a (Array Int (_ BitVec 8)))\n" ^
       "(assert (= (select a 0) #x00))\n" ^
       "(exit)\n")
  val {assertions = fp_assertions, ...} =
    parse_smtlib_state
      ("(set-logic QF_FP)\n" ^
       "(declare-const b Float32)\n" ^
       "(declare-const rm RoundingMode)\n" ^
       "(assert (= (fp.add rm b b) b))\n" ^
       "(exit)\n")
in
  assert (List.length array_assertions = 1,
    "indexed/parametric sort audit script produced the wrong assertion count");
  assert (Term.type_of (List.hd array_assertions) = Type.bool,
    "Array/BitVec sort audit assertion did not parse as Bool");
  assert (List.length fp_assertions = 1,
    "indexed floating-point sort audit script produced wrong assertion count");
  assert (Term.type_of (List.hd fp_assertions) = Type.bool,
    "FloatingPoint sort audit assertion did not parse as Bool")
end

fun smtlib_typecheck_invalid_assertion_diagnostic () =
  let
    val _ =
      parse_smtlib_state
        ("(set-logic QF_LIA)\n" ^
         "(assert 1)\n" ^
         "(exit)\n")
  in
    die "typechecker accepted a non-Bool assertion"
  end
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (contains "invalid SMT-LIB input" msg,
        "invalid assertion diagnostic did not identify invalid input: " ^ msg);
      assert (contains "line 2, column 9" msg,
        "invalid assertion diagnostic did not include source location: " ^ msg);
      assert (contains "command 'assert'" msg,
        "invalid assertion diagnostic did not include command context: " ^ msg);
      assert (contains "expected sort :bool" msg andalso
              contains "actual sort :int" msg,
        "invalid assertion diagnostic did not include expected/actual sorts: " ^
        msg)
    end

fun smtlib_typecheck_declared_function_mismatch_diagnostic () =
  let
    val _ =
      parse_smtlib_state
        ("(set-logic ALL)\n" ^
         "(declare-fun f (Bool) Bool)\n" ^
         "(assert (f 0))\n" ^
         "(exit)\n")
  in
    die "typechecker accepted an ill-sorted declared-function application"
  end
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (contains "command 'assert'" msg,
        "function mismatch diagnostic lacked command context: " ^ msg);
      assert (contains "expected sort :bool" msg andalso
              contains "actual sort :int" msg,
        "function mismatch diagnostic lacked expected/actual sorts: " ^ msg)
    end

fun smtlib_array_type_mismatch_diagnostics () =
let
  fun script logic body =
    "(set-logic " ^ logic ^ ")\n" ^ body ^ "(exit)\n"
  fun expect (label, text, diagnostic) =
    expect_hol_error_contains label diagnostic
      (fn () => ignore (parse_smtlib_state text))
  val cases = [
    ("array sort arity",
     script "QF_AX"
       ("(declare-sort I 0)\n" ^
        "(declare-const bad (Array I))\n"),
     "ArraysEx Array sort arity mismatch"),
    ("select index sort",
     script "QF_AX"
       ("(declare-sort I 0)\n" ^
        "(declare-sort E 0)\n" ^
        "(declare-const a (Array I E))\n" ^
        "(declare-const e E)\n" ^
        "(assert (= (select a e) e))\n"),
     "ArraysEx select index sort mismatch"),
    ("store value sort",
     script "QF_AX"
       ("(declare-sort I 0)\n" ^
        "(declare-sort E 0)\n" ^
        "(declare-const a (Array I E))\n" ^
        "(declare-const i I)\n" ^
        "(assert (= (store a i i) a))\n"),
     "ArraysEx store value sort mismatch"),
    ("read over write value sort",
     script "QF_AX"
       ("(declare-sort I 0)\n" ^
        "(declare-sort E 0)\n" ^
        "(declare-const a (Array I E))\n" ^
        "(declare-const i I)\n" ^
        "(assert (= (select (store a i i) i) i))\n"),
     "ArraysEx store value sort mismatch"),
    ("write over write value sort",
     script "QF_AX"
       ("(declare-sort I 0)\n" ^
        "(declare-sort E 0)\n" ^
        "(declare-const a (Array I E))\n" ^
        "(declare-const i I)\n" ^
        "(assert (= (store (store a i i) i i) a))\n"),
     "ArraysEx store value sort mismatch"),
    ("extensionality index sort",
     script "AUFLIA"
       ("(declare-const a (Array Int Bool))\n" ^
        "(assert (forall ((i Bool)) (= (select a i) true)))\n"),
     "ArraysEx select index sort mismatch"),
    ("mixed index value sorts",
     script "QF_AUFBV"
       ("(declare-const a (Array (_ BitVec 8) Bool))\n" ^
        "(assert (= (select a true) true))\n"),
     "ArraysEx select index sort mismatch")
  ]
  val {assertions, ...} =
    parse_smtlib_state
      (script "QF_AX"
        ("(declare-sort I 0)\n" ^
         "(declare-sort E 0)\n" ^
         "(declare-const a (Array I E))\n" ^
         "(declare-const i I)\n" ^
         "(declare-const e E)\n" ^
         "(assert (= (select (store a i e) i) e))\n"))
in
  List.app expect cases;
  assert (List.length assertions = 1,
    "well-typed array script should produce exactly one assertion");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "well-typed array assertion did not typecheck as Bool")
end

fun smtlib_command_malformed_diagnostics () =
  let
    fun typecheck text () = ignore (SmtLib_Parser.typecheck_script_string text)
    fun parse_state text () = ignore (parse_smtlib_state text)
  in
    expect_hol_error_contains "unknown set-logic" "unknown logic"
      (typecheck "(set-logic NO_SUCH_LOGIC)\n");
    expect_hol_error_contains "duplicate set-logic"
      "set-logic issued more than once"
      (typecheck "(set-logic QF_UF)\n(set-logic QF_UF)\n");
    expect_hol_error_contains "declare-sort arity"
      "unsupported sort arity"
      (typecheck "(set-logic QF_UF)\n(declare-sort U 1)\n");
    expect_hol_error_contains "declare-fun arity"
      "wrong number of arguments for 'f'"
      (typecheck
        ("(set-logic QF_UF)\n" ^
         "(declare-fun f (Bool) Bool)\n" ^
         "(assert (f true true))\n"));
    typecheck
      ("(set-logic QF_UF)\n" ^
       "(declare-fun h ((-> Bool Bool)) Bool)\n" ^
       "(check-sat)\n") ();
    expect_hol_error_contains "malformed function sort"
      "function sort '->' expects at least one domain sort and one range sort"
      (typecheck
        ("(set-logic QF_UF)\n" ^
         "(declare-const bad (-> Bool))\n"));
    expect_hol_error_contains "duplicate declare-const"
      "duplicate declaration for symbol 'p'"
      (typecheck
        ("(set-logic QF_UF)\n" ^
         "(declare-const p Bool)\n" ^
         "(declare-const p Bool)\n"));
    expect_hol_error_contains "duplicate define-const"
      "duplicate define-const/define-fun declaration for symbol 'p'"
      (typecheck
        ("(set-logic QF_UF)\n" ^
         "(define-const p Bool true)\n" ^
         "(define-const p Bool false)\n"));
    expect_hol_error_contains "set-option after logic"
      "set-option after logic or assertions"
      (typecheck
        ("(set-logic QF_UF)\n" ^
         "(set-option :produce-proofs true)\n"));
    typecheck
      ("(set-logic QF_LIA)\n" ^
       "(define-fun-rec f ((x Int)) Int (f x))\n" ^
       "(assert (= (f 0) (f 0)))\n") ();
    expect_hol_error_contains "mutual recursive define-fun"
      "malformed recursive definition block"
      (typecheck
        ("(set-logic QF_LIA)\n" ^
         "(define-funs-rec ((f ((x Int)) Int)) ())\n"));
    typecheck
      ("(set-logic QF_LIA)\n" ^
       "(define-funs-rec ((even ((x Int)) Bool) (odd ((x Int)) Bool))\n" ^
       "  ((odd x) (even x)))\n" ^
       "(assert (= (even 0) (even 0)))\n") ();
    typecheck
      ("(set-logic ALL)\n" ^
       "(declare-datatypes ((T 0) (U 0)) (((mkT)) ((mkU))))\n") ();
    expect_hol_error_contains "check-sat-assuming sort"
      "command 'check-sat-assuming'"
      (typecheck
        ("(set-logic QF_LIA)\n" ^
         "(check-sat-assuming (1))\n"));
    expect_hol_error_contains "get-value sort"
      "could not resolve symbol 'missing'"
      (typecheck
        ("(set-logic QF_UF)\n" ^
         "(get-value (missing))\n"));
    expect_hol_error_contains "pop underflow"
      "cannot pop the base assertion scope"
      (parse_state "(set-logic QF_UF)\n(pop 1)\n")
  end

fun smtlib_logic_fragment_diagnostics () =
  let
    fun fragment logic text =
      let
        val state = parse_smtlib_state text
      in
        SmtLib_Logics.fragment_violation_diagnostic logic (#assertions state)
      end
    fun expect_fragment label logic text expected =
      case fragment logic text of
        SOME msg =>
          assert (contains expected msg,
            label ^ " diagnostic missed '" ^ expected ^ "': " ^ msg)
      | NONE => die (label ^ " fragment violation was not detected")
    fun expect_no_fragment label logic text =
      case fragment logic text of
        SOME msg =>
          die (label ^ " reported a spurious fragment violation: " ^ msg)
      | NONE => ()
    fun script logic body =
      "(set-logic " ^ logic ^ ")\n" ^ body ^ "(check-sat)\n"
    fun script_for_checker parse_logic body =
      script parse_logic body
  in
    expect_fragment "QF quantifier" "QF_UF"
      (script "QF_UF"
       "(assert (forall ((p Bool)) p))\n")
      "quantified formula";
    expect_no_fragment "non-QF quantifier" "UF"
      (script "UF"
       "(assert (forall ((p Bool)) p))\n");
    expect_no_fragment "QF define-fun local definition" "QF_UF"
      (script "QF_UF"
       "(define-fun id ((p Bool)) Bool p)\n" ^
       "(assert (id true))\n" ^
       "");
    expect_no_fragment "QF recursive local definition" "QF_UF"
      (script "QF_UF"
       "(define-fun-rec f ((p Bool)) Bool p)\n");
    expect_fragment "linear arithmetic product" "ALIA"
      (script "ALIA"
       "(declare-const x Int)\n" ^
       "(declare-const y Int)\n" ^
       "(assert (= (* x y) 1))\n")
      "nonlinear arithmetic product";
    expect_no_fragment "linear coefficient product" "QF_LIA"
      (script "QF_LIA"
       "(declare-const x Int)\n" ^
       "(assert (= (* 2 x) 4))\n");
    expect_no_fragment "ground literal product" "QF_LIA"
      (script "QF_LIA"
       "(assert (= (* 2 3) 6))\n");
    expect_no_fragment "integer nonlinear arithmetic product" "NIA"
      (script "NIA"
       "(declare-const x Int)\n" ^
       "(declare-const y Int)\n" ^
       "(assert (= (* x y) 1))\n");
    expect_no_fragment "real nonlinear arithmetic product" "NRA"
      (script "NRA"
       "(declare-const x Real)\n" ^
       "(declare-const y Real)\n" ^
       "(assert (= (* x y) 1.0))\n");
    expect_fragment "difference logic sum atom" "QF_IDL"
      (script "QF_IDL"
       "(declare-const x Int)\n" ^
       "(declare-const y Int)\n" ^
       "(assert (<= (+ x y) 1))\n")
      "difference logic atom shape";
    expect_no_fragment "difference logic difference atom" "QF_IDL"
      (script "QF_IDL"
       "(declare-const x Int)\n" ^
       "(declare-const y Int)\n" ^
       "(assert (<= (- x y) 1))\n");
    expect_fragment "non-UF function application" "QF_NIRA"
      (script "QF_NIRA"
       "(declare-fun outside_fragment (Int) Int)\n" ^
       "(assert (= (outside_fragment 0) 0))\n")
      "uninterpreted function application";
    expect_no_fragment "UF function application" "QF_UFNIRA"
      (script "QF_UFNIRA"
       "(declare-fun outside_fragment (Int) Int)\n" ^
       "(assert (= (outside_fragment 0) 0))\n");
    expect_fragment "NIA real sort" "NIA"
      (script_for_checker "ALL"
       "(declare-const outside_fragment Real)\n" ^
       "(assert (= outside_fragment 0.0))\n")
      "real term sort";
    expect_no_fragment "NRA real sort" "NRA"
      (script "NRA"
       "(declare-const x Real)\n" ^
       "(assert (= x 0.0))\n");
    expect_fragment "NRA integer sort" "NRA"
      (script_for_checker "ALL"
       "(declare-const outside_fragment Int)\n" ^
       "(assert (= outside_fragment 0))\n")
      "integer term sort";
    expect_no_fragment "NIA integer sort" "NIA"
      (script "NIA"
       "(declare-const x Int)\n" ^
       "(assert (= x 0))\n");
    expect_fragment "AUFNIRA bit-vector sort" "AUFNIRA"
      (script_for_checker "ALL"
       "(declare-const outside_fragment (_ BitVec 1))\n" ^
       "(assert (= outside_fragment #b0))\n")
      "bit-vector term sort";
    expect_no_fragment "UFBV bit-vector sort" "UFBV"
      (script "UFBV"
       "(declare-const x (_ BitVec 1))\n" ^
       "(assert (= x #b0))\n");
    expect_fragment "string sort unavailable" "QF_UF"
      (script_for_checker "ALL"
       "(declare-const s String)\n" ^
       "(assert (= s s))\n")
      "string term sort";
    expect_no_fragment "string sort available" "QF_S"
      (script "QF_S"
       "(declare-const s String)\n" ^
       "(assert (= s s))\n");
    expect_fragment "free sort unavailable" "LIA"
      (script_for_checker "ALL"
       "(declare-sort U 0)\n" ^
       "(declare-const u U)\n" ^
       "(assert (= u u))\n")
      "free sort";
    expect_no_fragment "free sort available" "QF_UF"
      (script "QF_UF"
       "(declare-sort U 0)\n" ^
       "(declare-const u U)\n" ^
       "(assert (= u u))\n");
    expect_fragment "pure bit-vector integer-only term" "UFBV"
      (script "UFBV"
       "(declare-const outside_fragment Int)\n" ^
       "(assert (= outside_fragment 0))\n" ^
       "")
      "integer atom";
    expect_fragment "mixed bit-vector integer atom" "QF_BV"
      (script "QF_BV"
       "(declare-const outside_fragment Int)\n" ^
       "(declare-const b (_ BitVec 1))\n" ^
       "(assert (and (= outside_fragment 0) (= b #b0)))\n")
      "integer atom";
    expect_no_fragment "bit-vector integer conversion" "QF_BV"
      (script "QF_BV"
       "(assert (= ((_ int_to_bv 1) 0) #b0))\n")
  end

fun smtlib_checked_replay_gap_diagnostics () =
  let
    fun replay_gap logic text =
      let
        val state = parse_smtlib_state text
      in
        SmtLib_Logics.checked_replay_unsupported_diagnostic logic
          (#assertions state)
      end
    fun expect_gap label logic text expected =
      case replay_gap logic text of
        SOME msg =>
          assert (contains expected msg,
            label ^ " diagnostic missed '" ^ expected ^ "': " ^ msg)
      | NONE => die (label ^ " checked replay gap was not detected")
    fun expect_no_gap label logic text =
      case replay_gap logic text of
        SOME msg =>
          die (label ^ " reported a spurious checked replay gap: " ^ msg)
      | NONE => ()
  in
    expect_gap "UnicodeStrings replay" "QF_SLIA"
      ("(set-logic QF_SLIA)\n" ^
       "(declare-const s String)\n" ^
       "(assert (str.prefixof s (str.++ s s)))\n" ^
       "(check-sat)\n")
      "theory:UnicodeStrings:checked-replay";
    expect_gap "RegLan replay" "QF_SLIA"
      ("(set-logic QF_SLIA)\n" ^
       "(declare-const s String)\n" ^
       "(assert (str.in_re s (str.to_re s)))\n" ^
       "(check-sat)\n")
      "theory:UnicodeStrings:RegLan:checked-replay";
    expect_gap "Z3 set replay" "ALL"
      ("(set-logic ALL)\n" ^
       "(declare-const x Int)\n" ^
       "(declare-const xs (Set Int))\n" ^
       "(assert (set.member x xs))\n" ^
       "(check-sat)\n")
      "theory:Z3_Extensions:seq-set-bag:checked-replay";
    expect_no_gap "nonlinear arithmetic replay" "NIA"
      ("(set-logic NIA)\n" ^
       "(declare-const x Int)\n" ^
       "(declare-const y Int)\n" ^
       "(assert (= (* x y) 1))\n" ^
       "(check-sat)\n");
    expect_no_gap "ground literal product replay" "QF_NIA"
      ("(set-logic QF_NIA)\n" ^
       "(assert (= (* 2 3) 6))\n" ^
       "(check-sat)\n");
    expect_no_gap "linear coefficient product replay" "QF_NIA"
      ("(set-logic QF_NIA)\n" ^
       "(declare-const x Int)\n" ^
       "(assert (= (* 2 x) 4))\n" ^
       "(check-sat)\n");
    expect_no_gap "integer equality replay" "QF_LIA"
      ("(set-logic QF_LIA)\n" ^
       "(declare-const x Int)\n" ^
       "(assert (= x x))\n" ^
       "(check-sat)\n")
  end

fun smtlib_typecheck_overloaded_and_indexed_success () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic ALL)\n" ^
       "(assert (and (= 1 1) (= true true) " ^
       "(= ((_ extract 1 0) #b101) #b01)))\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1,
    "overloaded/indexed typecheck script produced wrong assertion count");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "overloaded/indexed typecheck assertion did not parse as Bool")
end

fun smtlib_core_symbol_metadata_success () =
let
  val metadata = SmtLib_Logics.metadata_of_logic "QF_UF"
  val eq_symbol = find_symbol_metadata "Core" "term" "=" metadata
  val distinct_symbol = find_symbol_metadata "Core" "term" "distinct" metadata
  val and_symbol = find_symbol_metadata "Core" "term" "and" metadata
  val bool_symbol = find_symbol_metadata "Core" "sort" "Bool" metadata
  val eq_attrs = #attributes eq_symbol
  val distinct_attrs = #attributes distinct_symbol
  val and_attrs = #attributes and_symbol
in
  assert (metadata_is_official bool_symbol,
    "Bool sort metadata is not marked official");
  assert (#overloaded eq_attrs andalso #chainable eq_attrs,
    "equality metadata did not preserve overloaded/chainable attributes");
  assert (metadata_is_official eq_symbol,
    "equality metadata is not marked official");
  assert (#overloaded distinct_attrs andalso #pairwise distinct_attrs,
    "distinct metadata did not preserve overloaded/pairwise attributes");
  assert (#left_associative and_attrs,
    "and metadata did not record its official left-associative attribute")
end

fun smtlib_logic_metadata_extension_split_success () =
let
  val metadata = SmtLib_Logics.metadata_of_logic "QF_BV"
  val bvult_symbol = find_symbol_metadata "Fixed_Size_BitVectors" "term"
    "bvult" metadata
  val bvule_symbol = find_symbol_metadata "Fixed_Size_BitVectors" "term"
    "bvule" metadata
  val rotate_left_symbol = find_symbol_metadata "Fixed_Size_BitVectors"
    "term" "rotate_left" metadata
  val bvudiv_symbol = find_symbol_metadata "Fixed_Size_BitVectors" "term"
    "bvudiv" metadata
  val bvudiv_alias = find_symbol_metadata_source "Fixed_Size_BitVectors" "term"
    "bvudiv_i" metadata_is_extension metadata
  val rotate_left_attrs = #attributes rotate_left_symbol
  val bvudiv_attrs = #attributes bvudiv_symbol
in
  assert (metadata_is_official bvult_symbol,
    "official bit-vector metadata was not preserved");
  assert (metadata_is_official bvule_symbol,
    "official promoted bit-vector metadata was not preserved");
  assert (#indexed rotate_left_attrs,
    "indexed bit-vector metadata was not preserved");
  assert (#soundness_audit bvudiv_attrs,
    "bit-vector division was not marked for soundness audit");
  assert (metadata_is_extension bvudiv_alias,
    "Z3 bit-vector alias metadata was not preserved")
end

fun smtlib_core_arith_array_bv_symbol_coverage_success () =
let
  val lia_metadata = SmtLib_Logics.metadata_of_logic "QF_LIA"
  val bv_metadata = SmtLib_Logics.metadata_of_logic "QF_BV"
  val ax_metadata = SmtLib_Logics.metadata_of_logic "QF_AX"
  val int_symbols = ["**", "divisible"]
  val array_symbols = ["select", "store"]
  val bv_symbols = [
    "_", "concat", "extract", "bvnot", "bvneg", "bvand", "bvor",
    "bvxor", "bvxnor", "bvadd", "bvmul", "bvudiv", "bvurem",
    "bvsub", "bvnand", "bvnor", "bvcomp", "bvsdiv", "bvsrem",
    "bvsmod", "bvshl", "bvlshr", "bvashr", "repeat", "zero_extend",
    "sign_extend", "rotate_left", "rotate_right", "bvult", "bvule",
    "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
    "ubv_to_int", "sbv_to_int", "int_to_bv", "bvnego", "bvuaddo",
    "bvsaddo", "bvumulo", "bvsmulo", "bvusubo", "bvssubo",
    "bvsdivo"
  ]
  fun require_official metadata theory name =
    assert (metadata_is_official
      (find_symbol_metadata theory "term" name metadata),
      "missing official metadata for " ^ theory ^ "." ^ name)
in
  List.app (require_official lia_metadata "Ints") int_symbols;
  List.app (require_official ax_metadata "ArraysEx") array_symbols;
  List.app (require_official bv_metadata "Fixed_Size_BitVectors") bv_symbols
end

fun smtlib_advanced_symbol_coverage_success () =
let
  val all_metadata = SmtLib_Logics.metadata_of_logic "ALL"
  val fp_metadata = SmtLib_Logics.metadata_of_logic "QF_FP"
  val string_metadata = SmtLib_Logics.metadata_of_logic "QF_SLIA"
  val rm_sort = find_symbol_metadata "FloatingPoint" "sort" "RoundingMode"
    fp_metadata
  val fp_sort = find_symbol_metadata "FloatingPoint" "sort" "FloatingPoint"
    fp_metadata
  val to_fp = find_symbol_metadata "FloatingPoint" "term" "to_fp"
    fp_metadata
  val fp_to_ubv = find_symbol_metadata "FloatingPoint" "term" "fp.to_ubv"
    fp_metadata
  val string_sort = find_symbol_metadata "UnicodeStrings" "sort" "String"
    string_metadata
  val reglan_sort = find_symbol_metadata "UnicodeStrings" "sort" "RegLan"
    string_metadata
  val concat_symbol = find_symbol_metadata "UnicodeStrings" "term" "str.++"
    string_metadata
  val re_loop = find_symbol_metadata "UnicodeStrings" "term" "re.loop"
    string_metadata
  val seq_sort = find_symbol_metadata "Z3_Extensions" "sort" "Seq"
    all_metadata
  val set_member = find_symbol_metadata "Z3_Extensions" "term" "set.member"
    all_metadata
  val bag_count = find_symbol_metadata "Z3_Extensions" "term" "bag.count"
    all_metadata
in
  assert (metadata_is_official rm_sort,
    "RoundingMode sort metadata is not marked official");
  assert (#indexed (#attributes fp_sort),
    "FloatingPoint sort metadata did not preserve indexed attributes");
  assert (#indexed (#attributes to_fp) andalso #indexed (#attributes fp_to_ubv),
    "indexed floating-point conversion metadata was not preserved");
  assert (metadata_is_official string_sort,
    "String sort metadata is not marked official");
  assert (not (List.null (#parametric_sorts (#attributes reglan_sort))),
    "RegLan metadata did not preserve its parameter");
  assert (#left_associative (#attributes concat_symbol),
    "str.++ metadata did not record left associativity");
  assert (#indexed (#attributes re_loop),
    "regex loop metadata did not preserve indexed attributes");
  assert (metadata_is_extension seq_sort andalso
    metadata_is_extension set_member andalso metadata_is_extension bag_count,
    "Z3 sequence/set/bag metadata was not marked as extension")
end

fun smtlib_arith_array_parse_signatures_success () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic QF_ALIA)\n" ^
       "(declare-const x Int)\n" ^
       "(declare-const a (Array Int Int))\n" ^
       "(assert (and ((_ divisible 3) (** x 2)) " ^
       "(= (select (store a x 7) x) 7)))\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1,
    "arithmetic/array signature script produced the wrong assertion count");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "arithmetic/array signature assertion did not parse as Bool")
end

fun smtlib_bitvector_parse_signatures_success () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic QF_BV)\n" ^
       "(declare-const a (_ BitVec 8))\n" ^
       "(declare-const b (_ BitVec 8))\n" ^
       "(assert (and " ^
       "(= (_ bv3 8) #x03) " ^
       "(= (concat #b1010 #b0101) a) " ^
       "(= ((_ extract 3 0) a) #b0011) " ^
       "(= (bvnot a) b) (= (bvneg a) b) " ^
       "(= (bvand a b) a) (= (bvor a b) a) " ^
       "(= (bvxor a b) a) (= (bvxnor a b) a) " ^
       "(= (bvadd a b) a) (= (bvmul a b) a) " ^
       "(= (bvudiv a b) a) (= (bvurem a b) a) " ^
       "(= (bvsub a b) a) (= (bvnand a b) a) " ^
       "(= (bvnor a b) a) (= (bvcomp a b) #b1) " ^
       "(= (bvsdiv a b) a) (= (bvsrem a b) a) " ^
       "(= (bvsmod a b) a) (= (bvshl a b) a) " ^
       "(= (bvlshr a b) a) (= (bvashr a b) a) " ^
       "(= ((_ repeat 2) #b10) #b1010) " ^
       "(= ((_ zero_extend 2) #b10) #b0010) " ^
       "(= ((_ sign_extend 2) #b10) #b1110) " ^
       "(= ((_ rotate_left 1) a) b) " ^
       "(= ((_ rotate_right 1) a) b) " ^
       "((_ @bit_of 3) a) " ^
       "(= (@bbterm ((_ @bit_of 0) a) ((_ @bit_of 1) a) " ^
       "((_ @bit_of 2) a) ((_ @bit_of 3) a) ((_ @bit_of 4) a) " ^
       "((_ @bit_of 5) a) ((_ @bit_of 6) a) ((_ @bit_of 7) a)) a) " ^
       "(bvult a b) (bvule a b) (bvugt a b) (bvuge a b) " ^
       "(bvslt a b) (bvsle a b) (bvsgt a b) (bvsge a b) " ^
       "(= (ubv_to_int a) 0) (= (sbv_to_int a) 0) " ^
       "(= ((_ int_to_bv 8) 3) a) " ^
       "(bvnego a) (bvuaddo a b) (bvsaddo a b) " ^
       "(bvumulo a b) (bvsmulo a b) (bvusubo a b) " ^
       "(bvssubo a b) (bvsdivo a b)))\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1,
    "bit-vector signature script produced the wrong assertion count");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "bit-vector signature assertion did not parse as Bool")
end

fun smtlib_floatingpoint_parse_signatures_success () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic QF_FP)\n" ^
       "(declare-const a Float32)\n" ^
       "(declare-const b Float32)\n" ^
       "(assert (and " ^
       "(= (fp.add RNE a b) a) " ^
       "(= (fp.sub RTZ a b) b) " ^
       "(= (fp.sqrt RTP a) b) " ^
       "(fp.eq (_ +zero 8 24) (_ -zero 8 24)) " ^
       "(fp.isNaN (_ NaN 8 24)) " ^
       "(= ((_ fp.to_ubv 8) a) #x00)))\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1,
    "floating-point signature script produced the wrong assertion count");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "floating-point signature assertion did not parse as Bool")
end

fun smtlib_string_regex_parse_signatures_success () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic QF_SLIA)\n" ^
       "(declare-const s String)\n" ^
       "(declare-const t String)\n" ^
       "(assert (and " ^
       "(= (str.++ s t) s) " ^
       "(= (str.len s) 0) " ^
       "(str.< s t) (str.<= s t) " ^
       "(= (str.at s 0) t) " ^
       "(= (str.substr s 0 1) t) " ^
       "(str.prefixof s t) (str.suffixof s t) (str.contains s t) " ^
       "(= (str.indexof s t 0) 0) " ^
       "(= (str.replace s t (str.from_code 65)) s) " ^
       "(str.in_re s (re.* (str.to_re t))) " ^
       "(str.in_re s ((_ re.loop 1 3) (re.union (str.to_re s) re.allchar)))))\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1,
    "string/regex signature script produced the wrong assertion count");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "string/regex signature assertion did not parse as Bool")
end

fun smtlib_z3_extension_parse_signatures_success () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic ALL)\n" ^
       "(declare-const xs (Seq Int))\n" ^
       "(declare-const ys (Seq Int))\n" ^
       "(declare-const s (Set Int))\n" ^
       "(declare-const b (Bag Int))\n" ^
       "(assert (and " ^
       "(= (seq.++ xs ys) xs) (= (seq.len xs) 0) " ^
       "(seq.contains xs ys) " ^
       "(set.member 1 (set.insert 1 s)) " ^
       "(set.subset (set.union s s) (set.intersect s s)) " ^
       "(= (bag.count 1 (bag.union_disjoint b b)) 0)))\n" ^
       "(exit)\n")
in
  assert (List.length assertions = 1,
    "Z3 extension signature script produced the wrong assertion count");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "Z3 extension signature assertion did not parse as Bool")
end

fun smtlib_scoped_logic_dictionary_success () =
let
  val logics = [
    "ALL", "ALIA", "ALIRA", "ANIA", "ANIRA", "AUFLIA", "AUFLIRA",
    "AUFNIRA", "BV", "LIA", "LRA", "NIA", "NRA", "UF",
    "UFBV", "UFIDL", "UFLIA", "UFLRA", "UFNIA", "UFNRA",
    "QF_ABV", "QF_ALIA", "QF_ALRA", "QF_ANIA", "QF_ANRA",
    "QF_AUFBV", "QF_AUFLIA", "QF_AUFLIRA", "QF_AUFNIA",
    "QF_AUFNIRA", "QF_AX", "QF_BV", "QF_IDL", "QF_LIA",
    "QF_LIRA", "QF_LRA", "QF_NIA", "QF_NIRA", "QF_NRA",
    "QF_RDL", "QF_UF", "QF_UFBV", "QF_UFIDL", "QF_UFLIA",
    "QF_UFLIRA", "QF_UFLRA", "QF_UFNIRA", "QF_UFNRA",
    "QF_S", "QF_SLIA", "QF_SNIA", "QF_FP", "QF_FPBV",
    "QF_BVFP", "QF_UFFP", "QF_UFBVFP"
  ]
  val legacy_linear_logics = [
    "ALIA", "ALIRA", "AUFLIA", "AUFLIRA", "LIA", "LRA",
    "QF_ALIA", "QF_ALRA", "QF_AUFLIA", "QF_AUFLIRA",
    "QF_IDL", "QF_LIA", "QF_LIRA", "QF_LRA", "QF_RDL",
    "QF_UFIDL", "QF_UFLIA", "QF_UFLIRA", "QF_UFLRA",
    "UFIDL", "UFLIA", "UFLRA"
  ]
  fun require_logic logic =
    let
      val _ = SmtLib_Logics.parsedicts_of_logic logic
      val metadata = SmtLib_Logics.metadata_of_logic logic
      val _ = SmtLib_Logics.logic_fragment_of_logic logic
      val was_legacy_linear =
        List.exists (fn linear_logic => logic = linear_logic)
          legacy_linear_logics
    in
      assert (not (List.null metadata),
        "logic metadata was empty for " ^ logic);
      assert (not was_legacy_linear orelse
              SmtLib_Logics.is_linear_arith_logic logic,
        "legacy linear-arithmetic logic no longer classified linear: " ^
        logic)
    end
in
  List.app require_logic logics
end

fun smtlib_translation_logic_inference_success () =
let
  fun expect_logic expected tm =
    let
      val (logic, set_logic, _, _) = inferred_logic tm
    in
      assert (logic = expected,
        "expected inferred logic " ^ expected ^ ", got " ^ logic);
      assert (set_logic = "(set-logic " ^ expected ^ ")\n",
        "set-logic command did not match inferred logic " ^ expected)
    end
in
  expect_logic "QF_LIA" ``(x:int) <= x + 1``;
  expect_logic "QF_NIA" ``(x:int) * y = y * x``;
  expect_logic "QF_BV" ``(x:word32) && y = y && x``;
  expect_logic "QF_AX" ``(P:'a -> bool) x``;
  expect_logic "QF_AX" ``(f:'a -> 'b) x = f x``;
  expect_logic "ALL" ``!(x:'a). (P:'a -> bool) x``
end

fun smtlib_translation_records_success () =
let
  val (logic, _, records, translation) = inferred_logic ``(P:'a -> bool) x``
  val _ = assert (logic = "QF_AX", "record test expected QF_AX")
  val has_logic =
    List.exists (fn SmtLib.LogicSelection {logic = "QF_AX", ...} => true
      | _ => false) records
  val has_type_decl =
    List.exists (fn SmtLib.TypeDeclaration {smt_name, ...} =>
        String.isPrefix "t" smt_name
      | _ => false) records
  val has_term_decl =
    List.exists (fn SmtLib.TermDeclaration {arity = 0, smt_name, range_sort, ...} =>
        String.isPrefix "v" smt_name
        andalso String.isPrefix "(Array " range_sort
      | _ => false) records
  val has_encoded_symbol =
    List.exists (fn SmtLib.EncodedSymbol {smt_symbol = "not", ...} => true
      | SmtLib.EncodedSymbol {smt_symbol = "=", ...} => true
      | _ => false) records
  val _ = SmtLib.parser_dicts_for_translation translation
in
  assert (has_logic, "translation records did not include selected logic");
  assert (has_type_decl, "translation records did not include type declaration");
  assert (has_term_decl, "translation records did not include array term declaration");
  assert (has_encoded_symbol, "translation records did not include encoded symbol")
end

fun smtlib_extended_hol_encoding_records_success () =
let
  val s = Term.mk_var ("s", stringSyntax.string_ty)
  val t = Term.mk_var ("t", stringSyntax.string_ty)
  val term = boolSyntax.mk_eq
    (stringSyntax.mk_strcat (s, t), stringSyntax.mk_strcat (t, s))
  val (logic, _, records, translation) = inferred_logic term
  val has_string_encoding =
    List.exists
      (fn SmtLib.HOLTheoryEncoding {
            feature, smt_theory = "UnicodeStrings",
            mode = SmtLib.NativeSMTLIB, parse = true,
            typecheck = true, translate = true, replay = false, ...} =>
            contains "HOL strings" feature
        | _ => false) records
  val has_concat_symbol =
    List.exists (fn SmtLib.EncodedSymbol {smt_symbol = "str.++", ...} =>
        true
      | _ => false) records
  val has_fp_matrix_row =
    List.exists
      (fn SmtLib.HOLTheoryEncoding {
            smt_theory = "FloatingPoint", translate = false,
            replay = false, proof_obligation, ...} =>
            contains "NaN" proof_obligation
        | _ => false) records
  val has_bag_matrix_row =
    List.exists
      (fn SmtLib.HOLTheoryEncoding {
            smt_theory = "Z3 sequence/set/bag extensions",
            translate = false, replay = false, notes, ...} =>
            contains "Seq/Set/Bag" notes
        | _ => false) records
  val _ = SmtLib.parser_dicts_for_translation translation
in
  assert (logic = "QF_S",
    "string translation expected QF_S, got " ^ logic);
  assert (has_string_encoding,
    "translation records lacked native HOL string encoding row");
  assert (has_concat_symbol,
    "translation records lacked str.++ encoded symbol");
  assert (has_fp_matrix_row,
    "translation records lacked FloatingPoint proof-obligation row");
  assert (has_bag_matrix_row,
    "translation records lacked sequence/set/bag matrix row")
end

fun smtlib_higher_order_translation_abstraction_success () =
let
  val (logic, _, records, translation) =
    inferred_logic ``(H:('a -> 'b) -> bool) f``
  val has_array_sort_decl =
    List.exists
      (fn SmtLib.TermDeclaration {arity = 0, range_sort, hol_term, ...} =>
            term_is_var_named "H" hol_term andalso
            String.isPrefix "(Array (Array " range_sort
        | _ => false) records
  val has_h_decl =
    List.exists
      (fn SmtLib.TermDeclaration {arity = 0, hol_term, ...} =>
            term_is_var_named "H" hol_term
        | _ => false) records
  val _ = SmtLib.parser_dicts_for_translation translation
in
  assert (logic = "QF_AX",
    "higher-order abstraction expected QF_AX, got " ^ logic);
  assert (has_array_sort_decl,
    "higher-order abstraction lacked nested array sort declaration");
  assert (has_h_decl,
    "higher-order abstraction lacked a declaration for H")
end

fun smtlib_translation_shape_matrix_success () =
let
  fun smtlib_text goal =
    let val (_, strings) = SmtLib.goal_to_SmtLib_translation NONE goal
    in String.concat strings end
  fun assert_snippet test_name text snippet =
    assert (contains snippet text,
      "translation matrix case '" ^ test_name ^
      "' did not emit expected SMT-LIB snippet '" ^ snippet ^
      "'\nSMT-LIB:\n" ^ text)
  fun expect_shape (test_name, goal, snippets) =
    let val text = smtlib_text goal
    in List.app (assert_snippet test_name text) snippets end
  val cases = [
    ("bool-sort-and-equality", ([], ``(p:bool) = q``),
      ["(set-logic QF_UF)\n", "(declare-fun v0 () Bool)\n",
       "(assert (not (= v0 v1)))"]),
    ("num-uninterpreted-sort", ([], ``42n = n``),
      ["(set-logic QF_UF)\n", "(declare-sort t0 0)\n",
       "(declare-fun v0 (t0) t0)"]),
    ("int-linear-arithmetic", ([], ``(x:int) + 7 <= y - ~3``),
      ["(set-logic QF_LIA)\n", "(declare-fun v0 () Int)\n",
       "(<= (+ v0 7) (- v1 (- 3)))"]),
    ("real-nonlinear-arithmetic", ([], ``(x:real) + 7r <= y * 2r``),
      ["(set-logic QF_NRA)\n", "(declare-fun v0 () Real)\n",
       "(<= (+ v0 7.0) (* v1 2.0))"]),
    ("word-bitvectors", ([], ``((x:word8) && 3w) = (y || 1w)``),
      ["(set-logic QF_BV)\n", "(_ BitVec 8)",
       "(= (bvand v0 (_ bv3 8)) (bvor v1 (_ bv1 8)))"]),
    ("string-native-sort-and-concat", ([],
       ``STRCAT (s:string) t = STRCAT t s``),
      ["(set-logic QF_S)\n", "(declare-fun v0 () String)\n",
       "(= (str.++ v0 v1) (str.++ v1 v0))"]),
    ("list-constructor-current-uf", ([],
       ``CONS (x:int) xs = CONS y ys``),
      ["(set-logic QF_UFLIA)\n", "(declare-sort t0 0)\n",
       "(declare-fun v0 (Int t0) t0)"]),
    ("function-application-arrays", ([],
       ``(f:'a -> 'b) x = g y``),
      ["(set-logic QF_AX)\n", "(declare-fun v0 () (Array t0 t1))",
       "(declare-fun v2 () (Array t2 t1))",
       "(= (select v0 v1) (select v2 v3))"]),
    ("tuple-selector-current-uf", ([],
       ``FST (p:int # bool) <= FST p + 1``),
      ["(set-logic QF_UFLIA)\n", "(declare-sort t0 0)",
       "(declare-fun v0 (t0) Int)"]),
    ("sets-as-predicates-current-uf", ([],
       ``(s:'a -> bool) x``),
      ["(set-logic QF_AX)\n", "(declare-fun v0 () (Array t0 Bool))",
       "(assert (not (select v0 v1)))"])
  ]
in
  List.app expect_shape cases
end

fun smtlib_term_translation_branch_matrix_success () =
let
  fun smtlib_text goal =
    let val (_, strings) = SmtLib.goal_to_SmtLib_translation NONE goal
    in String.concat strings end
  fun assert_has name text snippet =
    assert (contains snippet text,
      "term branch case '" ^ name ^ "' missed SMT-LIB snippet '" ^
      snippet ^ "'\nSMT-LIB:\n" ^ text)
  fun expect (name, goal, snippets) =
    let val text = smtlib_text goal
    in List.app (assert_has name text) snippets end
  val cases = [
    ("variables-constants-applications", ([],
       ``(P:'a -> bool) x /\ T /\ ~F``),
      ["(declare-fun v0 () (Array t0 Bool))",
       "(and (select v0 v1) (and true (not false)))"]),
    ("quantifier-binder", ([], ``!x:int. x <= x + 1``),
      ["(set-logic LIA)\n", "(forall ((b0 Int)) (<= b0 (+ b0 1)))"]),
    ("let-binder", ([],
       ``let x = (y:int) + 1 in x <= y + 1``),
      ["(let ((b0 (+ v0 1))) (<= b0 (+ v0 1)))"]),
    ("conditional", ([], ``(if p then q else ~q):bool``),
      ["(ite v0 v1 (not v1))"]),
    ("core-xor", ([], ``HolSmt$xor p q``),
      ["(set-logic QF_UF)\n", "(xor v0 v1)"]),
    ("distinct-like-not-equal", ([],
       ``((x:'a) = y) <=> ~(x <> y)``),
      ["(= (= v0 v1) (not (not (= v0 v1))))"]),
    ("integer-ediv-emod", ([],
       ``integer$ediv (x:int) y + integer$emod x y = x``),
      ["(+ (div v0 v1) (mod v0 v1))"]),
    ("real-division-preprocessed-symbol", ([],
       ``HolSmt$smt_rdiv (x:real) y = x``),
      ["(set-logic QF_LRA)\n", "(= (/ v0 v1) v0)"]),
    ("word-casts", ([],
       ``((w2w (x:word8)):word16) = sw2sw x``),
      ["((_ zero_extend 8) v0)", "((_ sign_extend 8) v0)"]),
    ("string-operations", ([],
       ``isPREFIX (s:string) (STRCAT s t) /\ (s < t) /\ (s <= t)``),
      ["str.prefixof", "str.++", "str.<", "str.<="]),
    ("datatype-constructor-current-uf", ([],
       ``SOME (x:int) = SOME y``),
      ["(set-logic QF_UFLIA)\n", "(declare-sort t0 0)",
       "(declare-fun v0 (Int) t0)"])
  ]
in
  List.app expect cases
end

fun smtlib_preprocessing_and_gap_diagnostics () =
let
  fun expect_translation_error label term expected =
    let
      val _ = SmtLib.goal_to_SmtLib_translation NONE ([], term)
    in
      die ("expected translation diagnostic for " ^ label)
    end
    handle Feedback.HOL_ERR holerr =>
      let val msg = Feedback.message_of holerr
      in
        assert (contains expected msg,
          label ^ " diagnostic did not include '" ^ expected ^ "': " ^ msg)
      end
  fun preprocessing_removes label term forbidden =
    let
      val (subgoals, _) = SmtLib.SIMP_TAC true ([], term)
      val rendered = String.concatWith "\n"
        (List.map (fn (_, t) => term_with_types t) subgoals)
    in
      List.app
        (fn snippet =>
          assert (not (contains snippet rendered),
            label ^ " preprocessing left '" ^ snippet ^
            "' in subgoals:\n" ^ rendered))
        forbidden
    end
    handle Feedback.HOL_ERR holerr =>
      die (label ^ " simplification/preprocessing tactic failed: " ^
        Feedback.message_of holerr)
  fun preprocessing_solves label term =
    let
      val (subgoals, _) = SmtLib.SIMP_TAC true ([], term)
    in
      assert (List.null subgoals,
        label ^ " preprocessing left " ^
        Int.toString (List.length subgoals) ^ " subgoal(s)")
    end
    handle Feedback.HOL_ERR holerr =>
      die (label ^ " simplification/preprocessing tactic failed: " ^
        Feedback.message_of holerr)
  val rdiv_thm = Hol_pp.thm_to_string HolSmtTheory.real_div_smt_rdiv
in
  ignore (inferred_logic ``(H:('a -> 'b) -> bool) f``);
  ignore (inferred_logic ``(f:int -> bool) = g``);
  expect_translation_error "datatype case selector current gap"
    ``(case (opt:int option) of NONE => 0i | SOME x => x) = 0i``
    "unsupported higher-order rator expression";
  assert (contains "if y = 0 then 0 else smt_rdiv x y" rdiv_thm,
    "real division preprocessing theorem did not expose smt_rdiv shape: " ^
    rdiv_thm);
  preprocessing_removes "let/lambda/beta validation"
    ``(let f = (\x:int. x + 1) in f 2) = 3`` ["let", "\\"];
  preprocessing_removes "pair selector simplification validation"
    ``FST ((x:int), p) = x`` ["FST"];
  preprocessing_solves "array read-over-write preprocessing"
    ``((i =+ e) (a:'i -> 'e)) i = e``;
  preprocessing_solves "array write-over-write preprocessing"
    ``(i =+ e2) ((i =+ e1) (a:'i -> 'e)) = (i =+ e2) a``;
  preprocessing_removes "array extensionality preprocessing"
    ``(!i:int. (a:int -> bool) i = b i) ==> (a = b)`` ["a = b"]
end

fun smtlib_roundtrip_current_theories_success () =
let
  fun roundtrip name goal = assert_goal_roundtrip name goal
in
  roundtrip "integers" ([],
    ``(x:int) + 7 <= y - ~3``);
  roundtrip "reals" ([],
    ``(x:real) + 7r <= y * 2r``);
  roundtrip "num-numerals-uninterpreted" ([],
    ``42n = n``);
  roundtrip "words-bitvectors" ([],
    ``((x:word8) && 3w) = (y || 1w)``);
  roundtrip "uninterpreted-functions-and-equality" ([],
    ``(f:'a -> 'b) x = g y``);
  roundtrip "core-xor" ([],
    ``HolSmt$xor p q``);
  roundtrip "function-application-array-encoding" ([],
    ``(f:'a -> 'b) x = f x``);
  roundtrip "mixed-int-word-uf" ([``(x:int) <= y``],
    ``((x:int) + 1 <= y + 2) /\ ((w:word8) + 1w = w + 1w) /\
      (P:'a -> bool) a``)
end

fun smtlib_roundtrip_known_gap_matrix_success () =
let
  val matrix = [
    {encoding = "integers/reals/numerals",
     status = "round-trips through parser_dicts_for_translation"},
    {encoding = "words/bit-vectors",
     status = "round-trips through parser_dicts_for_translation"},
    {encoding = "uninterpreted functions/equality",
     status = "round-trips through parser_dicts_for_translation"},
    {encoding = "SMT ArraysEx select/store",
     status = "round-trips through native SMT ArraysEx select/store"},
    {encoding = "strings/UnicodeStrings",
     status = "HOL string sort and selected string operations translate with \
              \native SMT-LIB records; replay remains unsupported"},
    {encoding = "floating point, regex, datatypes, sequences, sets, bags",
     status = "parse/typecheck matrix entries only unless a HOLTheoryEncoding \
              \record explicitly marks translate=true; replay remains false"}
  ]
  fun has_array_gap {encoding, status} =
    encoding = "SMT ArraysEx select/store" andalso
    String.isSubstring "round-trips" status andalso
    String.isSubstring "select/store" status
  fun has_advanced_gap {encoding, status} =
    encoding = "floating point, regex, datatypes, sequences, sets, bags" andalso
    String.isSubstring "parse/typecheck" status andalso
    String.isSubstring "replay remains false" status
in
  assert (List.exists has_array_gap matrix,
    "round-trip matrix lacks explicit ArraysEx select/store support row");
  assert (List.exists has_advanced_gap matrix,
    "round-trip matrix lacks explicit advanced-theory diagnostic")
end

fun parse_z3_proof_string version contents =
let
  val dicts = SmtLib_Logics.parsedicts_of_logic "ALL"
  val instream = TextIO.openString contents
in
  Z3_ProofParser.parse_stream_with_version dicts version instream
end

fun z3_proof_registry_metadata_success () =
  case Z3_Proof.lookup_rule "4.12.4" "mp-eq" of
    SOME ({name, premise_shape, conclusion_shape, replay_handler, ...}
          : Z3_Proof.proof_rule) =>
      (assert (name = "mp~", "mp-eq alias did not normalize to mp~");
       assert (premise_shape = Z3_Proof.TwoPremises,
        "mp~ registry premise shape is not TwoPremises");
       assert (conclusion_shape = Z3_Proof.BooleanConclusion,
        "mp~ registry conclusion shape is not BooleanConclusion");
       assert (replay_handler = "mp_eq",
        "mp~ registry replay handler is not mp_eq"))
  | NONE => die "FAIL: mp-eq alias was not found in Z3 proof rule registry"

fun z3_proof_parser_normalizes_rule_alias_success () =
let
  val proof = parse_z3_proof_string "4.12.4"
    "((proof (mp-eq (asserted false) (asserted (= false false)) false)))"
in
  case Redblackmap.peek (Z3_Proof.proof_steps proof, 0) of
    SOME (Z3_Proof.MP_EQ _) => ()
  | SOME _ => die "FAIL: mp-eq proof rule parsed to unexpected constructor"
  | NONE => die "FAIL: mp-eq proof did not define root proof step"
end

fun z3_proof_parser_erases_proof_bind_success () =
let
  val proof = parse_z3_proof_string "4.12.4"
    "((proof (proof-bind (asserted false))))"
in
  case Redblackmap.peek (Z3_Proof.proof_steps proof, 0) of
    SOME (Z3_Proof.ASSERTED _) => ()
  | SOME _ => die "FAIL: proof-bind parsed to unexpected constructor"
  | NONE => die "FAIL: proof-bind proof did not define root proof step"
end

fun z3_proof_parser_th_lemma_metadata_success () =
let
  val proof = parse_z3_proof_string "4.12.4"
    "((proof ((_ th-lemma arith farkas 1 2) true)))"
in
  case Redblackmap.peek (Z3_Proof.proof_steps proof, 0) of
    SOME (Z3_Proof.TH_LEMMA_ARITH
      ({theory, subkind, indices}, [], concl)) =>
        (assert (theory = "arith",
          "th-lemma metadata did not preserve theory");
         assert (subkind = SOME "farkas",
         "th-lemma metadata did not preserve subkind");
         assert (indices = ["1", "2"],
          "th-lemma metadata did not preserve proof indices: [" ^
          String.concatWith ", " indices ^ "]");
         assert (concl ~~ ``T``,
          "th-lemma metadata test parsed unexpected conclusion"))
  | SOME _ => die "FAIL: indexed th-lemma parsed to unexpected constructor"
  | NONE => die "FAIL: indexed th-lemma proof did not define root proof step"
end

fun z3_proof_parser_advanced_th_lemma_metadata_success () =
let
  val proof = parse_z3_proof_string "4.13.0"
    "((proof ((_ th-lemma fp eq-propagate 4) false)))"
in
  case Redblackmap.peek (Z3_Proof.proof_steps proof, 0) of
    SOME (Z3_Proof.TH_LEMMA_ADVANCED
      ({theory, subkind, indices}, [], concl)) =>
        (assert (theory = "fp",
          "advanced th-lemma metadata did not preserve theory");
         assert (subkind = SOME "eq-propagate",
          "advanced th-lemma metadata did not preserve subkind");
         assert (indices = ["4"],
          "advanced th-lemma metadata did not preserve proof indices: [" ^
          String.concatWith ", " indices ^ "]");
         assert (concl ~~ ``F``,
          "advanced th-lemma metadata test parsed unexpected conclusion"))
  | SOME _ => die "FAIL: advanced th-lemma parsed to unexpected constructor"
  | NONE => die "FAIL: advanced th-lemma proof did not define root proof step"
end

fun z3_proof_parser_unknown_rule_diagnostic () =
  (ignore (parse_z3_proof_string "4.12.4"
    "((proof (new-z3-rule false)))");
   die "FAIL: unknown Z3 proof rule parsed successfully")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring "registry lookup failed" msg,
        "unknown-rule diagnostic did not report registry lookup failure: " ^
        msg);
      assert (String.isSubstring "new-z3-rule" msg,
        "unknown-rule diagnostic did not include rule name: " ^ msg);
      assert (String.isSubstring "4.12.4" msg,
        "unknown-rule diagnostic did not include Z3 version: " ^ msg)
    end

fun replay_z3_proof_string contents =
  Z3_ProofReplay.replay_root_for_test
    (parse_z3_proof_string "4.12.4" contents)

fun assert_replays_raw_z3_proof_rule (name, proof_text, expected) =
let
  val thm = replay_z3_proof_string proof_text
  val actual = Thm.concl thm
in
  assert (actual ~~ expected,
    "raw Z3 proof rule " ^ name ^ " replayed to " ^
    term_with_types actual ^ ", expected " ^ term_with_types expected)
end

fun profile_call_count name =
  case List.find (fn (result_name, _) => result_name = name)
      (Profile.results ()) of
    SOME (_, info) => #n info
  | NONE => 0

fun assert_nnf_replays_without_metis (name, proof_text, expected) =
let
  val () = Profile.reset_all ()
  val thm = replay_z3_proof_string proof_text
  val actual = Thm.concl thm
  val structural = profile_call_count "nnf[structural]"
  val fallback = profile_call_count "nnf[metis-fallback]"
in
  assert (actual ~~ expected,
    "NNF proof " ^ name ^ " replayed to " ^ term_with_types actual ^
    ", expected " ^ term_with_types expected);
  assert (structural > 0,
    "NNF proof " ^ name ^ " did not use structural NNF replay");
  assert (fallback = 0,
    "NNF proof " ^ name ^ " used METIS fallback " ^
    Int.toString fallback ^ " time(s)")
end

fun assert_trans_star_replays_without_metis (name, proof_text, expected) =
let
  val () = Profile.reset_all ()
  val thm = replay_z3_proof_string proof_text
  val actual = Thm.concl thm
  val exact = profile_call_count "trans_star[exact]"
  val fallback = profile_call_count "trans_star[metis-fallback]"
in
  assert (actual ~~ expected,
    "trans* proof " ^ name ^ " replayed to " ^ term_with_types actual ^
    ", expected " ^ term_with_types expected);
  assert (exact > 0,
    "trans* proof " ^ name ^ " did not use exact chain replay");
  assert (fallback = 0,
    "trans* proof " ^ name ^ " used METIS fallback " ^
    Int.toString fallback ^ " time(s)")
end

fun z3_core_proof_rule_replay_minimal_raw_success () =
let
  val cases = [
    ("and-elim",
      "((proof (and-elim (asserted (and false true)) false)))",
      ``F``),
    ("apply-def",
      "((declare-fun z () Bool) \
        \(proof (apply-def (intro-def (= z false)) (= false z))))",
      ``F = (z:bool)``),
    ("asserted",
      "((proof (asserted false)))",
      ``F``),
    ("commutativity",
      "((proof (commutativity (= (= false true) (= true false)))))",
      ``(F = T) = (T = F)``),
    ("def-axiom",
      "((proof (def-axiom (or (not (and false true)) false))))",
      ``~(F /\ T) \/ F``),
    ("elim-unused",
      "((proof (elim-unused (= (forall ((x Bool)) false) false))))",
      ``(!x:bool. F) = F``),
    ("hypothesis",
      "((proof (hypothesis false)))",
      ``F``),
    ("iff-false",
      "((proof (iff-false (asserted (not true)) (= true false))))",
      ``T = F``),
    ("iff-true",
      "((proof (iff-true (asserted true) (= true true))))",
      ``T = T``),
    ("intro-def",
      "((declare-fun z () Bool) (proof (intro-def (= z false))))",
      ``(z:bool) = F``),
    ("lemma",
      "((proof (lemma (hypothesis false) (not false))))",
      ``~F``),
    ("monotonicity",
      "((proof (monotonicity (refl (= false false)) (= (not false) (not false)))))",
      ``~F = ~F``),
    ("mp",
      "((proof (mp (asserted true) (asserted (implies true false)) false)))",
      ``F``),
    ("mp~",
      "((proof (mp~ (asserted true) (asserted (= true false)) false)))",
      ``F``),
    ("nnf-neg",
      "((proof (nnf-neg (asserted false) false)))",
      ``F``),
    ("nnf-pos",
      "((proof (nnf-pos (asserted false) false)))",
      ``F``),
    ("not-or-elim",
      "((proof (not-or-elim (asserted (not (or false true))) (not true))))",
      ``~T``),
    ("quant-inst",
      "((proof ((_ quant-inst false) (or (not (forall ((x Bool)) x)) false))))",
      ``~(!x:bool. x) \/ F``),
    ("quant-intro",
      "((proof (quant-intro (refl (= false false)) \
        \(= (forall ((x Bool)) false) (forall ((x Bool)) false)))))",
      ``(!x:bool. F) = (!x:bool. F)``),
    ("refl",
      "((proof (refl (= false false))))",
      ``F = F``),
    ("rewrite",
      "((proof (rewrite (= false false))))",
      ``F = F``),
    ("rewrite/bvcomp",
      "((declare-fun a () (_ BitVec 8)) (declare-fun b () (_ BitVec 8)) \
        \(proof (rewrite (= (bvcomp a b) (ite (= a b) #b1 #b0)))))",
      ``word_compare (a:word8) b = if a = b then 1w else 0w:word1``),
    ("rewrite/bvsmod_i",
      "((declare-fun a () (_ BitVec 8)) (declare-fun b () (_ BitVec 8)) \
        \(proof (rewrite (= (bvsmod a b) (bvsmod_i a b)))))",
      ``word_smod (a:word8) b = word_smod a b``),
    ("sk",
      "((declare-fun z () Bool) (proof (sk (= (exists ((x Bool)) x) z))))",
      ``(?x:bool. x) = z``),
    ("symm",
      "((proof (symm (asserted (= false true)) (= true false))))",
      ``T = F``),
    ("trans",
      "((proof (trans (asserted (= false true)) \
        \(asserted (= true false)) (= false false))))",
      ``F = F``),
    ("trans*",
      "((proof (trans* (asserted (= false true)) \
        \(asserted (= true false)) (= false false))))",
      ``F = F``),
    ("true-axiom",
      "((proof (true-axiom true)))",
      ``T``),
    ("unit-resolution",
      "((proof (unit-resolution (asserted (or false true)) \
        \(asserted (not true)) false)))",
      ``F``)
  ]
in
  List.app assert_replays_raw_z3_proof_rule cases
end

fun z3_trans_star_chain_search_replay_no_metis_success () =
let
  val cases = [
    ("straight chain",
      "((declare-fun a () Bool) (declare-fun b () Bool) \
        \(declare-fun c () Bool) (declare-fun d () Bool) \
        \(proof (trans* (asserted (= a b)) (asserted (= b c)) \
        \(asserted (= c d)) (= a d))))",
      ``(a:bool) = d``),
    ("chain with symmetry",
      "((declare-fun a () Bool) (declare-fun b () Bool) \
        \(declare-fun c () Bool) (declare-fun d () Bool) \
        \(proof (trans* (asserted (= a b)) (asserted (= c b)) \
        \(asserted (= c d)) (= a d))))",
      ``(a:bool) = d``),
    ("chain with irrelevant premise",
      "((declare-fun a () Bool) (declare-fun b () Bool) \
        \(declare-fun c () Bool) (declare-fun x () Bool) \
        \(declare-fun y () Bool) \
        \(proof (trans* (asserted (= a b)) (asserted (= x y)) \
        \(asserted (= b c)) (= a c))))",
      ``(a:bool) = c``)
  ]
in
  List.app assert_trans_star_replays_without_metis cases
end

fun z3_trans_star_chain_search_no_path_diagnostic () =
  (ignore (replay_z3_proof_string
    "((declare-fun a () Bool) (declare-fun b () Bool) \
      \(declare-fun c () Bool) (declare-fun d () Bool) \
      \(proof (trans* (asserted (= a b)) (asserted (= c d)) (= a d))))");
   die "FAIL: trans* proof without an equality path replayed successfully")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring "no equality path" msg,
        "trans* no-path diagnostic did not explain missing path: " ^ msg);
      assert (String.isSubstring "a" msg andalso String.isSubstring "d" msg,
        "trans* no-path diagnostic did not include endpoints: " ^ msg)
    end

fun z3_nnf_structural_replay_no_metis_success () =
let
  val cases = [
    ("nnf-pos observed identity",
      "((declare-fun a () Bool) \
        \(proof (nnf-pos (asserted (= a a)) (= a a))))",
      ``(a:bool) = a``),
    ("nnf-pos implication premise congruence",
      "((declare-fun a () Bool) (declare-fun b () Bool) \
        \(declare-fun na () Bool) \
        \(proof (nnf-pos (asserted (= (not a) na)) \
        \(= (implies a b) (or na b)))))",
      ``((a:bool) ==> b) = (na \/ b)``),
    ("nnf-neg and",
      "((declare-fun a () Bool) (declare-fun b () Bool) \
        \(declare-fun na () Bool) (declare-fun nb () Bool) \
        \(proof (nnf-neg (asserted (= (not a) na)) \
        \(asserted (= (not b) nb)) \
        \(= (not (and a b)) (or na nb)))))",
      ``~((a:bool) /\ b) = (na \/ nb)``),
    ("nnf-neg or",
      "((declare-fun a () Bool) (declare-fun b () Bool) \
        \(declare-fun na () Bool) (declare-fun nb () Bool) \
        \(proof (nnf-neg (asserted (= (not a) na)) \
        \(asserted (= (not b) nb)) \
        \(= (not (or a b)) (and na nb)))))",
      ``~((a:bool) \/ b) = (na /\ nb)``),
    ("nnf-neg implication",
      "((declare-fun a () Bool) (declare-fun b () Bool) \
        \(declare-fun nb () Bool) \
        \(proof (nnf-neg (asserted (= (not b) nb)) \
        \(= (not (implies a b)) (and a nb)))))",
      ``~((a:bool) ==> b) = (a /\ nb)``),
    ("nnf-neg forall",
      "((proof (nnf-neg \
        \(= (not (forall ((x Bool)) false)) \
        \(exists ((x Bool)) true)))))",
      ``~(!x:bool. F) = (?x:bool. T)``),
    ("nnf-neg exists",
      "((proof (nnf-neg \
        \(= (not (exists ((x Bool)) true)) \
        \(forall ((x Bool)) false)))))",
      ``~(?x:bool. T) = (!x:bool. F)``)
  ]
in
  List.app assert_nnf_replays_without_metis cases
end

fun z3_th_lemma_existing_theory_replay_minimal_success () =
let
  val cases = [
    ("arith/farkas",
      "((proof ((_ th-lemma arith farkas 1) (= 1 1))))"),
    ("arith/assign-bounds",
      "((proof ((_ th-lemma arith assign-bounds 0) (= 2 2))))"),
    ("arith/eq-propagate",
      "((proof ((_ th-lemma arith eq-propagate 0) (= 3 3))))"),
    ("arith/gomory-cut",
      "((proof ((_ th-lemma arith gomory-cut 0) (= 4 4))))"),
    ("arith/triangle-eq",
      "((proof ((_ th-lemma arith triangle-eq 0) (= 5 5))))"),
    ("array/select-store",
      "((proof ((_ th-lemma array select-store 0) (= false false))))"),
    ("array/extensionality",
      "((proof ((_ th-lemma array extensionality 0) (= true true))))"),
    ("basic/true",
      "((proof ((_ th-lemma basic eq-propagate 0) true)))"),
    ("basic/equality",
      "((proof ((_ th-lemma basic eq-propagate 1) (= false false))))"),
    ("basic/int-equality-symmetry",
      "((declare-fun x () Int) (declare-fun y () Int) \
        \(proof ((_ th-lemma basic eq-propagate 2) \
        \(implies (= x y) (= y x)))))"),
    ("arith/nla-square",
      "((declare-fun x () Int) \
        \(proof ((_ th-lemma arith nla 6) (>= (* x x) 0))))"),
    ("bv/bit-blast",
      "((proof ((_ th-lemma bv bit-blast 1) (= false false))))")
  ]
in
  List.app (fn (name, proof_text) =>
    (let
       val thm = replay_z3_proof_string proof_text
       val _ = assert (List.null (Thm.hyp thm),
         "th-lemma " ^ name ^ " replayed with unexpected hypotheses: " ^
         Library.thm_to_string thm)
       val _ = Library.check_oracle_tags ("th-lemma " ^ name) thm
     in
       ()
     end
      handle Feedback.HOL_ERR holerr =>
        die ("FAIL: th-lemma " ^ name ^ " did not replay: " ^
          Feedback.message_of holerr))) cases
end

fun assert_basic_th_lemma_dispatch
    (name, proof_text, required_profile, forbidden_profiles) =
let
  val () = Profile.reset_all ()
  val thm = replay_z3_proof_string proof_text
in
  assert (List.null (Thm.hyp thm),
    "basic th-lemma " ^ name ^ " replayed with unexpected hypotheses: " ^
    Library.thm_to_string thm);
  Library.check_oracle_tags ("basic th-lemma " ^ name) thm;
  assert (profile_call_count required_profile > 0,
    "basic th-lemma " ^ name ^ " did not use " ^ required_profile);
  List.app (fn profile =>
    assert (profile_call_count profile = 0,
      "basic th-lemma " ^ name ^ " unexpectedly used " ^ profile))
    forbidden_profiles
end

fun z3_th_lemma_basic_dispatch_replay_success () =
let
  val arith_profile = "th_lemma[basic](4)(arith)"
  val bv_profile = "th_lemma[basic](5)(bv)"
  val array_profile = "th_lemma[basic](6)(array)"
  val metis_profile = "th_lemma[basic](7)(METIS)"
  val cases = [
    ("pure-boolean",
      "((proof ((_ th-lemma basic eq-propagate 0) true)))",
      "th_lemma[basic](3)(TAUT_PROVE)",
      [arith_profile, bv_profile, array_profile, metis_profile]),
    ("arith",
      "((declare-fun x () Int) (declare-fun y () Int) \
        \(proof ((_ th-lemma basic eq-propagate 1) \
        \(implies (= x y) (= y x)))))",
      arith_profile,
      [bv_profile, array_profile, metis_profile]),
    ("bv",
      "((declare-fun x () (_ BitVec 8)) \
        \(proof ((_ th-lemma basic eq-propagate 2) \
        \(= (bvadd x #x00) x))))",
      bv_profile,
      [arith_profile, array_profile, metis_profile]),
    ("array",
      "((declare-fun a () (Array Bool Bool)) (declare-fun i () Bool) \
        \(proof ((_ th-lemma basic eq-propagate 3) \
        \(= (store a i (select a i)) a))))",
      array_profile,
      [arith_profile, bv_profile, metis_profile])
  ]
in
  List.app assert_basic_th_lemma_dispatch cases
end

fun z3_th_lemma_basic_unsupported_diagnostic () =
  (ignore (replay_z3_proof_string
    "((proof ((_ th-lemma basic eq-propagate 7) false)))");
   die "FAIL: unsupported basic th-lemma replayed successfully")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring "theory=basic" msg,
        "basic th-lemma diagnostic did not include theory: " ^ msg);
      assert (String.isSubstring "subkind=eq-propagate" msg,
        "basic th-lemma diagnostic did not include subkind: " ^ msg);
      assert (String.isSubstring "indices=[7]" msg,
        "basic th-lemma diagnostic did not include proof indices: " ^ msg);
      assert (String.isSubstring "parsed HOL conclusion: F" msg,
        "basic th-lemma diagnostic did not include conclusion: " ^ msg);
      assert (String.isSubstring "unsupported th-lemma shape" msg,
        "basic th-lemma diagnostic did not report unsupported shape: " ^ msg);
      assert (String.isSubstring "attempted theories=[boolean, metis]" msg,
        "basic th-lemma diagnostic did not include attempted theories: " ^ msg)
    end

fun z3_nonlinear_missing_csdp_diagnostic () =
let
  val expected = Library.csdp_missing_diagnostic
  val script =
    "load \"Library\";\n" ^
    "val expected = Library.csdp_missing_diagnostic;\n" ^
    "val _ =\n" ^
    "  (ignore (Library.nla_prove ``0r < 1r + 2r * (x:real) * x * x * x + 2r * x * x * x * y - x * x * y * y + 5r * y * y * y * y``);\n" ^
    "   OS.Process.exit OS.Process.failure)\n" ^
    "  handle Feedback.HOL_ERR holerr =>\n" ^
    "    let val msg = Feedback.message_of holerr\n" ^
    "    in if msg = expected then OS.Process.exit OS.Process.success\n" ^
    "       else (print (msg ^ \"\\n\"); OS.Process.exit OS.Process.failure)\n" ^
    "    end;\n"
in
  with_temp_file script (fn input =>
    with_temp_file "" (fn output =>
      let
        val cmd =
          "HOL4_CSDP_EXECUTABLE=/definitely-not-hol4-csdp " ^
          "\"$HOLDIR/bin/hol\" --gcthreads=1 " ^
          "--holstate=\"$HOLDIR/src/HolSmt/smtheap\" < " ^ input ^
          " > " ^ output ^ " 2>&1"
        val status = OS.Process.system cmd
        val text = read_text_file output
      in
        assert (OS.Process.isSuccess status,
          "missing CSDP diagnostic mismatch; expected '" ^ expected ^
          "', saw: " ^ text)
      end))
end

fun assert_array_prover name prover tm =
  (let
     val thm = prover tm
   in
     assert (Thm.concl thm ~~ tm,
       name ^ " proved wrong conclusion: " ^ Library.thm_to_string thm);
     Library.check_oracle_tags name thm
   end
   handle Feedback.HOL_ERR holerr =>
     die ("FAIL: " ^ name ^ " did not prove array goal: " ^
       Feedback.message_of holerr))

fun array_prove_ladder_rungs_success () =
  (assert_array_prover "array_prove proforma rung"
     SmtArrayProve.array_prove
     ``((i =+ e) (a :'i -> 'v)) i = e``;
   assert_array_prover "array_prove literal update rung"
     SmtArrayProve.simp_prove_update
     ``((1i =+ T) (a :int -> bool)) 1i``;
   assert_array_prover "array_prove symbolic select/store rung"
     SmtArrayProve.symbolic_index_prove
     ``i <> j ==> ((i =+ e) (a :'i -> 'v)) j = a j``;
   assert_array_prover "array_prove extensionality rung"
     SmtArrayProve.extensionality_prove
     ``(!i. (a :'i -> 'v) i = b i) ==> (a = b)``;
   assert_array_prover "array_prove explicit metis rung"
     SmtArrayProve.metis_array_prove
     ``(i =+ e) ((i =+ e) (a :'i -> 'v)) = (i =+ e) a``)

fun array_prove_unsupported_diagnostic () =
  (ignore (SmtArrayProve.array_prove ``F``);
   die "FAIL: unsupported array th-lemma replayed successfully")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring "unsupported th-lemma shape" msg,
        "array th-lemma diagnostic did not report unsupported shape: " ^ msg);
      assert (String.isSubstring "theory=array" msg,
        "array th-lemma diagnostic did not include theory: " ^ msg);
      assert (String.isSubstring "conclusion=F" msg,
        "array th-lemma diagnostic did not include conclusion: " ^ msg)
    end

fun expect_advanced_th_lemma_diagnostic
    (name, proof_text, theory_text, obligation_id) =
  (ignore (replay_z3_proof_string proof_text);
   die ("FAIL: unsupported advanced th-lemma " ^ name ^
     " replayed successfully"))
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring theory_text msg,
        "advanced th-lemma diagnostic did not include theory for " ^ name ^
        ": " ^ msg);
      assert (String.isSubstring "z3_version=4.12.4" msg,
        "advanced th-lemma diagnostic did not include Z3 version for " ^
        name ^ ": " ^ msg);
      assert (String.isSubstring "proof-format limitation" msg,
        "advanced th-lemma diagnostic did not explain proof-format limit for " ^
        name ^ ": " ^ msg);
      assert (String.isSubstring ("missing feature: " ^ obligation_id) msg,
        "advanced th-lemma diagnostic did not include missing feature for " ^
        name ^ ": " ^ msg);
      assert (String.isSubstring ("failing case IDs: " ^ obligation_id) msg,
        "advanced th-lemma diagnostic did not include failing case ID for " ^
        name ^ ": " ^ msg);
      assert (String.isSubstring "parsed HOL conclusion: F" msg,
        "advanced th-lemma diagnostic did not include conclusion for " ^
        name ^ ": " ^ msg)
    end

fun z3_th_lemma_advanced_unsupported_diagnostic () =
let
  val cases = [
    ("floating-point",
      "((proof ((_ th-lemma fp eq-propagate 1) false)))",
      "theory=fp",
      "proof-rule:th-lemma-fp"),
    ("sequence",
      "((proof ((_ th-lemma seq eq-propagate 2) false)))",
      "theory=seq",
      "proof-rule:th-lemma-seq"),
    ("string",
      "((proof ((_ th-lemma string eq-propagate 3) false)))",
      "theory=string",
      "proof-rule:th-lemma-string"),
    ("regexp",
      "((proof ((_ th-lemma regexp eq-propagate 4) false)))",
      "theory=regexp",
      "proof-rule:th-lemma-regexp"),
    ("datatype",
      "((proof ((_ th-lemma datatype eq-propagate 5) false)))",
      "theory=datatype",
      "proof-rule:th-lemma-datatype")
  ]
in
  List.app expect_advanced_th_lemma_diagnostic cases
end

fun z3_proof_replay_failure_diagnostic () =
  (ignore (replay_z3_proof_string "((proof (commutativity false)))");
   die "FAIL: malformed Z3 proof rule replayed successfully")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring "proof rule: commutativity" msg,
        "replay diagnostic did not include exact proof rule: " ^ msg);
      assert (String.isSubstring "local proof subterm: commutativity" msg,
        "replay diagnostic did not include local proof term: " ^ msg);
      assert (String.isSubstring "parsed HOL conclusion: F" msg,
        "replay diagnostic did not include parsed conclusion: " ^ msg);
      assert (String.isSubstring "replay state:" msg andalso
              String.isSubstring "asserted_hyps=" msg andalso
              String.isSubstring "definition_hyps=" msg andalso
              String.isSubstring "z3_vars=" msg,
        "replay diagnostic did not include replay-state summary: " ^ msg);
      assert (String.isSubstring "z3_version=4.12.4" msg,
        "replay diagnostic did not include Z3 version: " ^ msg)
    end

fun expect_z3_replay_malformed_premise_diagnostic (name, proof_text) =
  (ignore (replay_z3_proof_string proof_text);
   die ("FAIL: malformed-premise Z3 proof rule " ^ name ^
     " replayed successfully"))
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring ("proof rule: " ^ name) msg,
        "malformed-premise diagnostic did not include proof rule " ^
        name ^ ": " ^ msg);
      assert (String.isSubstring "local proof subterm:" msg,
        "malformed-premise diagnostic did not include local proof subterm for " ^
        name ^ ": " ^ msg);
      assert (String.isSubstring "parsed HOL conclusion:" msg,
        "malformed-premise diagnostic did not include parsed conclusion for " ^
        name ^ ": " ^ msg);
      assert (String.isSubstring "premise HOL theorems:" msg,
        "malformed-premise diagnostic did not include premise theorems for " ^
        name ^ ": " ^ msg);
      assert (String.isSubstring "underlying HOL_ERR:" msg,
        "malformed-premise diagnostic did not include underlying HOL_ERR for " ^
        name ^ ": " ^ msg)
    end

fun z3_proof_replay_malformed_premise_diagnostics () =
let
  val cases = [
    ("and_elim",
      "((proof (and-elim (asserted false) true)))"),
    ("mp",
      "((proof (mp (asserted true) (asserted true) false)))"),
    ("unit_resolution",
      "((proof (unit-resolution false)))")
  ]
in
  List.app expect_z3_replay_malformed_premise_diagnostic cases
end

fun z3_tac_oracle_tag_gate_rejects_oracle_thm () =
  (Library.check_oracle_tags "Z3_SMT_Prover"
     (Thm.mk_oracle_thm "HolSmtLib" ([], boolSyntax.T));
   die "FAIL: oracle-tagged theorem passed the Z3_TAC oracle gate")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring "unexpected oracle/axiom tags" msg,
        "oracle gate diagnostic did not mention unexpected tags: " ^ msg)
    end

fun z3_reconstructed_theorem_contract_success () =
  ignore (Z3.check_reconstructed_theorem "unit-test"
    (([], boolSyntax.T), boolTheory.TRUTH))

fun z3_reconstructed_theorem_contract_rejects_bad_shape () =
let
  fun expect_failure label expected thunk =
    (ignore (thunk ());
     die ("FAIL: theorem contract accepted " ^ label))
    handle Feedback.HOL_ERR holerr =>
      let val msg = Feedback.message_of holerr
      in
        assert (String.isSubstring expected msg,
          "theorem contract diagnostic for " ^ label ^
          " did not include " ^ expected ^ ": " ^ msg)
      end
in
  expect_failure "extra hypothesis" "extra hypotheses" (fn () =>
    Z3.check_reconstructed_theorem "unit-test"
      (([], boolSyntax.T), Thm.ASSUME boolSyntax.T));
  expect_failure "extra hypothesis details" "unexpected hypotheses: [T]"
    (fn () =>
      Z3.check_reconstructed_theorem "unit-test"
        (([], boolSyntax.T), Thm.ASSUME boolSyntax.T));
  expect_failure "allowed hypothesis details" "allowed hypotheses: []"
    (fn () =>
      Z3.check_reconstructed_theorem "unit-test"
        (([], boolSyntax.T), Thm.ASSUME boolSyntax.T));
  expect_failure "conclusion mismatch" "parsed assertion-negation goal" (fn () =>
    Z3.check_reconstructed_theorem "unit-test"
      (([], boolSyntax.F), boolTheory.TRUTH))
end

fun z3_direct_bitvector_overflow_contradiction_success () =
let
  fun conjunction [] = boolSyntax.T
    | conjunction (tm :: tms) =
        List.foldl (fn (next, acc) => boolSyntax.mk_conj (acc, next)) tm tms
  val state =
    parse_smtlib_state
      ("(set-option :produce-proofs true)\n" ^
       "(set-logic QF_BV)\n" ^
       "(declare-const a (_ BitVec 8))\n" ^
       "(declare-const b (_ BitVec 8))\n" ^
       "(assert (and (bvsaddo a b) (not (bvsaddo a b))))\n" ^
       "(check-sat)\n" ^
       "(get-proof)\n")
  val goal = boolSyntax.mk_neg (conjunction (#assertions state))
  val thm =
    case Z3.Z3_SMT_Prover ([], goal) of
      SolverSpec.UNSAT (SOME thm) => thm
    | _ => die "FAIL: direct bitvector contradiction did not produce a theorem"
in
  assert (List.null (Thm.hyp thm),
    "direct bitvector contradiction theorem has unexpected hypotheses");
  assert (Term.aconv (Thm.concl thm) goal,
    "direct bitvector contradiction theorem conclusion does not match goal");
  Library.check_oracle_tags "unit-test" thm
end

fun z3_direct_bitvector_overflow_tautology_sat_success () =
let
  fun conjunction [] = boolSyntax.T
    | conjunction (tm :: tms) =
        List.foldl (fn (next, acc) => boolSyntax.mk_conj (acc, next)) tm tms
  val state =
    parse_smtlib_state
      ("(set-logic QF_BV)\n" ^
       "(declare-const a (_ BitVec 8))\n" ^
       "(declare-const b (_ BitVec 8))\n" ^
       "(assert (or (bvumulo a b) (not (bvumulo a b))))\n" ^
       "(check-sat)\n")
  val goal = boolSyntax.mk_neg (conjunction (#assertions state))
in
  case Z3.Z3_SMT_Prover ([], goal) of
    SolverSpec.SAT NONE => ()
  | SolverSpec.SAT (SOME _) =>
      die "FAIL: direct bitvector tautology SAT produced a theorem"
  | _ => die "FAIL: direct bitvector tautology was not reported SAT"
end

fun z3_direct_distinct_contradiction_success () =
let
  fun conjunction [] = boolSyntax.T
    | conjunction (tm :: tms) =
        List.foldl (fn (next, acc) => boolSyntax.mk_conj (acc, next)) tm tms
  val state =
    parse_smtlib_state
      ("(set-option :produce-proofs true)\n" ^
       "(set-logic QF_LIA)\n" ^
       "(assert (distinct 1 1))\n" ^
       "(check-sat)\n" ^
       "(get-proof)\n")
  val goal = boolSyntax.mk_neg (conjunction (#assertions state))
  val thm =
    case Z3.Z3_SMT_Prover ([], goal) of
      SolverSpec.UNSAT (SOME thm) => thm
    | _ => die "FAIL: direct distinct contradiction did not produce a theorem"
in
  assert (List.null (Thm.hyp thm),
    "direct distinct contradiction theorem has unexpected hypotheses");
  assert (Term.aconv (Thm.concl thm) goal,
    "direct distinct contradiction theorem conclusion does not match goal");
  Library.check_oracle_tags "unit-test" thm
end

(* The checked SAT short-circuit in Z3.Z3_SMT_Prover proves the asserted
   body satisfiable entirely within HOL and returns `SAT NONE' without ever
   invoking an external solver.  Each script below is a trivially true
   ground (or trivially satisfiable) arithmetic fact whose HOL translation
   makes Z3 diverge; the short-circuit must decide them locally.  These
   tests run regardless of whether Z3 is configured. *)
fun z3_direct_ground_arithmetic_sat_success () =
let
  fun conjunction [] = boolSyntax.T
    | conjunction (tm :: tms) =
        List.foldl (fn (next, acc) => boolSyntax.mk_conj (acc, next)) tm tms
  fun expect_sat label text =
    let
      val state = parse_smtlib_state text
      val goal = boolSyntax.mk_neg (conjunction (#assertions state))
    in
      case Z3.Z3_SMT_Prover ([], goal) of
        SolverSpec.SAT NONE => ()
      | SolverSpec.SAT (SOME _) =>
          die ("FAIL: " ^ label ^ " short-circuit produced a theorem")
      | SolverSpec.UNSAT _ =>
          die ("FAIL: " ^ label ^ " was wrongly reported UNSAT")
      | SolverSpec.UNKNOWN _ =>
          die ("FAIL: " ^ label ^ " was not decided by the SAT short-circuit")
    end
in
  (* integer ABS -- the `|7| = 7'-shaped example over int *)
  expect_sat "int abs"
    ("(set-logic QF_LIA)\n(assert (= (abs (- 7)) 7))\n(check-sat)\n");
  (* Euclidean division/modulo carry a `nocompute' attribute and require
     the EDIV_DEF/EMOD_DEF unfolding step of the ladder *)
  expect_sat "int ediv"
    ("(set-logic QF_LIA)\n(assert (= (div 7 3) 2))\n(check-sat)\n");
  expect_sat "int emod"
    ("(set-logic QF_LIA)\n(assert (= (mod 7 3) 1))\n(check-sat)\n");
  (* real division goes through Z3's total `smt_rdiv' constant *)
  expect_sat "real division"
    ("(set-logic QF_LRA)\n(assert (= (/ 3.0 2.0) 1.5))\n(check-sat)\n");
  (* linear real arithmetic decided by evaluation *)
  expect_sat "real plus"
    ("(set-logic QF_LRA)\n(assert (= (+ 1.0 2.0 3.0) 6.0))\n(check-sat)\n");
  (* mixed int/real embedding *)
  expect_sat "intreal to_int"
    ("(set-logic QF_NIRA)\n(assert (= (to_int 2.0) 2))\n(check-sat)\n");
  (* a satisfiable equation over an unknown: the ladder proves the
     existential closure `?x. x = 0' *)
  expect_sat "int existential"
    ("(set-logic QF_LIA)\n(declare-const x Int)\n" ^
     "(assert (= x 0))\n(check-sat)\n");
  expect_sat "real existential"
    ("(set-logic QF_LRA)\n(declare-const x Real)\n" ^
     "(assert (= x 0.0))\n(check-sat)\n");
  (* propositional tautology -- guards the pre-existing TAUT_CONV branch *)
  expect_sat "propositional tautology"
    ("(set-logic QF_UF)\n(declare-const p Bool)\n" ^
     "(assert (or p (not p)))\n(check-sat)\n")
end

fun holsmt_solver_result_negative_diagnostics () =
let
  fun expect_error label expected solver =
    (ignore (Tactical.TAC_PROOF (([], boolSyntax.T),
       HolSmtLib.GENERIC_SMT_TAC solver));
     die ("FAIL: " ^ label ^ " solver result was accepted"))
    handle Feedback.HOL_ERR holerr =>
      let val msg = Feedback.message_of holerr
      in
        assert (Feedback.top_structure_of holerr = "HolSmtLib" andalso
                Feedback.top_function_of holerr = "GENERIC_SMT_TAC",
          label ^ " diagnostic came from the wrong function: " ^ msg);
        assert (String.isSubstring expected msg,
          label ^ " diagnostic did not include '" ^ expected ^ "': " ^ msg)
      end
in
  expect_error "sat" "satisfiable" (fn _ => SolverSpec.SAT NONE);
  expect_error "unknown" "unknown" (fn _ => SolverSpec.UNKNOWN (SOME "audit"))
end

fun solver_spec_rejects_bad_proof_theorem () =
let
  fun solver_with_thm thm =
    SolverSpec.make_solver
      (fn _ => ((), []))
      "cat "
      (fn () => fn _ => SolverSpec.UNSAT (SOME thm))
  fun expect_failure label expected thm goal =
    (ignore (solver_with_thm thm goal);
     die ("FAIL: SolverSpec accepted bad proof theorem with " ^ label))
    handle Feedback.HOL_ERR holerr =>
      let val msg = Feedback.message_of holerr
      in
        assert (Feedback.top_structure_of holerr = "SolverSpec" andalso
                Feedback.top_function_of holerr = "make_solver",
          label ^ " diagnostic came from the wrong function: " ^ msg);
        assert (String.isSubstring expected msg,
          label ^ " diagnostic did not include '" ^ expected ^ "': " ^ msg)
      end
in
  expect_failure "extra hypotheses" "additional hyp(s)"
    (Thm.ASSUME boolSyntax.T) ([], boolSyntax.T);
  expect_failure "conclusion mismatch" "conclusion does not match goal"
    boolTheory.TRUTH ([], boolSyntax.F)
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
    ("script_ast_command_syntax_error", script_ast_command_syntax_error),
    ("script_ast_stack_and_query_success", script_ast_stack_and_query_success),
    ("script_ast_datatype_recursive_remaining_success",
      script_ast_datatype_recursive_remaining_success),
    ("parse_file_datatype_command_success",
      parse_file_datatype_command_success),
    ("parse_file_datatype_dictionary_success",
      parse_file_datatype_dictionary_success),
    ("parse_file_parametric_datatype_dictionary_success",
      parse_file_parametric_datatype_dictionary_success),
    ("parse_legacy_datatype_mutual_dictionary_success",
      parse_legacy_datatype_mutual_dictionary_success),
    ("parse_file_echo_success", parse_file_echo_success),
    ("parse_file_push_pop_assertion_scoping",
      parse_file_push_pop_assertion_scoping),
    ("parse_file_push_pop_declaration_scoping",
      parse_file_push_pop_declaration_scoping),
    ("parse_file_reset_assertions_state", parse_file_reset_assertions_state),
    ("parse_file_reset_state", parse_file_reset_state),
    ("parse_file_query_commands_success", parse_file_query_commands_success),
    ("parse_file_define_fun_fragment_scope_success",
      parse_file_define_fun_fragment_scope_success),
    ("parse_file_define_funs_rec_fragment_scope_success",
      parse_file_define_funs_rec_fragment_scope_success),
    ("smtlib_soundness_audit_scope_success",
      smtlib_soundness_audit_scope_success),
    ("smtlib_indexed_parametric_sort_reconstruction_success",
      smtlib_indexed_parametric_sort_reconstruction_success),
    ("smtlib_typecheck_invalid_assertion_diagnostic",
      smtlib_typecheck_invalid_assertion_diagnostic),
    ("smtlib_typecheck_declared_function_mismatch_diagnostic",
      smtlib_typecheck_declared_function_mismatch_diagnostic),
    ("smtlib_array_type_mismatch_diagnostics",
      smtlib_array_type_mismatch_diagnostics),
    ("smtlib_command_malformed_diagnostics",
      smtlib_command_malformed_diagnostics),
    ("smtlib_logic_fragment_diagnostics",
      smtlib_logic_fragment_diagnostics),
    ("smtlib_checked_replay_gap_diagnostics",
      smtlib_checked_replay_gap_diagnostics),
    ("smtlib_typecheck_overloaded_and_indexed_success",
      smtlib_typecheck_overloaded_and_indexed_success),
    ("smtlib_core_symbol_metadata_success",
      smtlib_core_symbol_metadata_success),
    ("smtlib_logic_metadata_extension_split_success",
      smtlib_logic_metadata_extension_split_success),
    ("smtlib_core_arith_array_bv_symbol_coverage_success",
      smtlib_core_arith_array_bv_symbol_coverage_success),
    ("smtlib_advanced_symbol_coverage_success",
      smtlib_advanced_symbol_coverage_success),
    ("smtlib_arith_array_parse_signatures_success",
      smtlib_arith_array_parse_signatures_success),
    ("smtlib_bitvector_parse_signatures_success",
      smtlib_bitvector_parse_signatures_success),
    ("smtlib_floatingpoint_parse_signatures_success",
      smtlib_floatingpoint_parse_signatures_success),
    ("smtlib_string_regex_parse_signatures_success",
      smtlib_string_regex_parse_signatures_success),
    ("smtlib_z3_extension_parse_signatures_success",
      smtlib_z3_extension_parse_signatures_success),
    ("smtlib_scoped_logic_dictionary_success",
      smtlib_scoped_logic_dictionary_success),
    ("smtlib_translation_logic_inference_success",
      smtlib_translation_logic_inference_success),
    ("smtlib_translation_records_success",
      smtlib_translation_records_success),
    ("smtlib_extended_hol_encoding_records_success",
      smtlib_extended_hol_encoding_records_success),
    ("smtlib_higher_order_translation_abstraction_success",
      smtlib_higher_order_translation_abstraction_success),
    ("smtlib_translation_shape_matrix_success",
      smtlib_translation_shape_matrix_success),
    ("smtlib_term_translation_branch_matrix_success",
      smtlib_term_translation_branch_matrix_success),
    ("smtlib_preprocessing_and_gap_diagnostics",
      smtlib_preprocessing_and_gap_diagnostics),
    ("smtlib_roundtrip_current_theories_success",
      smtlib_roundtrip_current_theories_success),
    ("smtlib_roundtrip_known_gap_matrix_success",
      smtlib_roundtrip_known_gap_matrix_success),
    ("z3_proof_registry_metadata_success",
      z3_proof_registry_metadata_success),
    ("z3_proof_parser_normalizes_rule_alias_success",
      z3_proof_parser_normalizes_rule_alias_success),
    ("z3_proof_parser_erases_proof_bind_success",
      z3_proof_parser_erases_proof_bind_success),
    ("z3_proof_parser_th_lemma_metadata_success",
      z3_proof_parser_th_lemma_metadata_success),
    ("z3_proof_parser_advanced_th_lemma_metadata_success",
      z3_proof_parser_advanced_th_lemma_metadata_success),
    ("z3_proof_parser_unknown_rule_diagnostic",
      z3_proof_parser_unknown_rule_diagnostic),
    ("z3_core_proof_rule_replay_minimal_raw_success",
      z3_core_proof_rule_replay_minimal_raw_success),
    ("z3_trans_star_chain_search_replay_no_metis_success",
      z3_trans_star_chain_search_replay_no_metis_success),
    ("z3_trans_star_chain_search_no_path_diagnostic",
      z3_trans_star_chain_search_no_path_diagnostic),
    ("z3_nnf_structural_replay_no_metis_success",
      z3_nnf_structural_replay_no_metis_success),
    ("z3_th_lemma_existing_theory_replay_minimal_success",
      z3_th_lemma_existing_theory_replay_minimal_success),
    ("z3_th_lemma_basic_dispatch_replay_success",
      z3_th_lemma_basic_dispatch_replay_success),
    ("z3_th_lemma_basic_unsupported_diagnostic",
      z3_th_lemma_basic_unsupported_diagnostic),
    ("z3_nonlinear_missing_csdp_diagnostic",
      z3_nonlinear_missing_csdp_diagnostic),
    ("array_prove_ladder_rungs_success",
      array_prove_ladder_rungs_success),
    ("array_prove_unsupported_diagnostic",
      array_prove_unsupported_diagnostic),
    ("z3_th_lemma_advanced_unsupported_diagnostic",
      z3_th_lemma_advanced_unsupported_diagnostic),
    ("z3_proof_replay_failure_diagnostic",
      z3_proof_replay_failure_diagnostic),
    ("z3_proof_replay_malformed_premise_diagnostics",
      z3_proof_replay_malformed_premise_diagnostics),
    ("z3_tac_oracle_tag_gate_rejects_oracle_thm",
      z3_tac_oracle_tag_gate_rejects_oracle_thm),
    ("z3_reconstructed_theorem_contract_success",
      z3_reconstructed_theorem_contract_success),
    ("z3_reconstructed_theorem_contract_rejects_bad_shape",
      z3_reconstructed_theorem_contract_rejects_bad_shape),
    ("z3_direct_bitvector_overflow_contradiction_success",
      z3_direct_bitvector_overflow_contradiction_success),
    ("z3_direct_bitvector_overflow_tautology_sat_success",
      z3_direct_bitvector_overflow_tautology_sat_success),
    ("z3_direct_distinct_contradiction_success",
      z3_direct_distinct_contradiction_success),
    ("z3_direct_ground_arithmetic_sat_success",
      z3_direct_ground_arithmetic_sat_success),
    ("holsmt_solver_result_negative_diagnostics",
      holsmt_solver_result_negative_diagnostics),
    ("solver_spec_rejects_bad_proof_theorem",
      solver_spec_rejects_bad_proof_theorem)
  ]
  val () = List.app run_test tests
  val () = print "\ndone, all unit tests successful.\n"
in
  ()
end

end (* struct *)
