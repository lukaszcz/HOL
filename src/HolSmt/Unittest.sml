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

fun parse_smtlib_state_with_options options contents =
  with_temp_file contents (SmtLib_Parser.parse_file_state_with_options options)

fun term_has_subterm pred tm =
  pred tm orelse
  (let
     val (rator, rand) = Term.dest_comb tm
   in
     term_has_subterm pred rator orelse term_has_subterm pred rand
   end
   handle _ =>
     (let val (_, body) = Term.dest_abs tm
      in term_has_subterm pred body end
      handle _ => false))

fun term_has_real_of_int tm =
  term_has_subterm intrealSyntax.is_real_of_int tm

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

fun parse_legacy_smtlib_assertions contents =
  let
    val (_, _, _, assertions) =
      SmtLib_Parser.parse_benchmark
        (Library.get_token (string_get_char contents))
  in
    assertions
  end

fun parse_legacy_smtlib_state contents =
  SmtLib_Parser.parse_benchmark_state
    (Library.get_token (string_get_char contents))

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

fun assert_no_hyps (label, thm) =
  assert (List.null (Thm.hyp thm),
    label ^ " produced a theorem with hypotheses")

fun assert_concl_alpha (label, thm, expected) =
  let val actual = Thm.concl thm
  in
    assert (actual ~~ expected,
      label ^ " conclusion mismatch\nexpected: " ^
      term_with_types expected ^ "\nactual: " ^ term_with_types actual)
  end

fun assert_num_binder_conv (label, input, expected) =
  let
    val thm = SmtLib.NUM_BINDERS_TO_INT_CONV input
    val expected_concl = boolSyntax.mk_eq (input, expected)
  in
    assert_no_hyps (label, thm);
    assert_concl_alpha (label, thm, expected_concl)
  end

(*****************************************************************************)
(* local datatypes for translation tests                                      *)
(*****************************************************************************)

val _ = Hol_datatype
  `smt_rec = <| smt_count : int; smt_flag : bool |>`

val _ = Hol_datatype
  `smt_tri = SmtTriA | SmtTriB of int | SmtTriC of bool`

val _ = Hol_datatype
  `smt_left = SmtLeftDone | SmtLeft of smt_right;
   smt_right = SmtRightDone | SmtRight of smt_left`

val _ = new_type ("smt_nonfree", 1)
val _ = new_constant ("smt_nonfree_nil", ``:'a smt_nonfree``)
val _ = new_constant
  ("smt_nonfree_cons", ``:'a -> 'a smt_nonfree -> 'a smt_nonfree``)
val _ = new_constant ("smtlib_uf_logic_foo", ``:int -> int``)
val smt_nonfree_ind = new_axiom
  ("smt_nonfree_ind",
   ``!P. P smt_nonfree_nil /\
         (!t. P t ==> !a. P (smt_nonfree_cons a t)) ==> !x. P x``)
val smt_nonfree_cases = new_axiom
  ("smt_nonfree_cases",
   ``!x. (x = smt_nonfree_nil) \/
         ?a t. x = smt_nonfree_cons a t``)
val _ = TypeBase.write [
  TypeBasePure.mk_nondatatype_info
    (``:'a smt_nonfree``,
     {encode = NONE, induction = SOME smt_nonfree_ind,
      nchotomy = SOME smt_nonfree_cases, size = NONE})
]

(*****************************************************************************)
(* test definitions                                                          *)
(*****************************************************************************)

fun num_binder_transfer_lemmas_success () =
  let
    val forall_expected =
      ``!P :num -> bool.
          (!n :num. P n) <=> (!i :int. 0 <= i ==> P (Num i))``
    val exists_expected =
      ``!P :num -> bool.
          (?n :num. P n) <=> (?i :int. 0 <= i /\ P (Num i))``
  in
    assert_no_hyps ("NUM_FORALL_TO_INT", HolSmtTheory.NUM_FORALL_TO_INT);
    assert_no_hyps ("NUM_EXISTS_TO_INT", HolSmtTheory.NUM_EXISTS_TO_INT);
    assert_concl_alpha
      ("NUM_FORALL_TO_INT", HolSmtTheory.NUM_FORALL_TO_INT,
       forall_expected);
    assert_concl_alpha
      ("NUM_EXISTS_TO_INT", HolSmtTheory.NUM_EXISTS_TO_INT,
       exists_expected)
  end

fun num_binder_relativization_forall_success () =
  assert_num_binder_conv
    ("num forall binder relativization",
     ``!n :num. n = n``,
     ``!i :int. 0 <= i ==> Num i = Num i``)

fun num_binder_relativization_exists_success () =
  assert_num_binder_conv
    ("num exists binder relativization",
     ``?n :num. n = 0``,
     ``?i :int. 0 <= i /\ Num i = 0``)

fun num_binder_relativization_nested_mixed_success () =
  assert_num_binder_conv
    ("nested mixed num binder relativization",
     ``!n :num. !j :int. ?m :num. j <= &m /\ n <= m``,
     ``!i :int.
         0 <= i ==>
         !j :int.
           ?k :int.
             0 <= k /\ j <= &(Num k) /\ Num i <= Num k``)

fun num_binder_relativization_non_num_noop_success () =
  assert_num_binder_conv
    ("non-num binder relativization no-op",
     ``!i :int. i <= i``,
     ``!i :int. i <= i``)

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

fun transferred_smtlib_text tm =
let
  val (goal, _) = SolverSpec.simplify (SmtLib.SIMP_TAC true) ([], tm)
  val (_, strings) = SmtLib.goal_to_SmtLib_translation NONE goal
in
  String.concat strings
end

fun transferred_smtlib_goal_text goal0 =
let
  val (goal, _) = SolverSpec.simplify (SmtLib.SIMP_TAC true) goal0
  val (_, strings) = SmtLib.goal_to_SmtLib_translation NONE goal
in
  String.concat strings
end

fun assert_not_contains label needle haystack =
  assert (not (contains needle haystack),
    label ^ " unexpectedly contained '" ^ needle ^ "':\n" ^ haystack)

fun assert_pure_int_transfer label text =
  (assert_not_contains label "(declare-sort" text;
   assert_not_contains label "forall" text;
   assert_not_contains label "Num" text;
   assert_not_contains label "int_of_num" text)

(* Some totalized operations retain first-order definitions for otherwise
   unsupported HOL constants (for example integer max and total real
   division).  They are still a successful num-to-Int transfer provided no
   Peano/nat encoding remains. *)
fun assert_num_free_transfer label text =
  (assert_not_contains label "(declare-sort" text;
   assert_not_contains label "Num" text;
   assert_not_contains label "int_of_num" text)

fun num_transfer_literal_normalization_success () =
let
  val text = transferred_smtlib_text ``42n = n``
in
  assert_pure_int_transfer "num literal transfer" text;
  assert (contains "(assert (<= 0 v0))" text,
    "num literal transfer did not emit free-var non-negativity guard:\n" ^
    text);
  assert (contains "42" text,
    "num literal transfer did not normalize the numeral to Int 42:\n" ^ text)
end

fun num_transfer_operator_drive_success () =
let
  val text = transferred_smtlib_text
    ``!n m :num.
        Num (&n) + (n - m) + (n DIV SUC m) + (n MOD SUC m) <=
        MAX (SUC n) (MIN n m)``
in
  assert_pure_int_transfer "num operator transfer" text;
  assert (contains "div" text,
    "num operator transfer did not drive DIV to integer div:\n" ^ text);
  assert (contains "mod" text,
    "num operator transfer did not drive MOD to integer mod:\n" ^ text);
  assert (contains "ite" text,
    "num operator transfer did not preserve guarded subtraction/DIV/MOD:\n" ^
    text)
end

fun num_transfer_unguarded_num_corner_success () =
let
  val text = transferred_smtlib_text ``Num (i:int) = 0``
in
  assert_pure_int_transfer "unguarded Num transfer" text;
  assert (contains "ite" text,
    "unguarded Num did not normalize to its total integer encoding:\n" ^ text)
end

fun num_transfer_guarded_num_success () =
let
  val text = transferred_smtlib_text ``0i <= i ==> Num i = 0``
in
  assert_pure_int_transfer "guarded Num transfer" text;
  assert (contains "(assert (<= 0 v0))" text,
    "guarded Num transfer did not retain guard as integer assumption:\n" ^
    text);
  assert (contains "ite" text,
    "guarded Num transfer did not use the total integer Num encoding:\n" ^
    text)
end

fun num_transfer_assumption_free_var_success () =
let
  val text =
    transferred_smtlib_goal_text ([``(x:num) <= 1``], ``(x:num) <= 2``)
in
  assert_pure_int_transfer "num assumption transfer" text;
  assert (contains "(assert (<= 0 v0))" text,
    "num assumption transfer did not emit non-negativity guard:\n" ^ text);
  assert (contains "1" text andalso contains "2" text,
    "num assumption transfer did not retain integer bounds:\n" ^ text)
end

fun num_bridge_axioms_retired_success () =
let
  val text = transferred_smtlib_text ``(1:int) + 2 = 3``
in
  assert_not_contains "num bridge axiom retirement" "forall" text;
  assert_not_contains "num bridge axiom retirement" "Num" text;
  assert_not_contains "num bridge axiom retirement" "int_of_num" text
end

fun ceiling_builtin_encoding_success () =
let
  val text = transferred_smtlib_text ``clgtoks (x:real) = (0:int)``
in
  assert_not_contains "ceiling builtin encoding" "forall" text;
  assert (contains "to_int" text,
    "ceiling was not encoded through SMT-LIB to_int:\n" ^ text)
end

fun literal_power_unfolding_success () =
let
  val text = transferred_smtlib_text
    ``(x:real) pow 5 = x * x * x * x * x``
in
  assert_not_contains "literal real power unfolding" "(Real Int) Real" text;
  assert (contains "*" text,
    "literal real power did not emit multiplication:\n" ^ text)
end

fun symbolic_positive_power_transfer_success () =
let
  val one_text = transferred_smtlib_text ``(1:real) pow n = 1``
  val positive_text = transferred_smtlib_text ``0 < (42:real) pow n``
in
  assert_pure_int_transfer "symbolic unit-base power" one_text;
  assert_pure_int_transfer "symbolic positive-base power" positive_text
end

fun num_floor_ceiling_total_transfer_success () =
let
  val floor_text = transferred_smtlib_text ``flr (-4 / 3 :real) = (0:num)``
  val ceiling_text = transferred_smtlib_text ``clg (-4 / 3 :real) = (0:num)``
in
  assert_num_free_transfer "negative fractional num floor" floor_text;
  assert_num_free_transfer "negative fractional num ceiling" ceiling_text;
  assert (contains "to_int" floor_text andalso contains "to_int" ceiling_text,
    "floor/ceiling transfer did not use native SMT to_int:\n" ^
    floor_text ^ "\n" ^ ceiling_text)
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

fun parse_file_datatype_elaboration_options_success () =
let
  val options = {dict_logic = NONE, elaborate_datatypes = true}
  fun typecheck script =
    SmtLib_Parser.typecheck_script_string_with_options options script
  fun has_typebase_constructor tm =
    term_has_subterm (Lib.can TypeBase.is_constructor) tm
  fun assert_assertions label state =
    let val assertions = #assertions state
    in
      assert (not (List.null assertions),
        label ^ " produced no assertions");
      assert (List.all (fn tm => Term.type_of tm = Type.bool) assertions,
        label ^ " produced a non-Bool assertion");
      assert (List.exists has_typebase_constructor assertions,
        label ^ " assertion did not contain a TypeBase constructor")
    end
  val enum_state = typecheck
    ("(set-logic ALL)\n" ^
     "(declare-datatype ColorA2_09 ((redA2_09) (greenA2_09)))\n" ^
     "(assert (= redA2_09 greenA2_09))\n" ^
     "(exit)\n")
  val recursive_state = typecheck
    ("(set-logic ALL)\n" ^
     "(declare-datatype ListA2_09 " ^
     "((nilA2_09) (consA2_09 (headA2_09 Int) " ^
     "(tailA2_09 ListA2_09))))\n" ^
     "(assert (= (tailA2_09 (consA2_09 1 nilA2_09)) nilA2_09))\n" ^
     "(exit)\n")
  val mutual_state = typecheck
    ("(set-logic ALL)\n" ^
     "(declare-datatypes ((TreeA2_09 0) (ForestA2_09 0))\n" ^
     "  (((leafA2_09) (nodeA2_09 (childrenA2_09 ForestA2_09)))\n" ^
     "   ((nilFA2_09) (consFA2_09 (headFA2_09 TreeA2_09) " ^
     "(tailFA2_09 ForestA2_09)))))\n" ^
     "(assert ((_ is nodeA2_09) (nodeA2_09 nilFA2_09)))\n" ^
     "(exit)\n")
  val parametric_state = typecheck
    ("(set-logic ALL)\n" ^
     "(declare-datatype BoxA2_09 " ^
     "(par (T) ((boxA2_09 (valueA2_09 T)))))\n" ^
     "(declare-const biA2_09 (BoxA2_09 Int))\n" ^
     "(declare-const bbA2_09 (BoxA2_09 Bool))\n" ^
     "(assert (and (= (valueA2_09 (boxA2_09 1)) 1) " ^
     "((_ is boxA2_09) biA2_09)))\n" ^
     "(assert (and (= (valueA2_09 (boxA2_09 true)) true) " ^
     "((_ is boxA2_09) bbA2_09)))\n" ^
     "(exit)\n")
in
  assert_assertions "enum datatype elaboration" enum_state;
  assert_assertions "recursive datatype elaboration" recursive_state;
  assert_assertions "mutual datatype elaboration" mutual_state;
  assert_assertions "parametric datatype elaboration" parametric_state
end

fun parse_file_datatype_elaboration_flag_off_success () =
let
  val hol_tyop = "smtlib_dt_A2FlagOff09"
  val decls_before = Type.decls hol_tyop
  val state =
    parse_smtlib_state
      ("(set-logic ALL)\n" ^
       "(declare-datatype A2FlagOff09 " ^
       "((mkA2FlagOff09 (vA2FlagOff09 Int))))\n" ^
       "(assert (= (vA2FlagOff09 (mkA2FlagOff09 1)) 1))\n" ^
       "(exit)\n")
  val after = Type.decls hol_tyop
in
  assert (List.length (#assertions state) = 1,
    "flag-off datatype script produced the wrong assertion count");
  assert (decls_before = after,
    "flag-off datatype typecheck defined a TypeBase datatype")
end

fun expect_smtlib_typecheck_failure label options script diagnostic =
  (ignore (SmtLib_Parser.typecheck_script_string_with_options options script);
   die ("FAIL: " ^ label ^ " typechecked successfully"))
  handle HOL_ERR holerr =>
    let val msg = message_of holerr
    in
      assert (contains diagnostic msg,
        label ^ " diagnostic mismatch\nexpected substring: " ^
        diagnostic ^ "\nactual: " ^ msg)
    end

fun parse_file_datatype_match_elaboration_success () =
let
  val options = {dict_logic = NONE, elaborate_datatypes = true}
  val state =
    SmtLib_Parser.typecheck_script_string_with_options options
      ("(set-logic ALL)\n" ^
       "(declare-datatype MatchTreeA2_16 " ^
       "((leafA2_16 (valueA2_16 Int)) " ^
       "(nodeA2_16 (leftA2_16 MatchTreeA2_16) " ^
       "(rightA2_16 MatchTreeA2_16)) (emptyA2_16)))\n" ^
       "(declare-const tA2_16 MatchTreeA2_16)\n" ^
       "(declare-const xA2_16 Bool)\n" ^
       "(assert (= (match tA2_16\n" ^
       "  (((leafA2_16 xA2_16) xA2_16)\n" ^
       "   ((nodeA2_16 lA2_16 rA2_16)\n" ^
       "    (match lA2_16 (((leafA2_16 yA2_16) yA2_16) " ^
       "(fallbackA2_16 0))))\n" ^
       "   (emptyA2_16 2))) 0))\n" ^
       "(assert (= (match tA2_16 " ^
       "((emptyA2_16 0) (defaultA2_16 1))) 1))\n" ^
       "(exit)\n")
  val assertions = #assertions state
in
  assert (List.length assertions = 2,
    "match elaboration script produced the wrong assertion count");
  assert (List.all (fn tm => Term.type_of tm = Type.bool) assertions,
    "match elaboration produced a non-Bool assertion");
  assert (List.all (term_has_subterm (Lib.can TypeBase.dest_case))
      assertions,
    "match elaboration did not build TypeBase case terms")
end

fun parse_file_datatype_dependency_elaboration_success () =
let
  val options = {dict_logic = NONE, elaborate_datatypes = true}
  val state =
    SmtLib_Parser.typecheck_script_string_with_options options
      ("(set-logic ALL)\n" ^
       "(declare-datatype DependencyColorA2_17 " ^
       "((dependencyRedA2_17) (dependencyGreenA2_17)))\n" ^
       "(declare-datatype DependencyBoxA2_17 " ^
       "((dependencyBoxA2_17 " ^
       "(dependencyValueA2_17 DependencyColorA2_17))))\n" ^
       "(declare-const dependencyBoxValueA2_17 DependencyBoxA2_17)\n" ^
       "(assert (= (dependencyValueA2_17 dependencyBoxValueA2_17) " ^
       "dependencyRedA2_17))\n" ^
       "(declare-datatype DependencyWeirdA2_17 " ^
       "(par (L R) ((dependencyWeirdA2_17 " ^
       "(dependencyLeftA2_17 L) (dependencyRightA2_17 R)))))\n" ^
       "(declare-datatype DependencyHolderA2_17 " ^
       "(par (T) ((dependencyHolderA2_17 " ^
       "(dependencyPayloadA2_17 (DependencyWeirdA2_17 Int T))))))\n" ^
       "(declare-const dependencyHolderValueA2_17 " ^
       "(DependencyHolderA2_17 Bool))\n" ^
       "(assert (= (dependencyPayloadA2_17 dependencyHolderValueA2_17) " ^
       "(dependencyWeirdA2_17 1 true)))\n" ^
       "(exit)\n")
in
  assert (List.length (#assertions state) = 2,
    "datatype dependency elaboration produced the wrong assertion count");
  assert (List.all (fn tm => Term.type_of tm = Type.bool) (#assertions state),
    "datatype dependency elaboration produced a non-Bool assertion")
end

fun parse_file_datatype_match_source_order_success () =
let
  val options = {dict_logic = NONE, elaborate_datatypes = true}
  val state =
    SmtLib_Parser.typecheck_script_string_with_options options
      ("(set-logic ALL)\n" ^
       "(declare-datatype MatchOrderColorA2_17 " ^
       "((matchOrderRedA2_17) (matchOrderGreenA2_17)))\n" ^
       "(assert (match matchOrderRedA2_17 " ^
       "((matchOrderFallbackA2_17 true) (matchOrderRedA2_17 false))))\n" ^
       "(exit)\n")
  val assertion = hd (#assertions state)
in
  assert (not (term_has_subterm (fn tm => tm ~~ boolSyntax.F) assertion),
    "match lowering ignored an earlier default branch")
end

fun parse_file_datatype_match_negatives () =
let
  val options = {dict_logic = NONE, elaborate_datatypes = true}
  val base =
    "(set-logic ALL)\n" ^
    "(declare-datatype MatchColorA2_16 ((redA2_16) (greenA2_16)))\n" ^
    "(declare-const cA2_16 MatchColorA2_16)\n"
  val _ = expect_smtlib_typecheck_failure
    "non-exhaustive match" options
    (base ^
     "(assert (= (match cA2_16 ((redA2_16 0))) 0))\n" ^
     "(exit)\n")
    "non-exhaustive match"
  val _ = expect_smtlib_typecheck_failure
    "unknown constructor match" options
    (base ^
     "(assert (= (match cA2_16 (((blueA2_16 xA2_16) 0) " ^
     "(fallbackA2_16 1))) 1))\n" ^
     "(exit)\n")
    "unknown match constructor 'blueA2_16'"
  val _ = expect_smtlib_typecheck_failure
    "duplicate constructor match" options
    (base ^
     "(assert (= (match cA2_16 ((redA2_16 0) " ^
     "(redA2_16 1) (greenA2_16 2))) 0))\n" ^
     "(exit)\n")
    "duplicate match constructor pattern 'redA2_16'"
in
  ()
end

fun parse_file_datatype_match_placeholder_rejection () =
let
  val options = {dict_logic = NONE, elaborate_datatypes = false}
in
  expect_smtlib_typecheck_failure
    "placeholder match rejection" options
    ("(set-logic ALL)\n" ^
     "(declare-datatype MatchPlaceholderA2_16 " ^
     "((mkMatchPlaceholderA2_16 (vMatchPlaceholderA2_16 Int))))\n" ^
     "(declare-const pMatchPlaceholderA2_16 MatchPlaceholderA2_16)\n" ^
     "(assert (= (match pMatchPlaceholderA2_16 " ^
     "(((mkMatchPlaceholderA2_16 xMatchPlaceholderA2_16) " ^
     "xMatchPlaceholderA2_16))) 0))\n" ^
     "(exit)\n")
    "placeholder datatype mode cannot support binding patterns soundly"
end

fun holsmtlib_z3_tac_datatype_flag_leakage_guard () =
let
  fun existing path = OS.FileSys.access (path, [OS.FileSys.A_READ])
  val path =
    if existing "HolSmtLib.sml" then "HolSmtLib.sml"
    else "src/HolSmt/HolSmtLib.sml"
  val source = read_text_file path
in
  assert (not (String.isSubstring "elaborate_datatypes" source),
    "HolSmtLib mentions the datatype elaboration flag");
  assert (not (String.isSubstring "typecheck_script_with_options" source),
    "HolSmtLib uses the parser options entry point");
  assert (not (String.isSubstring "parse_file_state_with_options" source),
    "HolSmtLib uses the parser options entry point")
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

fun datatype_command script =
  case SmtLib_Parser.parse_script_string script of
    [command] =>
      (case SmtLib_Parser.node_of command of
         SmtLib_Parser.CmdDeclareDatatype (name, decl) => (name, decl)
       | _ => die "expected declare-datatype command")
  | _ => die "expected one datatype command"

fun datatypes_command script =
  case SmtLib_Parser.parse_script_string script of
    [command] =>
      (case SmtLib_Parser.node_of command of
         SmtLib_Parser.CmdDeclareDatatypes (bindings, decls) =>
           (bindings, decls)
       | _ => die "expected declare-datatypes command")
  | _ => die "expected one datatypes command"

fun smtlib_datatype_elaboration_core_success () =
let
  fun has_option opt = case opt of SOME _ => true | NONE => false
  fun assert_tyinfo label tyi =
    let
      val ty = TypeBasePure.ty_of tyi
      val constructors = TypeBasePure.constructors_of tyi
      val one_one = TypeBasePure.one_one_of tyi
      val distinct = TypeBasePure.distinct_of tyi
    in
      assert (not (List.null constructors),
        label ^ " had no TypeBase constructors");
      assert (has_option one_one, label ^ " had no one_one theorem");
      assert (has_option distinct, label ^ " had no distinct theorem");
      assert (has_option (TypeBase.fetch ty),
        label ^ " type was not registered in TypeBase")
    end
  fun define_one script =
    SmtLib_Datatypes.define_datatype (datatype_command script)
  fun define_group script =
    SmtLib_Datatypes.define_datatypes (datatypes_command script)
  fun const_name tm =
    #Name (Term.dest_thy_const tm)
    handle Feedback.HOL_ERR _ => Lib.fst (Term.dest_const tm)
  fun constructor_args ty =
    case Lib.total Type.dom_rng ty of
      NONE => []
    | SOME (domain, range) => domain :: constructor_args range
  fun constructor_pattern ctor =
    let
      val arg_tys = constructor_args (Term.type_of ctor)
      val vars = List.tabulate (List.length arg_tys,
        fn i => Term.mk_var ("x" ^ Int.toString i, List.nth (arg_tys, i)))
    in
      (Term.list_mk_comb (ctor, vars), vars)
    end
  fun lookup kind names smt =
    case SmtLib_Datatypes.lookup_smt kind names smt of
      SOME hol => hol
    | NONE => die ("missing datatype name-map entry for " ^ smt)

  val simple = define_one
    "(declare-datatype SimpleA1 ((simpleA) (simpleB (ival Int))))"
  val recursive = define_one
    ("(declare-datatype RecListA1 " ^
     "((nilA) (consA (head Int) (tail RecListA1))))")
  val mutual = define_group
    ("(declare-datatypes ((MutTreeA1 0) (MutForestA1 0)) " ^
     "(((leafA) (nodeA (forest MutForestA1))) " ^
     "((emptyA) (consForestA (tree MutTreeA1) (rest MutForestA1)))))")
  val parametric = define_one
    "(declare-datatype BoxA1 (par (T) ((emptyBox) (box (value T)))))"
  val _ = List.app (fn (label, tyi) => assert_tyinfo label tyi)
    [("simple", hd (#tyinfos simple)),
     ("recursive", hd (#tyinfos recursive)),
     ("mutual-tree", hd (#tyinfos mutual)),
     ("mutual-forest", hd (tl (#tyinfos mutual))),
     ("parametric", hd (#tyinfos parametric))]

  val cache1 = define_one
    "(declare-datatype CacheA1 ((cacheNil) (cacheCons (v Int))))"
  val cache2 = define_one
    "(declare-datatype CacheA1 ((cacheNil) (cacheCons (v Int))))"
  val _ = assert (#hol_types cache1 = #hol_types cache2,
    "identical datatype declaration did not hit the cache")

  val collision = define_one
    "(declare-datatype List ((nil) (cons (head Int) (tail List))))"
  val collision_ty =
    lookup SmtLib_Datatypes.TypeName (#names collision) "List"
  val collision_cons =
    lookup SmtLib_Datatypes.ConstructorName (#names collision) "cons"
  val _ = assert (collision_ty <> "List" andalso
                  String.isPrefix "smtlib_dt_" collision_ty,
    "datatype type name collision was not freshened")
  val _ = assert (collision_cons <> "cons" andalso
                  String.isPrefix "smtlib_dt_ctor_" collision_cons,
    "constructor name collision was not freshened")

  val same1 = define_one
    "(declare-datatype SameA1 ((sameMk (x Int))))"
  val same2 = define_one
    "(declare-datatype SameA1 ((sameMk (x Bool))))"
  val _ = assert (#hol_types same1 <> #hol_types same2,
    "different datatype structures with the same SMT name reused a HOL type")

  val pair_decl = define_one
    ("(declare-datatype MaybePairA1 " ^
     "((none) (mk (left Int) (right Bool))))")
  val pair_ty = hd (#hol_types pair_decl)
  val pair_names = #names pair_decl
  val mk_hol = lookup SmtLib_Datatypes.ConstructorName pair_names "mk"
  val p = Term.mk_var ("p", pair_ty)
  val ctors = TypeBase.constructors_of pair_ty
  fun selector_branch ctor =
    let
      val (pat, vars) = constructor_pattern ctor
      val rhs =
        if const_name ctor = mk_hol then hd vars
        else boolSyntax.mk_arb intSyntax.int_ty
    in
      (pat, rhs)
    end
  fun tester_branch ctor =
    let val (pat, _) = constructor_pattern ctor
    in
      (pat, if const_name ctor = mk_hol then boolSyntax.T else boolSyntax.F)
    end
  val selector_actual =
    SmtLib_Datatypes.mk_selector_case
      {selector = "left", constructor = "mk", scrutinee = p}
  val selector_expected = TypeBase.mk_case (p, List.map selector_branch ctors)
  val tester_actual =
    SmtLib_Datatypes.mk_tester_case {constructor = "mk", scrutinee = p}
  val tester_expected = TypeBase.mk_case (p, List.map tester_branch ctors)
in
  assert (selector_actual ~~ selector_expected,
    "selector builder produced " ^ term_with_types selector_actual ^
    ", expected " ^ term_with_types selector_expected);
  assert (tester_actual ~~ tester_expected,
    "tester builder produced " ^ term_with_types tester_actual ^
    ", expected " ^ term_with_types tester_expected)
end

fun smtlib_datatype_elaboration_wellfounded_diagnostic () =
  let
    val _ = SmtLib_Datatypes.define_datatype
      (datatype_command
        "(declare-datatype D ((mk (self D))))")
  in
    die "ill-founded datatype declaration was accepted"
  end
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (contains "datatype declaration 'D' is not well-founded" msg,
        "well-foundedness diagnostic mismatch: " ^ msg)
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

fun parse_legacy_define_fun_rec_hypothesis_only_success () =
let
  val {assertions, local_definitions, queries, ...} =
    parse_legacy_smtlib_state
      ("(set-logic QF_UF)\n" ^
       "(define-fun-rec f ((p Bool)) Bool (f p))\n" ^
       "(define-funs-rec ((g ((p Bool)) Bool) (h ((p Bool)) Bool)) " ^
       "((h p) (g p)))\n" ^
       "(assert (not (f true)))\n" ^
       "(check-sat)\n")
  val recursive_equations = List.filter boolSyntax.is_forall assertions
in
  assert (List.length assertions = 4,
    "legacy recursive definitions were not added as hypothesis assertions");
  assert (List.length recursive_equations = 3,
    "legacy recursive definition equations were not universally quantified");
  assert (List.null local_definitions,
    "legacy recursive definitions were installed as local definitions");
  assert (List.exists (fn query =>
      case query of
        SmtLib_Parser.QueryCheckSat
          {assertions = query_assertions, local_definitions = query_defs,
           assumptions = []} =>
          List.length query_assertions = 4 andalso List.null query_defs
      | _ => false) queries,
    "legacy check-sat query did not preserve recursive hypotheses")
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

fun smtlib_int_real_operator_coercion_success () =
let
  val script =
    "(set-logic QF_LIRA)\n" ^
    "(declare-const x Int)\n" ^
    "(declare-const y Real)\n" ^
    "(assert (= (+ x y) 3.0))\n" ^
    "(exit)\n"
  val legacy_assertions = parse_legacy_smtlib_assertions script
  val {assertions = checked_assertions, ...} = parse_smtlib_state script
in
  assert (List.length legacy_assertions = 1,
    "legacy operator coercion script produced wrong assertion count");
  assert (List.length checked_assertions = 1,
    "typechecked operator coercion script produced wrong assertion count");
  assert (term_has_real_of_int (List.hd legacy_assertions),
    "legacy operator coercion did not insert real_of_int");
  assert (term_has_real_of_int (List.hd checked_assertions),
    "typechecked operator coercion did not insert real_of_int")
end

fun smtlib_int_real_user_function_coercion_success () =
let
  val script =
    "(set-logic QF_UFLIRA)\n" ^
    "(declare-const x Int)\n" ^
    "(declare-fun p (Real) Bool)\n" ^
    "(assert (p x))\n" ^
    "(exit)\n"
  val legacy_assertions = parse_legacy_smtlib_assertions script
  val {assertions = checked_assertions, ...} = parse_smtlib_state script
in
  assert (List.length legacy_assertions = 1,
    "legacy user-function coercion script produced wrong assertion count");
  assert (List.length checked_assertions = 1,
    "typechecked user-function coercion script produced wrong assertion count");
  assert (term_has_real_of_int (List.hd legacy_assertions),
    "legacy user-function coercion did not insert real_of_int");
  assert (term_has_real_of_int (List.hd checked_assertions),
    "typechecked user-function coercion did not insert real_of_int")
end

fun smtlib_int_only_no_spurious_coercion_success () =
let
  val script =
    "(set-logic QF_LIA)\n" ^
    "(declare-const x Int)\n" ^
    "(declare-fun p (Int) Bool)\n" ^
    "(assert (p x))\n" ^
    "(exit)\n"
  val legacy_assertions = parse_legacy_smtlib_assertions script
  val {assertions = checked_assertions, ...} = parse_smtlib_state script
in
  assert (List.length legacy_assertions = 1,
    "legacy Int-only script produced wrong assertion count");
  assert (List.length checked_assertions = 1,
    "typechecked Int-only script produced wrong assertion count");
  assert (not (term_has_real_of_int (List.hd legacy_assertions)),
    "legacy Int-only script inserted a spurious real_of_int");
  assert (not (term_has_real_of_int (List.hd checked_assertions)),
    "typechecked Int-only script inserted a spurious real_of_int")
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

fun smtlib_declare_sort_parametric_success () =
let
  val script =
    "(set-logic QF_UF)\n" ^
    "(declare-sort A 0)\n" ^
    "(declare-sort B 0)\n" ^
    "(declare-sort Box 1)\n" ^
    "(declare-sort Pair 2)\n" ^
    "(declare-const x1 (Box A))\n" ^
    "(declare-const x2 (Box A))\n" ^
    "(declare-const y (Box B))\n" ^
    "(declare-const p (Pair A B))\n" ^
    "(declare-const q (Pair B A))\n" ^
    "(assert (= x1 x2))\n" ^
    "(assert (= y y))\n" ^
    "(assert (= p p))\n" ^
    "(assert (= q q))\n" ^
    "(exit)\n"
  fun check_assertions label assertions =
    let
      val vars = List.concat (List.map Term.free_vars assertions)
      fun var_ty name =
        case List.find (fn tm => Lib.fst (Term.dest_var tm) = name) vars of
          SOME tm => Lib.snd (Term.dest_var tm)
        | NONE => die (label ^ " missing free variable " ^ name)
      val x1_ty = var_ty "x1"
      val x2_ty = var_ty "x2"
      val y_ty = var_ty "y"
      val p_ty = var_ty "p"
      val q_ty = var_ty "q"
      fun same ty1 ty2 = Type.compare (ty1, ty2) = EQUAL
    in
      assert (List.length assertions = 4,
        label ^ " parametric declare-sort assertion count mismatch");
      assert (same x1_ty x2_ty,
        label ^ " did not share equal Box A instantiations");
      assert (not (same x1_ty y_ty),
        label ^ " equated distinct Box instantiations");
      assert (not (same p_ty q_ty),
        label ^ " equated distinct Pair instantiations");
      assert (not (same x1_ty p_ty),
        label ^ " equated distinct declared sort constructors")
    end
  val legacy_assertions = parse_legacy_smtlib_assertions script
  val {assertions = checked_assertions, ...} = parse_smtlib_state script
in
  check_assertions "legacy parser" legacy_assertions;
  check_assertions "typechecker" checked_assertions
end

fun smtlib_declare_sort_parametric_arity_diagnostics () =
let
  fun script body =
    "(set-logic QF_UF)\n" ^
    "(declare-sort A 0)\n" ^
    "(declare-sort Box 1)\n" ^
    body ^
    "(exit)\n"
  val too_few = script "(declare-const bad Box)\n"
  val too_many = script "(declare-const bad (Box A A))\n"
  fun legacy text () = ignore (parse_legacy_smtlib_assertions text)
  fun typecheck text () = ignore (SmtLib_Parser.typecheck_script_string text)
in
  expect_hol_error_contains "legacy declare-sort arity too few"
    "declare-sort arity mismatch for 'Box': expected 1, actual 0"
    (legacy too_few);
  expect_hol_error_contains "legacy declare-sort arity too many"
    "declare-sort arity mismatch for 'Box': expected 1, actual 2"
    (legacy too_many);
  expect_hol_error_contains "typecheck declare-sort arity too few"
    "declare-sort arity mismatch for 'Box': expected 1, actual 0"
    (typecheck too_few);
  expect_hol_error_contains "typecheck declare-sort arity too many"
    "declare-sort arity mismatch for 'Box': expected 1, actual 2"
    (typecheck too_many)
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
    fun fragment_with_options options logic text =
      let
        val state = parse_smtlib_state_with_options options text
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
    fun expect_no_fragment_with_options label options logic text =
      case fragment_with_options options logic text of
        SOME msg =>
          die (label ^ " reported a spurious fragment violation: " ^ msg)
      | NONE => ()
    fun expect_term_fragment label logic term expected =
      case SmtLib_Logics.fragment_violation_diagnostic logic [term] of
        SOME msg =>
          assert (contains expected msg,
            label ^ " diagnostic missed '" ^ expected ^ "': " ^ msg)
      | NONE => die (label ^ " fragment violation was not detected")
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
    expect_fragment "datatype sort unavailable" "QF_UF"
      (script_for_checker "ALL"
       "(declare-datatype D ((mkD)))\n" ^
       "(declare-const d D)\n" ^
       "(assert (= d mkD))\n")
      "datatype sort is outside logic fragment QF_UF";
    expect_no_fragment "placeholder datatype sort available" "QF_DT"
      (script "QF_DT"
       "(declare-datatype D ((mkD)))\n" ^
       "(declare-const d D)\n" ^
       "(assert (= d mkD))\n");
    expect_no_fragment_with_options "TypeBase datatype sort available"
      {dict_logic = NONE, elaborate_datatypes = true} "QF_DT"
      (script "QF_DT"
       "(declare-datatype E ((mkE)))\n" ^
       "(declare-const e E)\n" ^
       "(assert (= e mkE))\n");
    expect_term_fragment "native list datatype sort unavailable" "QF_UFLIA"
      ``([]:int list) = []``
      "datatype sort is outside logic fragment QF_UFLIA";
    expect_term_fragment "native unit datatype sort unavailable" "QF_UFLIA"
      ``(():unit) = ()``
      "datatype sort is outside logic fragment QF_UFLIA";
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

fun smtlib_and_or_right_assoc_parse_shape_success () =
let
  val assertions =
    parse_smtlib_assertions
      ("(set-logic QF_UF)\n" ^
       "(declare-const a Bool)\n" ^
       "(declare-const b Bool)\n" ^
       "(declare-const c Bool)\n" ^
       "(assert (and a b c))\n" ^
       "(assert (or a b c))\n" ^
       "(exit)\n")
  val a = Term.mk_var ("a", Type.bool)
  val b = Term.mk_var ("b", Type.bool)
  val c = Term.mk_var ("c", Type.bool)
  fun assert_and_shape tm =
    let
      val (left, right) = boolSyntax.dest_conj tm
      val (mid, last) = boolSyntax.dest_conj right
    in
      assert (Term.aconv left a andalso Term.aconv mid b andalso
        Term.aconv last c,
        "(and a b c) did not parse as a /\\ (b /\\ c)")
    end
  fun assert_or_shape tm =
    let
      val (left, right) = boolSyntax.dest_disj tm
      val (mid, last) = boolSyntax.dest_disj right
    in
      assert (Term.aconv left a andalso Term.aconv mid b andalso
        Term.aconv last c,
        "(or a b c) did not parse as a \\/ (b \\/ c)")
    end
in
  case assertions of
    [and_tm, or_tm] => (assert_and_shape and_tm; assert_or_shape or_tm)
  | _ => die "and/or associativity script produced wrong assertion count"
end

fun smtlib_core_symbol_metadata_success () =
let
  val metadata = SmtLib_Logics.metadata_of_logic "QF_UF"
  val eq_symbol = find_symbol_metadata "Core" "term" "=" metadata
  val distinct_symbol = find_symbol_metadata "Core" "term" "distinct" metadata
  val and_symbol = find_symbol_metadata "Core" "term" "and" metadata
  val or_symbol = find_symbol_metadata "Core" "term" "or" metadata
  val bool_symbol = find_symbol_metadata "Core" "sort" "Bool" metadata
  val eq_attrs = #attributes eq_symbol
  val distinct_attrs = #attributes distinct_symbol
  val and_attrs = #attributes and_symbol
  val or_attrs = #attributes or_symbol
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
    "and metadata did not record its official left-associative attribute");
  assert (#left_associative or_attrs,
    "or metadata did not record its official left-associative attribute")
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
    "AUFNIRA", "AUFDTLIA", "AUFDTLIRA", "AUFDTNIRA", "AUFBVDT",
    "AUFBVDTLIA", "AUFBVDTNIA", "AUFBVDTNIRA", "BV", "LIA", "LRA",
    "NIA", "NRA", "UF", "UFBV", "UFBVDT", "UFIDL", "UFDT",
    "UFDTLIA", "UFDTLIRA", "UFDTNIA", "UFDTNIRA", "UFLIA", "UFLRA",
    "UFNIA", "UFNRA",
    "QF_ABV", "QF_ALIA", "QF_ALRA", "QF_ANIA", "QF_ANRA",
    "QF_AUFBV", "QF_AUFLIA", "QF_AUFLIRA", "QF_AUFNIA",
    "QF_AUFNIRA", "QF_AX", "QF_BV", "QF_DT", "QF_IDL", "QF_LIA",
    "QF_LIRA", "QF_LRA", "QF_NIA", "QF_NIRA", "QF_NRA",
    "QF_RDL", "QF_UF", "QF_UFBV", "QF_UFDT", "QF_UFDTLIA",
    "QF_UFDTLIRA", "QF_UFDTNIA", "QF_UFIDL", "QF_UFLIA",
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
      val fragment = SmtLib_Logics.logic_fragment_of_logic logic
      val was_legacy_linear =
        List.exists (fn linear_logic => logic = linear_logic)
          legacy_linear_logics
      val has_dt = String.isSubstring "DT"
        (if String.isPrefix "QF_" logic then String.extract (logic, 3, NONE)
         else logic)
    in
      assert (not (List.null metadata),
        "logic metadata was empty for " ^ logic);
      assert (not was_legacy_linear orelse
              SmtLib_Logics.is_linear_arith_logic logic,
        "legacy linear-arithmetic logic no longer classified linear: " ^
        logic);
      assert (#datatypes fragment = (logic = "ALL" orelse has_dt),
        "datatype fragment bit was wrong for " ^ logic)
    end
in
  List.app require_logic logics
end

fun smtlib_translation_logic_inference_success () =
let
  fun mk_features (quantifiers, uninterpreted, arrays, bitvectors,
                   integers, reals, strings, nonlinear) =
    SmtLib.LogicFeatures {
      quantifiers = quantifiers, uninterpreted = uninterpreted,
      arrays = arrays, bitvectors = bitvectors, integers = integers,
      reals = reals, strings = strings, datatypes = false,
      nonlinear = nonlinear}
  fun mk_datatype_features (quantifiers, uninterpreted, arrays, bitvectors,
                            integers, reals, strings, nonlinear) =
    SmtLib.LogicFeatures {
      quantifiers = quantifiers, uninterpreted = uninterpreted,
      arrays = arrays, bitvectors = bitvectors, integers = integers,
      reals = reals, strings = strings, datatypes = true,
      nonlinear = nonlinear}
  fun expect_features expected (name, feature_tuple) =
    let
      val (logic, reason) =
        SmtLib.infer_logic_from_features (mk_features feature_tuple)
    in
      assert (logic = expected,
        "feature-vector inference '" ^ name ^ "' expected " ^ expected ^
        ", got " ^ logic ^ " (" ^ reason ^ ")")
    end
  fun expect_datatype_features expected (name, feature_tuple) =
    let
      val (logic, reason) =
        SmtLib.infer_logic_from_features (mk_datatype_features feature_tuple)
    in
      assert (logic = expected,
        "datatype feature-vector inference '" ^ name ^ "' expected " ^
        expected ^ ", got " ^ logic ^ " (" ^ reason ^ ")")
    end
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
  List.app (expect_features "QF_UF") [
    ("core", (false, false, false, false, false, false, false, false))
  ];
  List.app (expect_features "QF_LIA") [
    ("linear integer", (false, false, false, false, true, false,
      false, false))
  ];
  List.app (expect_features "QF_NIA") [
    ("nonlinear integer", (false, false, false, false, true, false,
      false, true))
  ];
  List.app (expect_features "QF_LRA") [
    ("linear real", (false, false, false, false, false, true,
      false, false))
  ];
  List.app (expect_features "QF_BV") [
    ("bitvectors", (false, false, false, true, false, false,
      false, false))
  ];
  List.app (expect_features "QF_UFBV") [
    ("bitvectors with UF", (false, true, false, true, false, false,
      false, false))
  ];
  List.app (expect_features "QF_AX") [
    ("quantifier-free arrays", (false, false, true, false, false, false,
      false, false))
  ];
  List.app (expect_features "QF_AUFLIA") [
    ("quantifier-free arrays LIA", (false, false, true, false, true,
      false, false, false))
  ];
  List.app (expect_features "QF_S") [
    ("strings", (false, false, false, false, false, false, true, false))
  ];
  List.app (expect_features "QF_SLIA") [
    ("strings LIA", (false, false, false, false, true, false, true,
      false))
  ];
  List.app (expect_features "QF_SNIA") [
    ("strings NIA", (false, false, false, false, true, false, true, true))
  ];
  List.app (expect_datatype_features "QF_DT") [
    ("datatypes", (false, false, false, false, false, false, false, false))
  ];
  List.app (expect_datatype_features "QF_UFDT") [
    ("datatypes with UF", (false, true, false, false, false, false,
      false, false))
  ];
  List.app (expect_datatype_features "QF_UFDTLIA") [
    ("datatypes with LIA", (false, false, false, false, true, false,
      false, false))
  ];
  List.app (expect_datatype_features "QF_UFDTLIRA") [
    ("datatypes with LIRA", (false, false, false, false, true, true,
      false, false))
  ];
  List.app (expect_datatype_features "QF_UFDTNIA") [
    ("datatypes with NIA", (false, false, false, false, true, false,
      false, true))
  ];
  List.app (expect_datatype_features "UFDT") [
    ("quantified datatypes", (true, false, false, false, false, false,
      false, false))
  ];
  List.app (expect_datatype_features "UFDTLIA") [
    ("quantified datatypes with LIA", (true, false, false, false, true,
      false, false, false))
  ];
  List.app (expect_datatype_features "UFDTLIRA") [
    ("quantified datatypes with LRA", (true, false, false, false, false,
      true, false, false)),
    ("quantified datatypes with LIRA", (true, false, false, false, true,
      true, false, false))
  ];
  List.app (expect_datatype_features "UFDTNIA") [
    ("quantified datatypes with NIA", (true, false, false, false, true,
      false, false, true))
  ];
  List.app (expect_datatype_features "UFDTNIRA") [
    ("quantified datatypes with NRA", (true, false, false, false, false,
      true, false, true)),
    ("quantified datatypes with NIRA", (true, false, false, false, true,
      true, false, true))
  ];
  List.app (expect_datatype_features "AUFDTLIA") [
    ("datatypes with arrays", (false, false, true, false, false, false,
      false, false)),
    ("datatypes with arrays LIA", (false, false, true, false, true, false,
      false, false))
  ];
  List.app (expect_datatype_features "AUFDTLIRA") [
    ("datatypes with arrays LRA", (false, false, true, false, false, true,
      false, false)),
    ("datatypes with arrays LIRA", (false, false, true, false, true, true,
      false, false))
  ];
  List.app (expect_datatype_features "AUFDTNIRA") [
    ("datatypes with arrays NIA", (false, false, true, false, true, false,
      false, true)),
    ("datatypes with arrays NRA", (false, false, true, false, false, true,
      false, true))
  ];
  List.app (expect_datatype_features "UFBVDT") [
    ("datatypes with bitvectors", (false, false, false, true, false, false,
      false, false)),
    ("datatypes with bitvectors UF", (false, true, false, true, false,
      false, false, false))
  ];
  List.app (expect_datatype_features "AUFBVDT") [
    ("datatypes with arrays bitvectors", (false, false, true, true, false,
      false, false, false))
  ];
  List.app (expect_features "ALL") [
    ("mixed strings", (false, true, false, false, false, false, true,
      false)),
    ("quantified bitvectors", (true, false, false, true, false, false,
      false, false))
  ];
  List.app (expect_features "ALIA") [
    ("quantified arrays", (true, false, true, false, false, false,
      false, false)),
    ("quantified arrays LIA", (true, false, true, false, true, false,
      false, false))
  ];
  List.app (expect_features "AUFLIA") [
    ("quantified arrays UF", (true, true, true, false, false, false,
      false, false)),
    ("quantified arrays UF LIA", (true, true, true, false, true, false,
      false, false))
  ];
  List.app (expect_features "ANIA") [
    ("quantified arrays NIA", (true, false, true, false, true, false,
      false, true))
  ];
  List.app (expect_features "AUFNIRA") [
    ("quantified arrays UF NIA", (true, true, true, false, true, false,
      false, true)),
    ("quantified arrays UF NRA", (true, true, true, false, false, true,
      false, true))
  ];
  List.app (expect_features "ALIRA") [
    ("quantified arrays LRA", (true, false, true, false, false, true,
      false, false)),
    ("quantified arrays LIRA", (true, false, true, false, true, true,
      false, false))
  ];
  List.app (expect_features "AUFLIRA") [
    ("quantified arrays UF LRA", (true, true, true, false, false, true,
      false, false)),
    ("quantified arrays UF LIRA", (true, true, true, false, true, true,
      false, false))
  ];
  List.app (expect_features "ANIRA") [
    ("quantified arrays NRA", (true, false, true, false, false, true,
      false, true)),
    ("quantified arrays NIRA", (true, false, true, false, true, true,
      false, true))
  ];
  expect_logic "QF_LIA" ``(x:int) <= x + 1``;
  expect_logic "QF_NIA" ``(x:int) * y = y * x``;
  expect_logic "QF_BV" ``(x:word32) && y = y && x``;
  expect_logic "QF_UFLIA" ``smtlib_uf_logic_foo (x:int) = x``;
  expect_logic "QF_AX" ``(P:'a -> bool) x``;
  expect_logic "QF_AX" ``(f:'a -> 'b) x = f x``;
  expect_logic "QF_DT" ``(x:ordering) = y``;
  expect_logic "QF_UFDTLIA" ``CONS (x:int) xs = CONS y ys``;
  expect_logic "AUFLIA" ``!(x:'a). (P:'a -> bool) x``
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

fun z3_414_logic_policy_success () =
let
  fun features arrays = SmtLib.LogicFeatures {
    quantifiers = true, uninterpreted = false, arrays = arrays,
    bitvectors = false, integers = true, reals = false, strings = false,
    datatypes = true, nonlinear = false}
  fun selection version logic arrays =
    Z3.z3_414_logic_policy version {
      features = features arrays, inferred_logic = logic,
      reason = "deterministic feature scan: test"}
  fun expect_widened version logic =
    case selection (SOME version) logic true of
      SOME {logic = "ALL", reason} =>
        assert (contains "deterministic feature scan: test" reason andalso
                contains "Z3 4.14.x" reason,
          "Z3 4.14 policy did not preserve and extend the logic reason")
    | SOME {logic = selected, ...} =>
        die ("FAIL: Z3 4.14 policy selected " ^ selected ^
          " instead of ALL for " ^ logic)
    | NONE => die ("FAIL: Z3 4.14 policy did not widen " ^ logic)
  fun expect_unchanged label version logic arrays =
    case selection version logic arrays of
      NONE => ()
    | SOME {logic = selected, ...} =>
        die ("FAIL: Z3 4.14 policy changed " ^ label ^ " to " ^ selected)
  val affected = [
    "ALIRA", "ANIA", "ANIRA",
    "AUFDTLIA", "AUFDTLIRA", "AUFDTNIRA", "AUFBVDT"
  ]
in
  List.app
    (fn version => List.app (expect_widened version) affected)
    ["4.14.0", "4.14.1", "4.14.99"];
  List.app
    (fn logic =>
      (expect_unchanged "Z3 4.13 neighbor" (SOME "4.13.0") logic true;
       expect_unchanged "Z3 4.15 neighbor" (SOME "4.15.3") logic true;
       expect_unchanged "array-free feature vector" (SOME "4.14.1")
         logic false))
    affected;
  expect_unchanged "unrelated logic" (SOME "4.14.1") "QF_LIA" true;
  List.app
    (fn version => expect_unchanged "malformed or unknown version" version
       "AUFDTLIA" true)
    [NONE, SOME "", SOME "0", SOME "4.14", SOME "4.14.x",
     SOME "4.14.1.0"]
end

fun z3_414_array_datatype_translation_success () =
let
  val compatibility_reason = "Z3 4.14.x array-logic compatibility widening"
  val terms = [
    ("list nil", ``list_CASE [] n c = n``),
    ("list cons", ``list_CASE (x::xs) n c = c x xs``),
    ("option some", ``option_CASE (SOME x) n s = s x``),
    ("option none", ``option_CASE NONE n s = n``),
    ("symbolic option", ``option_CASE ov n s = n``)
  ]
  fun logic_reason translation =
    case List.find
      (fn SmtLib.LogicSelection _ => true | _ => false)
      (SmtLib.translation_records translation) of
      SOME (SmtLib.LogicSelection {logic, reason, ...}) => (logic, reason)
    | _ => die "FAIL: translation has no LogicSelection record"
  fun check_term (name, tm) =
    let
      val (generic, _) = SmtLib.goal_to_SmtLib_translation NONE ([], tm)
      val generic_logic = SmtLib.translation_logic generic
      fun translated proof version =
        if proof then
          Z3.goal_to_SmtLib_with_get_proof_translation_for_version
            (SOME version) ([], tm)
        else
          Z3.goal_to_SmtLib_translation_for_version
            (SOME version) ([], tm)
      fun check_414 version proof =
        let
          val (translation, strings) = translated proof version
          val text = String.concat strings
          val (record_logic, reason) = logic_reason translation
        in
          assert (SmtLib.translation_logic translation = "ALL" andalso
                  record_logic = "ALL",
            name ^ " did not record ALL under Z3 " ^ version);
          assert (List.hd strings = "(set-logic ALL)\n",
            name ^ " did not emit set-logic ALL under Z3 " ^ version);
          assert (contains compatibility_reason reason,
            name ^ " did not record the Z3 compatibility reason");
          assert (contains "(declare-datatypes" text andalso
                  contains "Array" text andalso contains "(_ is" text andalso
                  contains "sel_" text andalso contains "(select" text,
            name ^ " lost array/datatype case encoding under Z3 " ^ version);
          assert ((if proof then contains "(get-proof)" text
                   else not (contains "(get-proof)" text)),
            name ^ " used the wrong proof command suffix")
        end
      fun check_neighbor version =
        let
          val (translation, strings) = translated false version
        in
          assert (SmtLib.translation_logic translation = generic_logic,
            name ^ " changed logic on neighbor Z3 " ^ version);
          assert (List.hd strings =
              "(set-logic " ^ generic_logic ^ ")\n",
            name ^ " emitted a mismatched neighbor set-logic command")
        end
    in
      assert (generic_logic = "AUFDTLIA",
        name ^ " generic inference changed from AUFDTLIA to " ^
        generic_logic);
      List.app (fn version => (check_414 version false;
                               check_414 version true))
        ["4.14.0", "4.14.99"];
      List.app check_neighbor ["4.13.0", "4.15.3"]
    end
in
  List.app check_term terms
end

fun z3_414_all_inferred_families_translation_success () =
let
  val representatives = [
    ("ALIRA", ``!(x:real). (f:real -> real) x = f x``),
    ("ANIA", ``!(x:int). (f:int -> int) (x * x) = f (x * x)``),
    ("ANIRA", ``!(x:real). (f:real -> real) (x * x) = f (x * x)``),
    ("AUFDTLIA", ``option_CASE (SOME (x:int)) n s = s x``),
    ("AUFDTLIRA", ``option_CASE (SOME (x:real)) n s = s x + 0r``),
    ("AUFDTNIRA", ``option_CASE (SOME (x:real)) n s = s x * 1r``),
    ("AUFBVDT",
      ``option_CASE (SOME (x:'a)) (n:word32) (s:'a -> word32) = s x``)
  ]
  fun check (expected, tm) =
    let
      val (generic, _) = SmtLib.goal_to_SmtLib_translation NONE ([], tm)
      val (affected, affected_strings) =
        Z3.goal_to_SmtLib_translation_for_version (SOME "4.14.1") ([], tm)
      fun neighbor version =
        Lib.fst (Z3.goal_to_SmtLib_translation_for_version
          (SOME version) ([], tm))
    in
      assert (SmtLib.translation_logic generic = expected,
        "representative expected " ^ expected ^ ", inferred " ^
        SmtLib.translation_logic generic);
      assert (SmtLib.translation_logic affected = "ALL" andalso
              List.hd affected_strings = "(set-logic ALL)\n",
        expected ^ " was not widened on Z3 4.14.1");
      List.app
        (fn version => assert
          (SmtLib.translation_logic (neighbor version) = expected,
           expected ^ " changed on neighbor Z3 " ^ version))
        ["4.13.0", "4.15.3"]
    end
in
  List.app check representatives
end

fun z3_result_error_precedes_status () =
let
  fun result contents =
    let
      val instream = TextIO.openString contents
      val answer = Z3.is_sat_stream instream
      val () = TextIO.closeIn instream
    in
      answer
    end
  fun expect_sat contents =
    case result contents of
      SolverSpec.SAT NONE => ()
    | _ => die "FAIL: Z3 result parser did not return SAT"
  fun expect_unsat contents =
    case result contents of
      SolverSpec.UNSAT NONE => ()
    | _ => die "FAIL: Z3 result parser did not return UNSAT"
  fun expect_unknown_error contents =
    case result contents of
      SolverSpec.UNKNOWN (SOME message) =>
        assert (contains "unknown sort 'Array'" message,
          "Z3 error diagnostic lost the solver message")
    | SolverSpec.SAT _ =>
        die "FAIL: Z3 error followed by sat was accepted as SAT"
    | _ => die "FAIL: Z3 error did not return diagnostic UNKNOWN"
in
  expect_sat "sat\n";
  expect_unsat "unsat\n";
  expect_unsat "unsupported logic; continuing with ALL\nunsat\n";
  expect_unknown_error "  (error \"unknown sort 'Array'\")\nsat\n";
  (case result "" of
     SolverSpec.UNKNOWN NONE => ()
   | _ => die "FAIL: end-of-stream did not return UNKNOWN")
end

fun smtlib_datatype_type_translation_success () =
let
  fun smtlib_text goal =
    let val (_, strings) = SmtLib.goal_to_SmtLib_translation NONE goal
    in String.concat strings end
  fun assert_has label needle text =
    assert (contains needle text,
      label ^ " did not contain '" ^ needle ^ "':\n" ^ text)
  fun assert_lacks label needle text =
    assert (not (contains needle text),
      label ^ " unexpectedly contained '" ^ needle ^ "':\n" ^ text)
  val enum_text = smtlib_text ([], ``(x:ordering) = y``)
  val list_text = smtlib_text ([], ``(xs:int list) = ys``)
  val two_list_text = smtlib_text ([],
    ``((xs:int list) = ys) /\ ((bs:bool list) = cs)``)
  val record_text = smtlib_text ([], ``(r:smt_rec) = s``)
  val mutual_text = smtlib_text ([], ``(l:smt_left) = m``)
  val nonfree_text = smtlib_text ([],
    ``(n:int smt_nonfree) = m``)
  val builtin_text = smtlib_text ([], ``(s:string) = t``)
  val (records_translation, _) =
    SmtLib.goal_to_SmtLib_translation NONE ([], ``(xs:int list) = ys``)
  val records = SmtLib.translation_records records_translation
  val has_datatype_record =
    List.exists
      (fn SmtLib.DatatypeDeclaration {hol_types, smt_names, declaration} =>
            List.exists (fn ty => Type.compare (ty, ``:int list``) = EQUAL)
              hol_types andalso
            List.exists (fn name => name = "List_Int") smt_names andalso
            contains "(declare-datatypes" declaration
        | _ => false) records
in
  assert_has "enum datatype logic" "(set-logic QF_DT)\n" enum_text;
  assert_has "enum datatype" "(declare-datatypes ((Ordering 0))"
    enum_text;
  assert_has "recursive list datatype" "(declare-datatypes ((List_Int 0))"
    list_text;
  assert_has "recursive list self field" "List_Int" list_text;
  assert_has "first monomorphic list instance" "(List_Int 0)"
    two_list_text;
  assert_has "second monomorphic list instance" "(List_Bool 0)"
    two_list_text;
  assert_has "record datatype" "(declare-datatypes ((Smt_rec 0))"
    record_text;
  assert_has "record int selector"
    "(recordtype_smt_rec_seldef_smt_count Int)" record_text;
  assert_has "record bool selector"
    "(recordtype_smt_rec_seldef_smt_flag Bool)" record_text;
  assert_has "mutual datatype left sort" "(Smt_left 0)" mutual_text;
  assert_has "mutual datatype right sort" "(Smt_right 0)" mutual_text;
  assert_has "mutual datatype block" "(declare-datatypes" mutual_text;
  assert_has "non-free fallback sort" "(declare-sort t0 0)" nonfree_text;
  assert_lacks "non-free fallback" "(declare-datatypes" nonfree_text;
  assert_has "builtin string precedence" "(declare-fun v0 () String)"
    builtin_text;
  assert_lacks "builtin string precedence" "(declare-datatypes"
    builtin_text;
  assert (has_datatype_record,
    "translation records did not include datatype declaration record")
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
  val has_datatype_matrix_row =
    List.exists
      (fn SmtLib.HOLTheoryEncoding {
            smt_theory = "Datatypes", parse = true, typecheck = true,
            translate = true, replay = true, notes, ...} =>
            contains "native SMT-LIB Datatypes" notes
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
  assert (has_datatype_matrix_row,
    "translation records lacked native Datatypes encoding row");
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
    ("list-constructor-native-dt", ([],
       ``CONS (x:int) xs = CONS y ys``),
      ["(set-logic QF_UFDTLIA)\n", "(declare-datatypes ((List_Int 0))",
       "(ctor_List_Int_CONS v1 v2)"]),
    ("function-application-arrays", ([],
       ``(f:'a -> 'b) x = g y``),
      ["(set-logic QF_AX)\n", "(declare-fun v0 () (Array t0 t1))",
       "(declare-fun v2 () (Array t2 t1))",
       "(= (select v0 v1) (select v2 v3))"]),
    ("tuple-selector-native-dt", ([],
       ``FST (p:int # bool) <= FST p + 1``),
      ["(set-logic QF_UFDTLIA)\n",
       "(declare-datatypes ((Prod_Int_Bool 0))",
       "(declare-fun v0 (Prod_Int_Bool) Int)"]),
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
    ("datatype-constructor-native-dt", ([],
       ``SOME (x:int) = SOME y``),
      ["(set-logic QF_UFDTLIA)\n", "(declare-datatypes ((Option_Int 0))",
       "(ctor_Option_Int_SOME v1)"])
  ]
in
  List.app expect cases
end

fun smtlib_datatype_term_translation_success () =
let
  fun smtlib_text goal =
    let val (_, strings) = SmtLib.goal_to_SmtLib_translation NONE goal
    in String.concat strings end
  fun assert_has name text snippet =
    assert (contains snippet text,
      "datatype translation case '" ^ name ^
      "' missed SMT-LIB snippet '" ^ snippet ^ "'\nSMT-LIB:\n" ^ text)
  fun assert_lacks name text snippet =
    assert (not (contains snippet text),
      "datatype translation case '" ^ name ^
      "' unexpectedly emitted snippet '" ^ snippet ^ "'\nSMT-LIB:\n" ^ text)
  val ctor_text = smtlib_text ([], ``SmtTriB (x:int) = SmtTriB y``)
  val partial_text = smtlib_text ([],
    ``(SmtTriB = (f:int -> smt_tri))``)
  val case_text = smtlib_text ([],
    ``(case (z:smt_tri) of
         SmtTriA => 0i
       | SmtTriB x => x
       | SmtTriC p => if p then 1i else 2i) = 0i``)
  val selector_tm = TypeBase.mk_case
    (``z:smt_tri``,
     [(``SmtTriA``, boolSyntax.mk_arb intSyntax.int_ty),
      (``SmtTriB (x:int)``, ``x:int``),
      (``SmtTriC (p:bool)``, boolSyntax.mk_arb intSyntax.int_ty)])
  val selector_text = smtlib_text ([], boolSyntax.mk_eq (selector_tm, ``0i``))
  val record_access_text = smtlib_text ([],
    ``(r:smt_rec).smt_count = 0i``)
  val record_update_text = smtlib_text ([],
    ``(r with smt_count := 3i).smt_count = 3i``)
in
  assert_has "constructor application" ctor_text
    "(ctor_Smt_tri_SmtTriB v1)";
  assert_lacks "constructor application" ctor_text
    "(declare-fun v0 (Int) Smt_tri)";
  assert_has "partial constructor fallthrough" partial_text
    "(declare-fun v0 () (Array Int Smt_tri))";
  assert_has "case expression" case_text
    "(ite ((_ is ctor_Smt_tri_SmtTriA) v0) 0";
  assert_has "case expression" case_text
    "(sel_Smt_tri_ctor_Smt_tri_SmtTriB_0 v0)";
  assert_has "case expression" case_text
    "(ite (sel_Smt_tri_ctor_Smt_tri_SmtTriC_0 v0) 1 2)";
  assert_has "selector-shaped case" selector_text
    "(sel_Smt_tri_ctor_Smt_tri_SmtTriB_0 v0)";
  assert_lacks "selector-shaped case" selector_text
    "(_ is ctor_Smt_tri_SmtTriB)";
  assert_has "record access" record_access_text
    "(recordtype_smt_rec_seldef_smt_count v1)";
  assert_has "record update" record_update_text
    "(ctor_Smt_rec_recordtype_smt_rec 3";
  assert_has "record update" record_update_text
    "(recordtype_smt_rec_seldef_smt_flag v1)"
end

fun smtlib_datatype_parser_dict_success () =
let
  val (translation, _) =
    SmtLib.goal_to_SmtLib_translation NONE
      ([], ``SmtTriB (x:int) = SmtTriB y``)
  val dicts = SmtLib.parser_dicts_for_translation translation
  val ctor = parse_roundtrip_term "datatype constructor parser"
    "(ctor_Smt_tri_SmtTriB 7)" dicts
  val tester = parse_roundtrip_term "datatype tester parser"
    "((_ is ctor_Smt_tri_SmtTriB) (ctor_Smt_tri_SmtTriB 7))" dicts
  val expected_ctor = ``SmtTriB 7i``
  val expected_tester = TypeBase.mk_case
    (expected_ctor,
     [(``SmtTriA``, boolSyntax.F),
      (``SmtTriB (x:int)``, boolSyntax.T),
      (``SmtTriC (p:bool)``, boolSyntax.F)])
in
  assert (Term.aconv ctor expected_ctor,
    "datatype constructor parser resolved to " ^ term_with_types ctor ^
    ", expected " ^ term_with_types expected_ctor);
  assert (tester ~~ expected_tester,
    "datatype tester parser resolved to " ^ term_with_types tester ^
    ", expected " ^ term_with_types expected_tester)
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
    {encoding = "floating point, regex, sequences, sets, bags",
     status = "parse/typecheck matrix entries only unless a HOLTheoryEncoding \
              \record explicitly marks translate=true; replay remains false"}
  ]
  fun has_array_gap {encoding, status} =
    encoding = "SMT ArraysEx select/store" andalso
    String.isSubstring "round-trips" status andalso
    String.isSubstring "select/store" status
  fun has_advanced_gap {encoding, status} =
    encoding = "floating point, regex, sequences, sets, bags" andalso
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

fun parse_z3_proof_string_with_dicts dicts version contents =
let
  val instream = TextIO.openString contents
in
  Z3_ProofParser.parse_stream_with_version dicts version instream
end

fun parse_cpc_proof_string contents =
let
  val dicts = SmtLib_Logics.parsedicts_of_logic "ALL"
  val instream = TextIO.openString contents
in
  CPC_ProofParser.parse_stream_with_version dicts "1.3.4" instream
end

fun cpc_proof_parser_define_and_optional_conclusion_success () =
let
  val proof = parse_cpc_proof_string
    "((define @t1 () false) (assume @p1 @t1) \
    \(step @p2 false :rule refl :args (false)))"
  val commands = CPC_Proof.proof_commands proof
in
  case commands of
    [CPC_Proof.ASSUME ("@p1", tm), CPC_Proof.STEP
      {id = "@p2", conclusion = SOME conclusion, rule, premises = [],
       args = [arg]}] =>
       (assert (tm ~~ ``F``, "CPC define reference did not resolve");
        assert (conclusion ~~ ``F``, "CPC explicit conclusion did not parse");
        assert (arg ~~ ``F``, "CPC :args term did not parse");
        assert (#name rule = "refl", "CPC rule registry did not bind refl"))
  | _ => die "FAIL: CPC parser did not preserve define/assume/step commands"
end

fun cpc_proof_parser_declarations_success () =
let
  val proof = parse_cpc_proof_string
    "((declare-const c Bool) (declare-fun f (Int) Int) \
    \(assume @p1 (and c (= (f 0) (f 0)))))"
  val commands = CPC_Proof.proof_commands proof
in
  case commands of
    [CPC_Proof.ASSUME ("@p1", tm)] =>
      assert (Term.type_of tm = Type.bool,
        "CPC declaration parser did not make declared symbols available")
  | _ => die "FAIL: CPC declaration parser did not preserve the assumption"
end

fun cpc_proof_parser_singleton_premise_success () =
let
  val proof = parse_cpc_proof_string
    "((assume @p1 false) (step @p2 :rule true_elim :premises @p1))"
  val commands = CPC_Proof.proof_commands proof
in
  case commands of
    [CPC_Proof.ASSUME _, CPC_Proof.STEP {premises = ["@p1"], ...}] => ()
  | _ => die "FAIL: CPC parser did not accept a singleton bare :premises id"
end

fun cpc_proof_parser_version_gate_diagnostic () =
let
  val gated_rule = "refl"
  val gated_version = "1.4.0"
  val dicts = SmtLib_Logics.parsedicts_of_logic "ALL"
  val instream = TextIO.openString
    "((step @p1 :rule refl :args (false)))"
in
  assert (not (Option.isSome
      (CPC_Proof.lookup_rule gated_version gated_rule)),
    "version-gated CPC proof rule unexpectedly resolved");
  (ignore (CPC_ProofParser.parse_stream_with_version dicts gated_version
      instream);
   die "FAIL: version-gated CPC proof rule parsed successfully")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr in
      assert (String.isSubstring
          ("rule " ^ gated_rule ^ " is not supported by cvc5 version " ^
           gated_version) msg,
        "CPC version-gate diagnostic did not report the precise rule/version: " ^
        msg)
    end
end

fun cpc_proof_replay_contra_success () =
let
  val proof = parse_cpc_proof_string
    "((assume @p1 true) (assume @p2 (not true)) \
    \(step @p3 false :rule contra :premises (@p1 @p2)))"
  val thm = CPC_ProofReplay.replay_root_for_test proof
in
  assert (Thm.concl thm ~~ ``F``,
    "CPC contra did not replay to false")
end

fun cpc_proof_replay_eq_refl_cong_chain_success () =
let
  val proof = parse_cpc_proof_string
    "((define @t1 () (not (= true true))) (assume @p1 @t1) \
    \(step @p2 :rule evaluate :args ((not true))) \
    \(step @p3 :rule eq-refl :args (true)) \
    \(step @p4 :rule cong :premises (@p3) :args (@t1)) \
    \(step @p5 :rule trans :premises (@p4 @p2)) \
    \(step @p6 false :rule eq_resolve :premises (@p1 @p5)))"
  val thm = CPC_ProofReplay.replay_root_for_test proof
in
  assert (Thm.concl thm ~~ ``F``,
    "CPC eq-refl/cong/trans/eq_resolve chain did not replay to false")
end

fun cpc_proof_replay_and_elim_success () =
let
  val proof = parse_cpc_proof_string
    "((assume @p1 (and true false true)) \
    \(step @p2 :rule and_elim :premises (@p1) :args (1)))"
  val thm = CPC_ProofReplay.replay_root_for_test proof
in
  assert (Thm.concl thm ~~ ``F``,
    "CPC and_elim did not select the requested conjunct")
end

fun cpc_proof_replay_boolean_rewrites_success () =
let
  val proof = parse_cpc_proof_string
    "((step @p1 :rule bool-double-not-elim :args (true)) \
    \(step @p2 :rule bool-impl-false1 :args (true)) \
    \(step @p3 :rule bool-eq-nrefl :args (true)) \
    \(step @p4 :rule eq-symm :args (true false)) \
    \(step @p5 :rule bool-not-eq-elim2 :args (true false)))"
  val commands = CPC_Proof.proof_commands proof
  val thm = CPC_ProofReplay.replay_root_for_test proof
in
  assert (List.length commands = 5,
    "CPC boolean rewrite proof did not parse all rewrite steps");
  assert (Thm.concl thm ~~ ``~(T = F) = (T = ~F)``,
    "CPC boolean rewrite replay returned an unexpected final equality")
end

fun cpc_proof_replay_bool_impl_true2_success () =
let
  val proof = parse_cpc_proof_string
    "((step @p1 :rule bool-impl-true2 :args (false)))"
  val thm = CPC_ProofReplay.replay_root_for_test proof
in
  assert (Thm.concl thm ~~ ``(T ==> F) = F``,
    "CPC bool-impl-true2 did not rewrite true implication")
end

fun cpc_proof_replay_integer_tightening_success () =
let
  val proof = parse_cpc_proof_string
    "((step @p1 :rule arith-geq-tighten :args (0 1)))"
  val thm = CPC_ProofReplay.replay_root_for_test proof
in
  assert (Thm.concl thm ~~ ``~(0i >= 1i) = (1i >= 0i + 1i)``,
    "CPC arith-geq-tighten replay returned an unexpected equality")
end

fun cpc_proof_replay_ite_elim2_success () =
let
  val proof = parse_cpc_proof_string
    "((assume @p1 (ite true false true)) \
    \(step @p2 :rule ite_elim2 :premises (@p1)))"
  val thm = CPC_ProofReplay.replay_root_for_test proof
in
  assert (Thm.concl thm ~~ ``T \/ T``,
    "CPC ite_elim2 did not produce the condition-or-else clause")
end

fun cpc_proof_replay_factoring_success () =
let
  val proof = parse_cpc_proof_string
    "((assume @p1 (or true true)) \
    \(step @p2 :rule factoring :premises (@p1)))"
  val thm = CPC_ProofReplay.replay_root_for_test proof
in
  assert (Thm.concl thm ~~ ``T``,
    "CPC factoring did not eliminate the duplicate literal")
end

fun cpc_proof_parser_unknown_rule_diagnostic () =
  (ignore (parse_cpc_proof_string
    "((step @p1 false :rule made-up-cpc-rule))");
   die "FAIL: unknown CPC proof rule parsed successfully")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring "registry lookup failed" msg,
        "CPC unknown-rule diagnostic omitted registry failure: " ^ msg);
      assert (String.isSubstring "made-up-cpc-rule" msg,
        "CPC unknown-rule diagnostic omitted the rule name: " ^ msg);
      assert (String.isSubstring "1.3.4" msg,
        "CPC unknown-rule diagnostic omitted the cvc5 version: " ^ msg)
    end

fun cpc_live_checked_replay_success () =
  case CVC.CVC_SMT_CPC_Prover ([], ``T``) of
    SolverSpec.UNSAT (SOME thm) =>
      (assert (Thm.concl thm ~~ ``T``,
        "live CPC replay returned an unexpected theorem");
       Library.check_oracle_tags "CPC live replay unit test" thm)
  | SolverSpec.UNSAT NONE => die "FAIL: live CPC replay returned no theorem"
  | SolverSpec.SAT _ => die "FAIL: cvc5 reported sat for the negation of true"
  | SolverSpec.UNKNOWN _ => die "FAIL: cvc5 returned unknown for true"

fun cpc_live_checked_replay_equality_success () =
  case CVC.CVC_SMT_CPC_Prover ([], ``(cpc_x : int) = cpc_x``) of
    SolverSpec.UNSAT (SOME thm) =>
      (assert (Thm.concl thm ~~ ``(cpc_x : int) = cpc_x``,
        "live CPC equality replay returned an unexpected theorem");
       Library.check_oracle_tags "CPC live equality replay unit test" thm)
  | SolverSpec.UNSAT NONE => die "FAIL: live CPC equality replay returned no theorem"
  | SolverSpec.SAT _ => die "FAIL: cvc5 reported sat for a reflexive equality"
  | SolverSpec.UNKNOWN _ => die "FAIL: cvc5 returned unknown for a reflexive equality"

fun cpc_live_checked_replay_datatype_success () =
  case CVC.CVC_SMT_CPC_Prover ([], ``foo <> bar``) of
    SolverSpec.UNSAT (SOME thm) =>
      (assert (Thm.concl thm ~~ ``foo <> bar``,
        "live CPC datatype replay returned an unexpected theorem");
       Library.check_oracle_tags "CPC live datatype replay unit test" thm)
  | SolverSpec.UNSAT NONE => die "FAIL: live CPC datatype replay returned no theorem"
  | SolverSpec.SAT _ => die "FAIL: cvc5 reported sat for distinct constructors"
  | SolverSpec.UNKNOWN _ => die "FAIL: cvc5 returned unknown for datatype test"

fun cpc_live_checked_replay_selector_success () =
  case CVC.CVC_SMT_CPC_Prover
    ([], ``((x : person) with age := 7).age = 7``) of
    SolverSpec.UNSAT (SOME thm) =>
      (assert (Thm.concl thm ~~ ``((x : person) with age := 7).age = 7``,
        "live CPC selector replay returned an unexpected theorem");
       Library.check_oracle_tags "CPC live selector replay unit test" thm)
  | SolverSpec.UNSAT NONE => die "FAIL: live CPC selector replay returned no theorem"
  | SolverSpec.SAT _ => die "FAIL: cvc5 reported sat for selector theorem"
  | SolverSpec.UNKNOWN _ => die "FAIL: cvc5 returned unknown for selector test"

fun cpc_live_checked_replay_bv_xor_success () =
  case CVC.CVC_SMT_CPC_Prover ([], ``(x : word32) ?? x = 0w``) of
    SolverSpec.UNSAT (SOME thm) =>
      (assert (Thm.concl thm ~~ ``(x : word32) ?? x = 0w``,
        "live CPC bit-vector xor replay returned an unexpected theorem");
       Library.check_oracle_tags "CPC live bit-vector replay unit test" thm)
  | SolverSpec.UNSAT NONE => die "FAIL: live CPC replay returned no theorem"
  | SolverSpec.SAT _ => die "FAIL: cvc5 reported sat for bit-vector xor theorem"
  | SolverSpec.UNKNOWN _ => die "FAIL: cvc5 returned unknown for bit-vector xor test"

fun cpc_live_checked_replay_bv_bitblast_success () =
  case CVC.CVC_SMT_CPC_Prover
    ([], ``((x : word32) || y) || z = x || y || z``) of
    SolverSpec.UNSAT (SOME thm) =>
      (assert (Thm.concl thm ~~ ``((x : word32) || y) || z = x || y || z``,
        "live CPC bit-blast replay returned an unexpected theorem");
       Library.check_oracle_tags "CPC live bit-blast replay unit test" thm)
  | SolverSpec.UNSAT NONE => die "FAIL: live CPC replay returned no theorem"
  | SolverSpec.SAT _ => die "FAIL: cvc5 reported sat for bit-vector OR theorem"
  | SolverSpec.UNKNOWN _ => die "FAIL: cvc5 returned unknown for bit-vector OR test"

fun cpc_live_checked_replay_boolean_resolution_success () =
  case CVC.CVC_SMT_CPC_Prover
    ([], ``((p : bool) ==> q) /\ (q ==> p) ==> (p = q)``) of
    SolverSpec.UNSAT (SOME thm) =>
      (assert (Thm.concl thm ~~ ``((p : bool) ==> q) /\ (q ==> p) ==> (p = q)``,
        "live CPC Boolean resolution replay returned an unexpected theorem");
       Library.check_oracle_tags "CPC live Boolean resolution unit test" thm)
  | SolverSpec.UNSAT NONE => die "FAIL: live CPC Boolean resolution returned no theorem"
  | SolverSpec.SAT _ => die "FAIL: cvc5 reported sat for Boolean equivalence theorem"
  | SolverSpec.UNKNOWN _ => die "FAIL: cvc5 returned unknown for Boolean equivalence theorem"

fun cpc_live_checked_replay_nat_max_success () =
  case CVC.CVC_SMT_CPC_Prover ([], ``MAX (x : num) y >= y``) of
    SolverSpec.UNSAT (SOME thm) =>
      (assert (Thm.concl thm ~~ ``MAX (x : num) y >= y``,
        "live CPC natural MAX replay returned an unexpected theorem");
       Library.check_oracle_tags "CPC live natural MAX unit test" thm)
  | SolverSpec.UNSAT NONE => die "FAIL: live CPC natural MAX replay returned no theorem"
  | SolverSpec.SAT _ => die "FAIL: cvc5 reported sat for natural MAX theorem"
  | SolverSpec.UNKNOWN _ => die "FAIL: cvc5 returned unknown for natural MAX theorem"

fun cpc_live_checked_replay_int_abs_success () =
  case CVC.CVC_SMT_CPC_Prover ([], ``(x : int) >= 0 ==> ABS x = x``) of
    SolverSpec.UNSAT (SOME thm) =>
      (assert (Thm.concl thm ~~ ``(x : int) >= 0 ==> ABS x = x``,
        "live CPC integer ABS replay returned an unexpected theorem");
       Library.check_oracle_tags "CPC live integer ABS unit test" thm)
  | SolverSpec.UNSAT NONE => die "FAIL: live CPC integer ABS replay returned no theorem"
  | SolverSpec.SAT _ => die "FAIL: cvc5 reported sat for integer ABS theorem"
  | SolverSpec.UNKNOWN _ => die "FAIL: cvc5 returned unknown for integer ABS theorem"

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

fun z3_proof_parser_datatype_th_lemma_metadata_success () =
let
  val proof = parse_z3_proof_string "4.13.0"
    "((proof ((_ th-lemma datatype eq-propagate 5) false)))"
in
  case Redblackmap.peek (Z3_Proof.proof_steps proof, 0) of
    SOME (Z3_Proof.TH_LEMMA_DATATYPE
      ({theory, subkind, indices}, [], concl)) =>
        (assert (theory = "datatype",
          "datatype th-lemma metadata did not preserve theory");
         assert (subkind = SOME "eq-propagate",
          "datatype th-lemma metadata did not preserve subkind");
         assert (indices = ["5"],
          "datatype th-lemma metadata did not preserve proof indices: [" ^
          String.concatWith ", " indices ^ "]");
         assert (concl ~~ ``F``,
          "datatype th-lemma metadata test parsed unexpected conclusion"))
  | SOME _ => die "FAIL: datatype th-lemma parsed to unexpected constructor"
  | NONE => die "FAIL: datatype th-lemma proof did not define root proof step"
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

fun z3_proof_parser_version_gate_diagnostic () =
let
  val gated_rule = "apply-def"
  (* A hypothetical non-4.x version used purely to probe that the version gate
     REJECTS out-of-range versions.  It is not a supported version (only Z3 4.x
     is supported); it must merely fail the "4." prefix so `apply-def` does not
     resolve. *)
  val gated_version = "3.0.0"
in
  assert (not (Option.isSome
      (Z3_Proof.lookup_rule gated_version gated_rule)),
    "version-gated proof rule unexpectedly resolved");
  (ignore (parse_z3_proof_string gated_version
    "((proof (apply-def (asserted false) false)))");
   die "FAIL: version-gated Z3 proof rule parsed successfully")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring
          ("rule " ^ gated_rule ^ " not supported by Z3 version " ^
           gated_version) msg,
        "version-gate diagnostic did not report the precise rule/version: " ^
        msg)
    end
end

fun z3_proof_parser_rule_name_term_boundary () =
  (ignore (parse_z3_proof_string "4.12.4"
    "((proof (asserted (rewrite (= false false)))))");
   die "FAIL: rule-name identifier in conclusion parsed without ambiguity")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring "asserted" msg,
        "rule-name term boundary diagnostic did not include the enclosing \
        \proof rule: " ^ msg);
      assert (String.isSubstring "not a numeral" msg orelse
              String.isSubstring "argument" msg,
        "rule-name term boundary diagnostic did not identify proof parsing: " ^
        msg)
    end

fun replay_z3_proof_string contents =
  Z3_ProofReplay.replay_root_for_test
    (parse_z3_proof_string "4.12.4" contents)

fun replay_z3_proof_string_with_dicts dicts contents =
  Z3_ProofReplay.replay_root_for_test
    (parse_z3_proof_string_with_dicts dicts "4.12.4" contents)

fun assert_replays_raw_z3_proof_rule (name, proof_text, expected) =
let
  val thm = replay_z3_proof_string proof_text
  val actual = Thm.concl thm
in
  assert (actual ~~ expected,
    "raw Z3 proof rule " ^ name ^ " replayed to " ^
    term_with_types actual ^ ", expected " ^ term_with_types expected)
end

fun z3_remove_extra_hyps_only_p_eq_p_success () =
let
  val asserted = Term.empty_tmset
  val p_eq_p = ``(p:bool) = p``
  val q_eq_q = ``(q:bool) = q``
  val p_clean = Z3_ProofReplay.remove_extra_hyps
    (asserted, Thm.ASSUME p_eq_p)
  val q_kept = Z3_ProofReplay.remove_extra_hyps
    (asserted, Thm.ASSUME q_eq_q)
in
  assert (HOLset.isEmpty (Thm.hypset p_clean),
    "remove_extra_hyps did not discharge literal p = p");
  assert (HOLset.member (Thm.hypset q_kept, q_eq_q),
    "remove_extra_hyps discharged a non-p reflexive equality")
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
    ("datatype/acyclicity",
      "((declare-fun l () Smt_left) \
        \(proof ((_ th-lemma datatype 0) \
        \(not (= (ctor_Smt_left_SmtLeft \
        \(ctor_Smt_right_SmtRight l)) l)))))"),
    ("datatype/exhaustiveness",
      "((declare-fun c () Smt_tri) \
        \(proof ((_ th-lemma datatype 1) \
        \(implies (not ((_ is ctor_Smt_tri_SmtTriA) c)) \
        \(implies (not ((_ is ctor_Smt_tri_SmtTriB) c)) \
        \(implies (not ((_ is ctor_Smt_tri_SmtTriC) c)) false))))))"),
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
  let
    val (datatype_translation, _) =
      SmtLib.goal_to_SmtLib_translation NONE
        ([], ``((c:smt_tri) = c) /\ ((l:smt_left) = l)``)
    val datatype_dicts =
      SmtLib.parser_dicts_for_translation datatype_translation
    fun replay name =
      if String.isPrefix "datatype/" name then
        replay_z3_proof_string_with_dicts datatype_dicts
      else replay_z3_proof_string
  in
    List.app (fn (name, proof_text) =>
    (let
       val thm = replay name proof_text
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

fun assert_datatype_prover name prover tm =
  (let
     val thm = prover tm
   in
     assert (Thm.concl thm ~~ tm,
       name ^ " proved wrong conclusion: " ^ Library.thm_to_string thm);
     Library.check_oracle_tags name thm
   end
   handle Feedback.HOL_ERR holerr =>
     die ("FAIL: " ^ name ^ " did not prove datatype goal: " ^
       Feedback.message_of holerr))

fun smt_tri_tester ctor scrutinee =
  let
    fun result name = if name = ctor then boolSyntax.T else boolSyntax.F
  in
    TypeBase.mk_case
      (scrutinee,
       [(``SmtTriA``, result "SmtTriA"),
        (``SmtTriB (x:int)``, result "SmtTriB"),
        (``SmtTriC (p:bool)``, result "SmtTriC")])
  end

fun smt_tri_left_selector scrutinee =
  TypeBase.mk_case
    (scrutinee,
     [(``SmtTriA``, boolSyntax.mk_arb intSyntax.int_ty),
      (``SmtTriB (x:int)``, ``x:int``),
      (``SmtTriC (p:bool)``, boolSyntax.mk_arb intSyntax.int_ty)])

fun datatype_prove_ladder_rungs_success () =
  let
    val c = ``c:smt_tri``
    fun mk_imp_chain ants concl =
      List.foldr (fn (ant, acc) => boolSyntax.mk_imp (ant, acc)) concl ants
    val exhaustiveness_goal =
      mk_imp_chain
        (List.map boolSyntax.mk_neg
          [smt_tri_tester "SmtTriA" c,
           smt_tri_tester "SmtTriB" c,
           smt_tri_tester "SmtTriC" c])
        boolSyntax.F
  in
    assert (List.null Z3_ProformaThms.datatype_thm_list,
      "datatype proforma list should stay empty until shared schemata exist");
    assert_datatype_prover "datatype_prove harvest disjointness rung"
      SmtDatatypeProve.datatype_prove
      ``SmtTriA <> SmtTriB 1i``;
    assert_datatype_prover "datatype_prove harvest injectivity rung"
      SmtDatatypeProve.datatype_simp_prove
      ``SmtTriB (x:int) = SmtTriB y ==> x = y``;
    assert_datatype_prover "datatype_prove harvest selector rung"
      SmtDatatypeProve.datatype_simp_prove
      (boolSyntax.mk_eq (smt_tri_left_selector ``SmtTriB 7i``, ``7i``));
    assert_datatype_prover "datatype_prove exhaustiveness rung"
      SmtDatatypeProve.exhaustiveness_prove
      exhaustiveness_goal;
    assert_datatype_prover "datatype_prove acyclicity rung"
      SmtDatatypeProve.acyclicity_prove
      ``SmtLeft (SmtRight (l:smt_left)) <> l``;
    assert_datatype_prover "datatype_prove explicit metis rung"
      SmtDatatypeProve.metis_datatype_prove
      ``SmtTriB (x:int) = SmtTriB y /\ SmtTriA <> SmtTriB y ==> x = y``
  end

fun datatype_prove_unsupported_diagnostic () =
  (ignore (SmtDatatypeProve.datatype_prove ``F``);
   die "FAIL: unsupported datatype th-lemma replayed successfully")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring "unsupported th-lemma shape" msg,
        "datatype th-lemma diagnostic did not report unsupported shape: " ^
        msg);
      assert (String.isSubstring "theory=datatype" msg,
        "datatype th-lemma diagnostic did not include theory: " ^ msg);
      assert (String.isSubstring "conclusion=F" msg,
        "datatype th-lemma diagnostic did not include conclusion: " ^ msg)
    end

fun z3_rewrite_datatype_rung_replay_success () =
let
  val acyclic_eq =
    boolSyntax.mk_eq (``l:smt_left``, ``SmtLeft (SmtRight (l:smt_left))``)
  val (translation, _) =
    SmtLib.goal_to_SmtLib_translation NONE
      ([], acyclic_eq)
  val dicts = SmtLib.parser_dicts_for_translation translation
  val proof_text =
    "((declare-fun l () Smt_left) \
    \(proof (rewrite (= (= l (ctor_Smt_left_SmtLeft \
    \(ctor_Smt_right_SmtRight l))) false))))"
  val () = Profile.reset_all ()
  val thm = replay_z3_proof_string_with_dicts dicts proof_text
in
  assert (Thm.concl thm ~~ boolSyntax.mk_eq (acyclic_eq, boolSyntax.F),
    "datatype rewrite replayed to unexpected conclusion: " ^
    Library.thm_to_string thm);
  assert (profile_call_count "rewrite(11.1)(datatype)" > 0,
    "datatype rewrite did not use the rewrite datatype rung");
  Library.check_oracle_tags "datatype rewrite replay" thm
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
      "proof-rule:th-lemma-regexp")
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
  ignore (Z3.check_reconstructed_theorem "unit-test"
    (([boolSyntax.T], boolSyntax.T), Thm.ASSUME boolSyntax.T));
  expect_failure "extra hypothesis with allowed assumptions"
    "unexpected hypotheses: [T]"
    (fn () =>
      Z3.check_reconstructed_theorem "unit-test"
        (([boolSyntax.F], boolSyntax.T), Thm.ASSUME boolSyntax.T));
  expect_failure "allowed assumption details" "allowed hypotheses: [F]"
    (fn () =>
      Z3.check_reconstructed_theorem "unit-test"
        (([boolSyntax.F], boolSyntax.T), Thm.ASSUME boolSyntax.T));
  expect_failure "conclusion mismatch" "parsed assertion-negation goal" (fn () =>
    Z3.check_reconstructed_theorem "unit-test"
      (([], boolSyntax.F), boolTheory.TRUTH))
end

fun with_low_solver_timeout f =
let
  val old_timeout = !SolverSpec.timeout_milliseconds
  fun restore () = SolverSpec.timeout_milliseconds := old_timeout
  fun work () =
    (SolverSpec.timeout_milliseconds := 2000;
     f ())
in
  Portable.finally restore work ()
end

fun z3_direct_if_configured f =
  if Z3.is_configured () then
    with_low_solver_timeout f
  else
    ()

fun conjunction [] = boolSyntax.T
  | conjunction (tm :: tms) =
      List.foldl (fn (next, acc) => boolSyntax.mk_conj (acc, next)) tm tms

fun z3_direct_bitvector_contradiction_success () =
  z3_direct_if_configured (fn () =>
  let
    val state =
      parse_smtlib_state
        ("(set-option :produce-proofs true)\n" ^
         "(set-logic QF_BV)\n" ^
         "(declare-const a (_ BitVec 8))\n" ^
         "(assert (and (= a a) (not (= a a))))\n" ^
         "(check-sat)\n" ^
         "(get-proof)\n")
    val goal = boolSyntax.mk_neg (conjunction (#assertions state))
    val thm =
      case Z3.Z3_SMT_Prover ([], goal) of
        SolverSpec.UNSAT (SOME thm) => thm
      | _ =>
          die "FAIL: external bitvector contradiction did not replay a theorem"
  in
    assert (List.null (Thm.hyp thm),
      "direct bitvector contradiction theorem has unexpected hypotheses");
    assert (Term.aconv (Thm.concl thm) goal,
      "direct bitvector contradiction theorem conclusion does not match goal");
    Library.check_oracle_tags "unit-test" thm
  end)

fun z3_direct_bitvector_overflow_tautology_sat_success () =
  z3_direct_if_configured (fn () =>
  let
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
      SolverSpec.SAT _ => ()
    | SolverSpec.UNSAT _ =>
        die "FAIL: external bitvector tautology was wrongly reported UNSAT"
    | SolverSpec.UNKNOWN _ =>
        die "FAIL: external bitvector tautology was not reported SAT"
  end)

fun z3_direct_distinct_contradiction_success () =
  z3_direct_if_configured (fn () =>
  let
    val state =
      parse_smtlib_state
        ("(set-option :produce-proofs true)\n" ^
         "(set-logic QF_LIA)\n" ^
         "(assert (not (= 1 1)))\n" ^
         "(check-sat)\n" ^
         "(get-proof)\n")
    val goal = boolSyntax.mk_neg (conjunction (#assertions state))
    val thm =
      case Z3.Z3_SMT_Prover ([], goal) of
        SolverSpec.UNSAT (SOME thm) => thm
      | _ => die "FAIL: external integer contradiction did not replay a theorem"
  in
    assert (List.null (Thm.hyp thm),
      "direct integer contradiction theorem has unexpected hypotheses");
    assert (Term.aconv (Thm.concl thm) goal,
      "direct integer contradiction theorem conclusion does not match goal");
    Library.check_oracle_tags "unit-test" thm
  end)

(* Each script below is a trivially true ground or satisfiable arithmetic
   fact.  The proved transfer pass and timeout should let external Z3 report
   `sat' promptly; when Z3 is not configured this external-verdict check is
   skipped like the other solver-gated tests. *)
fun z3_direct_ground_arithmetic_sat_success () =
  z3_direct_if_configured (fn () =>
  let
    fun expect_sat label text =
      let
        val state = parse_smtlib_state text
        val goal = boolSyntax.mk_neg (conjunction (#assertions state))
      in
        case Z3.Z3_SMT_Prover ([], goal) of
          SolverSpec.SAT _ => ()
        | SolverSpec.UNSAT _ =>
            die ("FAIL: " ^ label ^ " was wrongly reported UNSAT")
        | SolverSpec.UNKNOWN _ =>
            die ("FAIL: " ^ label ^ " was not reported SAT")
      end
  in
    (* integer ABS -- the `|7| = 7'-shaped example over int *)
    expect_sat "int abs"
      ("(set-logic QF_LIA)\n(assert (= (abs (- 7)) 7))\n(check-sat)\n");
    (* Euclidean division/modulo previously exercised the divergent
       num-bridge path; they must now get a prompt external SAT verdict. *)
    expect_sat "int ediv"
      ("(set-logic QF_LIA)\n(assert (= (div 7 3) 2))\n(check-sat)\n");
    expect_sat "int emod"
      ("(set-logic QF_LIA)\n(assert (= (mod 7 3) 1))\n(check-sat)\n");
    (* real division goes through Z3's total `smt_rdiv' constant *)
    expect_sat "real division"
      ("(set-logic QF_LRA)\n(assert (= (/ 3.0 2.0) 1.5))\n(check-sat)\n");
    (* linear real arithmetic through external Z3 *)
    expect_sat "real plus"
      ("(set-logic QF_LRA)\n(assert (= (+ 1.0 2.0 3.0) 6.0))\n(check-sat)\n");
    (* mixed int/real embedding *)
    expect_sat "intreal to_int"
      ("(set-logic QF_NIRA)\n(assert (= (to_int 2.0) 2))\n(check-sat)\n");
    (* satisfiable equations over unknowns *)
    expect_sat "int existential"
      ("(set-logic QF_LIA)\n(declare-const x Int)\n" ^
       "(assert (= x 0))\n(check-sat)\n");
    expect_sat "real existential"
      ("(set-logic QF_LRA)\n(declare-const x Real)\n" ^
       "(assert (= x 0.0))\n(check-sat)\n");
    (* propositional tautology through external Z3 *)
    expect_sat "propositional tautology"
      ("(set-logic QF_UF)\n(declare-const p Bool)\n" ^
       "(assert (or p (not p)))\n(check-sat)\n")
  end)

fun z3_direct_ground_arithmetic_unsat_success () =
  z3_direct_if_configured (fn () =>
  let
    fun expect_unsat label text =
      let
        val state = parse_smtlib_state text
        val goal = boolSyntax.mk_neg (conjunction (#assertions state))
        val thm =
          case Z3.Z3_SMT_Prover ([], goal) of
            SolverSpec.UNSAT (SOME thm) => thm
          | SolverSpec.UNSAT NONE =>
              die ("FAIL: " ^ label ^ " returned UNSAT without a theorem")
          | SolverSpec.SAT _ =>
              die ("FAIL: " ^ label ^ " was wrongly reported SAT")
          | SolverSpec.UNKNOWN _ =>
              die ("FAIL: " ^ label ^ " was not reported UNSAT")
      in
        assert (List.null (Thm.hyp thm),
          label ^ " theorem has unexpected hypotheses");
        assert (Term.aconv (Thm.concl thm) goal,
          label ^ " theorem conclusion does not match goal");
        Library.check_oracle_tags "unit-test" thm
      end
  in
    expect_unsat "int divisible"
      ("(set-option :produce-proofs true)\n(set-logic QF_LIA)\n" ^
       "(assert ((_ divisible 3) 7))\n(check-sat)\n(get-proof)\n");
    expect_unsat "int pow"
      ("(set-option :produce-proofs true)\n(set-logic QF_NIA)\n" ^
       "(assert (= (** 2 3) 9))\n(check-sat)\n(get-proof)\n")
  end)

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
    ("num_binder_transfer_lemmas_success",
      num_binder_transfer_lemmas_success),
    ("num_binder_relativization_forall_success",
      num_binder_relativization_forall_success),
    ("num_binder_relativization_exists_success",
      num_binder_relativization_exists_success),
    ("num_binder_relativization_nested_mixed_success",
      num_binder_relativization_nested_mixed_success),
    ("num_binder_relativization_non_num_noop_success",
      num_binder_relativization_non_num_noop_success),
    ("num_transfer_literal_normalization_success",
      num_transfer_literal_normalization_success),
    ("num_transfer_operator_drive_success",
      num_transfer_operator_drive_success),
    ("num_transfer_unguarded_num_corner_success",
      num_transfer_unguarded_num_corner_success),
    ("num_transfer_guarded_num_success",
      num_transfer_guarded_num_success),
    ("num_transfer_assumption_free_var_success",
      num_transfer_assumption_free_var_success),
    ("num_bridge_axioms_retired_success",
      num_bridge_axioms_retired_success),
    ("ceiling_builtin_encoding_success", ceiling_builtin_encoding_success),
    ("literal_power_unfolding_success", literal_power_unfolding_success),
    ("symbolic_positive_power_transfer_success",
      symbolic_positive_power_transfer_success),
    ("num_floor_ceiling_total_transfer_success",
      num_floor_ceiling_total_transfer_success),
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
    ("parse_file_datatype_elaboration_options_success",
      parse_file_datatype_elaboration_options_success),
    ("parse_file_datatype_elaboration_flag_off_success",
      parse_file_datatype_elaboration_flag_off_success),
    ("parse_file_datatype_match_elaboration_success",
      parse_file_datatype_match_elaboration_success),
    ("parse_file_datatype_dependency_elaboration_success",
      parse_file_datatype_dependency_elaboration_success),
    ("parse_file_datatype_match_source_order_success",
      parse_file_datatype_match_source_order_success),
    ("parse_file_datatype_match_negatives",
      parse_file_datatype_match_negatives),
    ("parse_file_datatype_match_placeholder_rejection",
      parse_file_datatype_match_placeholder_rejection),
    ("holsmtlib_z3_tac_datatype_flag_leakage_guard",
      holsmtlib_z3_tac_datatype_flag_leakage_guard),
    ("parse_legacy_datatype_mutual_dictionary_success",
      parse_legacy_datatype_mutual_dictionary_success),
    ("smtlib_datatype_elaboration_core_success",
      smtlib_datatype_elaboration_core_success),
    ("smtlib_datatype_elaboration_wellfounded_diagnostic",
      smtlib_datatype_elaboration_wellfounded_diagnostic),
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
    ("parse_legacy_define_fun_rec_hypothesis_only_success",
      parse_legacy_define_fun_rec_hypothesis_only_success),
    ("smtlib_soundness_audit_scope_success",
      smtlib_soundness_audit_scope_success),
    ("smtlib_indexed_parametric_sort_reconstruction_success",
      smtlib_indexed_parametric_sort_reconstruction_success),
    ("smtlib_typecheck_invalid_assertion_diagnostic",
      smtlib_typecheck_invalid_assertion_diagnostic),
    ("smtlib_typecheck_declared_function_mismatch_diagnostic",
      smtlib_typecheck_declared_function_mismatch_diagnostic),
    ("smtlib_int_real_operator_coercion_success",
      smtlib_int_real_operator_coercion_success),
    ("smtlib_int_real_user_function_coercion_success",
      smtlib_int_real_user_function_coercion_success),
    ("smtlib_int_only_no_spurious_coercion_success",
      smtlib_int_only_no_spurious_coercion_success),
    ("smtlib_array_type_mismatch_diagnostics",
      smtlib_array_type_mismatch_diagnostics),
    ("smtlib_declare_sort_parametric_success",
      smtlib_declare_sort_parametric_success),
    ("smtlib_declare_sort_parametric_arity_diagnostics",
      smtlib_declare_sort_parametric_arity_diagnostics),
    ("smtlib_command_malformed_diagnostics",
      smtlib_command_malformed_diagnostics),
    ("smtlib_logic_fragment_diagnostics",
      smtlib_logic_fragment_diagnostics),
    ("smtlib_checked_replay_gap_diagnostics",
      smtlib_checked_replay_gap_diagnostics),
    ("smtlib_typecheck_overloaded_and_indexed_success",
      smtlib_typecheck_overloaded_and_indexed_success),
    ("smtlib_and_or_right_assoc_parse_shape_success",
      smtlib_and_or_right_assoc_parse_shape_success),
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
    ("z3_414_logic_policy_success",
      z3_414_logic_policy_success),
    ("z3_414_array_datatype_translation_success",
      z3_414_array_datatype_translation_success),
    ("z3_414_all_inferred_families_translation_success",
      z3_414_all_inferred_families_translation_success),
    ("z3_result_error_precedes_status",
      z3_result_error_precedes_status),
    ("smtlib_datatype_type_translation_success",
      smtlib_datatype_type_translation_success),
    ("smtlib_extended_hol_encoding_records_success",
      smtlib_extended_hol_encoding_records_success),
    ("smtlib_higher_order_translation_abstraction_success",
      smtlib_higher_order_translation_abstraction_success),
    ("smtlib_translation_shape_matrix_success",
      smtlib_translation_shape_matrix_success),
    ("smtlib_term_translation_branch_matrix_success",
      smtlib_term_translation_branch_matrix_success),
    ("smtlib_datatype_term_translation_success",
      smtlib_datatype_term_translation_success),
    ("smtlib_datatype_parser_dict_success",
      smtlib_datatype_parser_dict_success),
    ("smtlib_preprocessing_and_gap_diagnostics",
      smtlib_preprocessing_and_gap_diagnostics),
    ("smtlib_roundtrip_current_theories_success",
      smtlib_roundtrip_current_theories_success),
    ("smtlib_roundtrip_known_gap_matrix_success",
      smtlib_roundtrip_known_gap_matrix_success),
    ("cpc_proof_parser_define_and_optional_conclusion_success",
      cpc_proof_parser_define_and_optional_conclusion_success),
    ("cpc_proof_parser_declarations_success",
      cpc_proof_parser_declarations_success),
    ("cpc_proof_parser_singleton_premise_success",
      cpc_proof_parser_singleton_premise_success),
    ("cpc_proof_parser_version_gate_diagnostic",
      cpc_proof_parser_version_gate_diagnostic),
    ("cpc_proof_replay_contra_success",
      cpc_proof_replay_contra_success),
    ("cpc_proof_replay_eq_refl_cong_chain_success",
      cpc_proof_replay_eq_refl_cong_chain_success),
    ("cpc_proof_replay_and_elim_success",
      cpc_proof_replay_and_elim_success),
    ("cpc_proof_replay_boolean_rewrites_success",
      cpc_proof_replay_boolean_rewrites_success),
    ("cpc_proof_replay_bool_impl_true2_success",
      cpc_proof_replay_bool_impl_true2_success),
    ("cpc_proof_replay_integer_tightening_success",
      cpc_proof_replay_integer_tightening_success),
    ("cpc_proof_replay_ite_elim2_success",
      cpc_proof_replay_ite_elim2_success),
    ("cpc_proof_replay_factoring_success",
      cpc_proof_replay_factoring_success),
    ("cpc_proof_parser_unknown_rule_diagnostic",
      cpc_proof_parser_unknown_rule_diagnostic),
    ("cpc_live_checked_replay_success",
      cpc_live_checked_replay_success),
    ("cpc_live_checked_replay_equality_success",
      cpc_live_checked_replay_equality_success),
    ("cpc_live_checked_replay_datatype_success",
      cpc_live_checked_replay_datatype_success),
    ("cpc_live_checked_replay_selector_success",
      cpc_live_checked_replay_selector_success),
    ("cpc_live_checked_replay_bv_xor_success",
      cpc_live_checked_replay_bv_xor_success),
    ("cpc_live_checked_replay_bv_bitblast_success",
      cpc_live_checked_replay_bv_bitblast_success),
    ("cpc_live_checked_replay_boolean_resolution_success",
      cpc_live_checked_replay_boolean_resolution_success),
    ("cpc_live_checked_replay_nat_max_success",
      cpc_live_checked_replay_nat_max_success),
    ("cpc_live_checked_replay_int_abs_success",
      cpc_live_checked_replay_int_abs_success),
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
    ("z3_proof_parser_datatype_th_lemma_metadata_success",
      z3_proof_parser_datatype_th_lemma_metadata_success),
    ("z3_proof_parser_unknown_rule_diagnostic",
      z3_proof_parser_unknown_rule_diagnostic),
    ("z3_proof_parser_version_gate_diagnostic",
      z3_proof_parser_version_gate_diagnostic),
    ("z3_proof_parser_rule_name_term_boundary",
      z3_proof_parser_rule_name_term_boundary),
    ("z3_remove_extra_hyps_only_p_eq_p_success",
      z3_remove_extra_hyps_only_p_eq_p_success),
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
    ("datatype_prove_ladder_rungs_success",
      datatype_prove_ladder_rungs_success),
    ("datatype_prove_unsupported_diagnostic",
      datatype_prove_unsupported_diagnostic),
    ("z3_rewrite_datatype_rung_replay_success",
      z3_rewrite_datatype_rung_replay_success),
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
    ("z3_direct_bitvector_contradiction_success",
      z3_direct_bitvector_contradiction_success),
    ("z3_direct_bitvector_overflow_tautology_sat_success",
      z3_direct_bitvector_overflow_tautology_sat_success),
    ("z3_direct_distinct_contradiction_success",
      z3_direct_distinct_contradiction_success),
    ("z3_direct_ground_arithmetic_sat_success",
      z3_direct_ground_arithmetic_sat_success),
    ("z3_direct_ground_arithmetic_unsat_success",
      z3_direct_ground_arithmetic_unsat_success),
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
