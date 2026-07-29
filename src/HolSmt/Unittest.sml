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
  `smt_fun_rec = <| smt_fun : int -> bool -> int |>`

val _ = Hol_datatype
  `smt_left = SmtLeftDone | SmtLeft of smt_right;
   smt_right = SmtRightDone | SmtRight of smt_left`

val _ = new_type ("smt_nonfree", 1)
val _ = new_constant ("smt_nonfree_nil", ``:'a smt_nonfree``)
val _ = new_constant
  ("smt_nonfree_cons", ``:'a -> 'a smt_nonfree -> 'a smt_nonfree``)
val _ = new_constant ("smtlib_uf_logic_foo", ``:int -> int``)
val _ = new_constant
  ("smtlib_ho_rank2", ``:int -> bool -> int``)
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

fun num_to_int_under_abstraction_success () =
let
  val input =
    ``(H:(int -> bool) -> bool)
        (\x:int. x <= 0 /\ (n:num) = 1)``
  val expected =
    ``(H:(int -> bool) -> bool)
        (\x:int. x <= 0 /\ (&(n:num):int) = 1)``
  val thm = SmtLib.NUM_TO_INT_CONV input
  val binder_input =
    ``(H:(int -> bool) -> bool) (\x:int. !n:num. x <= &n)``
  val binder_expected =
    ``(H:(int -> bool) -> bool)
        (\x:int. !i:int. 0 <= i ==> x <= &(Num i))``
  val binder_thm = SmtLib.NUM_BINDERS_TO_INT_CONV binder_input
in
  assert_no_hyps ("NUM_TO_INT_CONV under abstraction", thm);
  assert_concl_alpha
    ("NUM_TO_INT_CONV under abstraction", thm,
     boolSyntax.mk_eq (input, expected));
  assert_no_hyps ("num binder conversion under abstraction", binder_thm);
  assert_concl_alpha
    ("num binder conversion under abstraction", binder_thm,
     boolSyntax.mk_eq (binder_input, binder_expected))
end

(* The raw binary_ieee carrier has many NaN payloads.  In particular the
   statement below is false (a sign-one NaN is a counterexample), and must
   not become provable merely because SMT-LIB has one NaN.  The smtfp
   universe check is the positive direction: its representation is
   canonical, injective, and onto exactly the canonical records. *)
fun smtfp_carrier_universe_direction_success () =
let
  val exact_universe_goal =
    ``!x : (2,3) smtfloat$smtfp.
        smtfloat$smtfp_canonical (smtfloat$smtfp_rep x)``
  val exact_universe = Tactical.TAC_PROOF
    (([], exact_universe_goal),
     simp [smtfloatTheory.smtfp_rep_canonical])
  val wider_universe_goal =
    ``!x : (2,3) binary_ieee$float.
        binary_ieee$float_is_nan x ==>
        x = (smtfloat$float_canon_qnan : (2,3) binary_ieee$float)``
  fun oracle_rejects () =
    ((ignore (Tactical.TAC_PROOF
        (([], wider_universe_goal), HolSmtLib.Z3_ORACLE_TAC));
      false)
     handle Feedback.HOL_ERR _ => true)
in
  Library.check_oracle_tags "smtfp exact universe goal" exact_universe;
  assert_concl_alpha
    ("smtfp exact universe goal", exact_universe, exact_universe_goal);
  Library.check_oracle_tags "smtfp representation canonical"
    smtfloatTheory.smtfp_rep_canonical;
  Library.check_oracle_tags "smtfp representation injective"
    smtfloatTheory.smtfp_rep_11;
  Library.check_oracle_tags "smtfp representation surjective"
    smtfloatTheory.smtfp_rep_surjective;
  if Z3.is_configured () then
    assert (oracle_rejects (),
      "Z3 oracle proved a NaN-unique claim over the wider raw carrier")
  else
    ()
end

fun smtfloat_rounding_conversions_success () =
let
  fun check (label, conv, input, expected) =
    (let
       val thm = conv input
     in
       assert_no_hyps (label, thm);
       Library.check_oracle_tags label thm;
       assert_concl_alpha
         (label, thm, boolSyntax.mk_eq (input, expected))
     end
     handle e => die (label ^ " raised " ^ General.exnMessage e))
  val fp3_one =
    ``(<| Sign := 0w; Exponent := 15w; Significand := 0w |> :
       (3,5) binary_ieee$float)``
  val fp3_two =
    ``(<| Sign := 0w; Exponent := 16w; Significand := 0w |> :
       (3,5) binary_ieee$float)``
  val fp3_eighteen =
    ``(<| Sign := 0w; Exponent := 19w; Significand := 1w |> :
       (3,5) binary_ieee$float)``
  val tests =
    [
      ("RTP ordinary (10,5)", smtfloatLib.round_CONV,
       ``(round roundTowardPositive (11r / 10) :
          (10,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 15w; Significand := 103w |> :
          (10,5) binary_ieee$float)``),
      ("RTN ordinary (10,5)", smtfloatLib.round_CONV,
       ``(round roundTowardNegative (11r / 10) :
          (10,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 15w; Significand := 102w |> :
          (10,5) binary_ieee$float)``),
      ("RTP positive underflow to minimum subnormal",
       smtfloatLib.round_CONV,
       ``(round roundTowardPositive (1r / 262144) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 0w; Significand := 1w |> :
          (3,5) binary_ieee$float)``),
      ("RTN negative underflow to minimum subnormal",
       smtfloatLib.round_CONV,
       ``(round roundTowardNegative (-1r / 262144) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 1w; Exponent := 0w; Significand := 1w |> :
          (3,5) binary_ieee$float)``),
      ("RTP negative ordinary (3,5)", smtfloatLib.round_CONV,
       ``(round roundTowardPositive (-33r / 32) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 1w; Exponent := 15w; Significand := 0w |> :
          (3,5) binary_ieee$float)``),
      ("RTN negative ordinary (3,5)", smtfloatLib.round_CONV,
       ``(round roundTowardNegative (-33r / 32) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 1w; Exponent := 15w; Significand := 1w |> :
          (3,5) binary_ieee$float)``),
      ("RNA ordinary unique inward (3,5)",
       smtfloatLib.round_tiesToAway_CONV,
       ``(round_tiesToAway (33r / 32) :
          (3,5) binary_ieee$float)``, fp3_one),
      ("RNE ordinary halfway disagreement (3,5)",
       smtfloatLib.round_CONV,
       ``(round roundTiesToEven (17r / 16) :
          (3,5) binary_ieee$float)``, fp3_one),
      ("RTP ordinary halfway point (3,5)", smtfloatLib.round_CONV,
       ``(round roundTowardPositive (17r / 16) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 15w; Significand := 1w |> :
          (3,5) binary_ieee$float)``),
      ("RTN ordinary halfway point (3,5)", smtfloatLib.round_CONV,
       ``(round roundTowardNegative (17r / 16) :
          (3,5) binary_ieee$float)``, fp3_one),
      ("RNA ordinary halfway disagreement (3,5)",
       smtfloatLib.round_tiesToAway_CONV,
       ``(round_tiesToAway (17r / 16) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 15w; Significand := 1w |> :
          (3,5) binary_ieee$float)``),
      ("RNA negative halfway disagreement (3,5)",
       smtfloatLib.round_tiesToAway_CONV,
       ``(round_tiesToAway (-17r / 16) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 1w; Exponent := 15w; Significand := 1w |> :
          (3,5) binary_ieee$float)``),
      ("RNA minimum-subnormal halfway (3,5)",
       smtfloatLib.round_tiesToAway_CONV,
       ``(round_tiesToAway (1r / 262144) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 0w; Significand := 1w |> :
          (3,5) binary_ieee$float)``),
      ("RNA negative minimum-subnormal halfway (3,5)",
       smtfloatLib.round_tiesToAway_CONV,
       ``(round_tiesToAway (-1r / 262144) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 1w; Exponent := 0w; Significand := 1w |> :
          (3,5) binary_ieee$float)``),
      ("RNA exact subnormal (10,5)",
       smtfloatLib.round_tiesToAway_CONV,
       ``(round_tiesToAway (3r / 16777216) :
          (10,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 0w; Significand := 3w |> :
          (10,5) binary_ieee$float)``),
      ("RTP exponent-boundary tie (3,5)", smtfloatLib.round_CONV,
       ``(round roundTowardPositive (31r / 16) :
          (3,5) binary_ieee$float)``, fp3_two),
      ("RTN exponent-boundary tie (3,5)", smtfloatLib.round_CONV,
       ``(round roundTowardNegative (31r / 16) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 15w; Significand := 7w |> :
          (3,5) binary_ieee$float)``),
      ("RNA exponent-boundary tie (3,5)",
       smtfloatLib.round_tiesToAway_CONV,
       ``(round_tiesToAway (31r / 16) :
          (3,5) binary_ieee$float)``, fp3_two),
      ("RNA negative exponent-boundary tie (3,5)",
       smtfloatLib.round_tiesToAway_CONV,
       ``(round_tiesToAway (-31r / 16) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 1w; Exponent := 16w; Significand := 0w |> :
          (3,5) binary_ieee$float)``),
      ("RTP overflow (10,5)", smtfloatLib.round_CONV,
       ``(round roundTowardPositive 65520r :
          (10,5) binary_ieee$float)``,
       ``float_plus_infinity (:10 # 5)``),
      ("RTN negative overflow (3,5)", smtfloatLib.round_CONV,
       ``(round roundTowardNegative (-63488r) :
          (3,5) binary_ieee$float)``,
       ``float_minus_infinity (:3 # 5)``),
      ("RTP negative overflow saturates (3,5)", smtfloatLib.round_CONV,
       ``(round roundTowardPositive (-63488r) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 1w; Exponent := 30w; Significand := 7w |> :
          (3,5) binary_ieee$float)``),
      ("RTN positive overflow saturates (3,5)", smtfloatLib.round_CONV,
       ``(round roundTowardNegative 63488r :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 30w; Significand := 7w |> :
          (3,5) binary_ieee$float)``),
      ("RNA overflow midpoint (3,5)",
       smtfloatLib.round_tiesToAway_CONV,
       ``(round_tiesToAway 63488r :
          (3,5) binary_ieee$float)``,
       ``float_plus_infinity (:3 # 5)``),
      ("RNA negative overflow midpoint (3,5)",
       smtfloatLib.round_tiesToAway_CONV,
       ``(round_tiesToAway (-63488r) :
          (3,5) binary_ieee$float)``,
       ``float_minus_infinity (:3 # 5)``),
      ("integral RNA ordinary inward",
       smtfloatLib.integral_round_tiesToAway_CONV,
       ``(integral_round_tiesToAway (6r / 5) :
          (3,5) binary_ieee$float)``, fp3_one),
      ("integral RNA halfway", smtfloatLib.integral_round_tiesToAway_CONV,
       ``(integral_round_tiesToAway (3r / 2) :
          (3,5) binary_ieee$float)``, fp3_two),
      ("integral RNA avoids double rounding",
       smtfloatLib.integral_round_tiesToAway_CONV,
       ``(integral_round_tiesToAway (83r / 5) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 19w; Significand := 0w |> :
          (3,5) binary_ieee$float)``),
      ("integral RNA coarse-format tie",
       smtfloatLib.integral_round_tiesToAway_CONV,
       ``(integral_round_tiesToAway 17r :
          (3,5) binary_ieee$float)``, fp3_eighteen),
      ("integral RNA negative halfway",
       smtfloatLib.integral_round_tiesToAway_CONV,
       ``(integral_round_tiesToAway (-3r / 2) :
          (3,5) binary_ieee$float)``,
       ``(<| Sign := 1w; Exponent := 16w; Significand := 0w |> :
          (3,5) binary_ieee$float)``),
      ("integral RNA overflow midpoint",
       smtfloatLib.integral_round_tiesToAway_CONV,
       ``(integral_round_tiesToAway (-63488r) :
          (3,5) binary_ieee$float)``,
       ``float_minus_infinity (:3 # 5)``),
      ("smt_round RTP dispatch", smtfloatLib.smt_round_CONV,
       ``(smt_round RTP (11r / 10) : (10,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 15w; Significand := 103w |> :
          (10,5) binary_ieee$float)``),
      ("smt_round RNA dispatch", smtfloatLib.smt_round_CONV,
       ``(smt_round RNA (17r / 16) : (3,5) binary_ieee$float)``,
       ``(<| Sign := 0w; Exponent := 15w; Significand := 1w |> :
          (3,5) binary_ieee$float)``),
      ("smt_integral_round RNA dispatch",
       smtfloatLib.smt_integral_round_CONV,
       ``(smt_integral_round RNA (3r / 2) :
          (3,5) binary_ieee$float)``, fp3_two)
    ]
in
  List.app check tests
end

fun smtfloat_ground_evaluation_success () =
let
  fun check (label, tm) =
    (let
       val eval_thm = bossLib.EVAL tm
       val thm =
         Drule.EQT_ELIM eval_thm
         handle Feedback.HOL_ERR _ =>
           die (label ^ " stuck at " ^
             Parse.term_to_string (boolSyntax.rhs (Thm.concl eval_thm)))
     in
       assert_no_hyps (label, thm);
       Library.check_oracle_tags label thm
     end
     handle e => die (label ^ " raised " ^ General.exnMessage e))
  val modes =
    [("RNE", ``RNE``), ("RNA", ``RNA``), ("RTP", ``RTP``),
     ("RTN", ``RTN``), ("RTZ", ``RTZ``)]
  fun each_mode (label, mk_test) =
    List.app (fn (name, mode) => check (label ^ " " ^ name, mk_test mode))
      modes
  val one = ``(smtfp_bits 0w 15w 0w : (3,5) smtfp)``
  val none = ``(smtfp_bits 1w 15w 0w : (3,5) smtfp)``
  val half = ``(smtfp_bits 0w 14w 0w : (3,5) smtfp)``
  val onehalf = ``(smtfp_bits 0w 15w 4w : (3,5) smtfp)``
  val two = ``(smtfp_bits 0w 16w 0w : (3,5) smtfp)``
  val three = ``(smtfp_bits 0w 16w 4w : (3,5) smtfp)``
  fun eq (l, r) = boolSyntax.mk_eq (l, r)
in
  List.app check
    [("literal +infinity normalization",
      ``(smtfp_bits 0w 31w 0w : (3,5) smtfp) = smtfp_pinf``),
     ("literal -infinity normalization",
      ``(smtfp_bits 1w 31w 0w : (3,5) smtfp) = smtfp_ninf``),
     ("literal +zero normalization",
      ``(smtfp_bits 0w 0w 0w : (3,5) smtfp) = smtfp_pzero``),
     ("literal -zero normalization",
      ``(smtfp_bits 1w 0w 0w : (3,5) smtfp) = smtfp_nzero``),
     ("literal NaN normalization",
      ``(smtfp_bits 1w 31w 3w : (3,5) smtfp) = smtfp_nan``),
     ("classification NaN", ``smtfp_is_nan
        (smtfp_nan : (3,5) smtfp)``),
     ("classification signalling", ``~smtfp_is_signalling
        (smtfp_nan : (3,5) smtfp)``),
     ("classification infinite", ``smtfp_is_infinite
        (smtfp_pinf : (3,5) smtfp)``),
     ("classification normal", eq (``smtfp_is_normal ^one``, ``T``)),
     ("classification subnormal", ``smtfp_is_subnormal
        (smtfp_bits 0w 0w 1w : (3,5) smtfp)``),
     ("classification zero", ``smtfp_is_zero
        (smtfp_nzero : (3,5) smtfp)``),
     ("classification finite", eq (``smtfp_is_finite ^one``, ``T``)),
     ("classification integral", eq (``smtfp_is_integral ^one``, ``T``)),
     ("classification negative", eq (``smtfp_is_negative ^none``, ``T``)),
     ("classification positive", eq (``smtfp_is_positive ^one``, ``T``)),
     ("absolute value", eq (``smtfp_abs ^none``, one)),
     ("negation", eq (``smtfp_neg ^one``, none)),
     ("less than", eq (``smtfp_lt ^one ^two``, ``T``)),
     ("less equal", eq (``smtfp_le ^one ^one``, ``T``)),
     ("greater than", eq (``smtfp_gt ^two ^one``, ``T``)),
     ("greater equal", eq (``smtfp_ge ^one ^one``, ``T``)),
     ("IEEE equality", eq (``smtfp_eq ^one ^one``, ``T``)),
     ("unordered", ``smtfp_unordered (smtfp_nan : (3,5) smtfp) ^one``),
     ("minimum", eq (``smtfp_min ^one ^two``, one)),
     ("maximum", eq (``smtfp_max ^one ^two``, two)),
     ("minimum opposite zero choice", ``smtfp_min
        (smtfp_pzero : (3,5) smtfp) smtfp_nzero =
        SmtFp (canon (float_min_zero_choice (:3 # 5)))``),
     ("maximum opposite zero choice", ``smtfp_max
        (smtfp_pzero : (3,5) smtfp) smtfp_nzero =
        SmtFp (canon (float_max_zero_choice (:3 # 5)))``),
     ("remainder", eq (``smtfp_rem ^three ^two``, none)),
     ("remainder infinity NaN", ``smtfp_rem
        (smtfp_pinf : (3,5) smtfp) ^one = smtfp_nan``),
     ("to real", eq (``smtfp_to_real ^one``, ``1r``)),
     ("to real unspecified", ``smtfp_to_real
        (smtfp_pinf : (3,5) smtfp) =
        float_to_real_unspecified
          (float_plus_infinity (:3 # 5))``),
     ("to unsigned BV unspecified", ``(smtfp_to_ubv RNE
        (smtfp_nan : (3,5) smtfp) : word8) =
        float_to_ubv_unspecified RNE
          (float_canon_qnan : (3,5) float)``),
     ("to signed BV unspecified", ``(smtfp_to_sbv RNE
        (smtfp_nan : (3,5) smtfp) : word8) =
        float_to_sbv_unspecified RNE
          (float_canon_qnan : (3,5) float)``),
     ("from IEEE BV", ``smtfp_from_ieee_bv
        (120w : (1 + (5 + 3)) word) = ^one``)];
  each_mode ("add", fn mode => eq (``smtfp_add ^mode ^one ^half``, onehalf));
  each_mode ("sub", fn mode => eq (``smtfp_sub ^mode ^one ^half``, half));
  each_mode ("mul", fn mode => eq (``smtfp_mul ^mode ^onehalf ^two``, three));
  each_mode ("div", fn mode => eq (``smtfp_div ^mode ^three ^two``, onehalf));
  each_mode ("sqrt", fn mode => eq (``smtfp_sqrt ^mode ^one``, one));
  each_mode ("fma", fn mode => eq (``smtfp_fma ^mode ^one ^two ^one``, three));
  List.app check
    [("add infinities NaN", ``smtfp_add RNE
       (smtfp_pinf : (3,5) smtfp) smtfp_ninf = smtfp_nan``),
     ("divide zero by zero NaN", ``smtfp_div RNA
       (smtfp_pzero : (3,5) smtfp) smtfp_nzero = smtfp_nan``),
     ("sqrt negative zero", ``smtfp_sqrt RNA
       (smtfp_nzero : (3,5) smtfp) = smtfp_nzero``),
     ("fma infinity times zero NaN", ``smtfp_fma RTZ
       (smtfp_pinf : (3,5) smtfp) smtfp_pzero ^one = smtfp_nan``)];
  each_mode ("between-format to_fp", fn mode =>
    ``(smtfp_to_fp ^mode ^one : (4,3) smtfp) =
      smtfp_bits 0w 3w 0w``);
  each_mode ("from real", fn mode => eq
    (``(smtfp_from_real ^mode 1r : (3,5) smtfp)``, one));
  each_mode ("from unsigned BV", fn mode => eq
    (``(smtfp_from_ubv ^mode (1w : word8) : (3,5) smtfp)``, one));
  each_mode ("from signed BV", fn mode => eq
    (``(smtfp_from_sbv ^mode (255w : word8) : (3,5) smtfp)``, none));
  List.app check
    [("roundToIntegral RNE", eq
       (``smtfp_round_to_integral RNE ^onehalf``, two)),
     ("roundToIntegral RNA", eq
       (``smtfp_round_to_integral RNA ^onehalf``, two)),
     ("roundToIntegral RTP", eq
       (``smtfp_round_to_integral RTP ^onehalf``, two)),
     ("roundToIntegral RTN", eq
       (``smtfp_round_to_integral RTN ^onehalf``, one)),
     ("roundToIntegral RTZ", eq
       (``smtfp_round_to_integral RTZ ^onehalf``, one)),
     ("to unsigned BV RNE", ``(smtfp_to_ubv RNE ^onehalf : word8) = 2w``),
     ("to unsigned BV RNA", ``(smtfp_to_ubv RNA ^onehalf : word8) = 2w``),
     ("to unsigned BV RTP", ``(smtfp_to_ubv RTP ^onehalf : word8) = 2w``),
     ("to unsigned BV RTN", ``(smtfp_to_ubv RTN ^onehalf : word8) = 1w``),
     ("to unsigned BV RTZ", ``(smtfp_to_ubv RTZ ^onehalf : word8) = 1w``),
     ("to signed BV RNE", ``(smtfp_to_sbv RNE
         (smtfp_bits 1w 15w 4w : (3,5) smtfp) : word8) = 254w``),
     ("to signed BV RNA", ``(smtfp_to_sbv RNA
         (smtfp_bits 1w 15w 4w : (3,5) smtfp) : word8) = 254w``),
     ("to signed BV RTP", ``(smtfp_to_sbv RTP
         (smtfp_bits 1w 15w 4w : (3,5) smtfp) : word8) = 255w``),
     ("to signed BV RTN", ``(smtfp_to_sbv RTN
         (smtfp_bits 1w 15w 4w : (3,5) smtfp) : word8) = 254w``),
     ("to signed BV RTZ", ``(smtfp_to_sbv RTZ
         (smtfp_bits 1w 15w 4w : (3,5) smtfp) : word8) = 255w``)]
end

fun hol_string_to_smt_conversion_success () =
let
  val input =
    ``STRCAT (s:string) t = STRCAT t s /\
      isPREFIX s t /\ (s < t) /\ (s <= t)``
  val expected =
    ``smtstring$smtstr_concat
        (smtstring$str_inj s) (smtstring$str_inj t) =
      smtstring$smtstr_concat
        (smtstring$str_inj t) (smtstring$str_inj s) /\
      smtstring$smtstr_prefixof
        (smtstring$str_inj s) (smtstring$str_inj t) /\
      smtstring$smtstr_lt
        (smtstring$str_inj s) (smtstring$str_inj t) /\
      smtstring$smtstr_le
        (smtstring$str_inj s) (smtstring$str_inj t)``
  val thm = SmtLib.HOL_STRING_TO_SMT_CONV input
  val quantified_input = ``!s:string. isPREFIX s s``
  val quantified_expected =
    ``!s:string.
        smtstring$smtstr_prefixof
          (smtstring$str_inj s) (smtstring$str_inj s)``
  val quantified_thm =
    SmtLib.HOL_STRING_TO_SMT_CONV quantified_input
in
  assert_no_hyps ("HOL_STRING_TO_SMT_CONV", thm);
  assert_concl_alpha
    ("HOL_STRING_TO_SMT_CONV", thm, boolSyntax.mk_eq (input, expected));
  assert_no_hyps ("quantified HOL_STRING_TO_SMT_CONV", quantified_thm);
  assert_concl_alpha
    ("quantified HOL_STRING_TO_SMT_CONV", quantified_thm,
     boolSyntax.mk_eq (quantified_input, quantified_expected))
end

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

fun smtlib_string_literal_codec_success () =
let
  open SmtLib_String_Literal
  fun bytes values = String.implode (List.map Char.chr values)
  val e_acute = bytes [195, 169]
  val euro = bytes [226, 130, 172]
  val smiling = bytes [240, 159, 153, 130]
  val maximum = bytes [240, 175, 191, 191]
  val decode_cases = [
    ("empty", "", []),
    ("plain ASCII", "AZ az09", [65, 90, 32, 97, 122, 48, 57]),
    ("raw two-byte UTF-8", e_acute, [233]),
    ("raw three-byte UTF-8", euro, [8364]),
    ("raw four-byte UTF-8", smiling, [128578]),
    ("raw maximum UTF-8", maximum, [196607]),
    ("mixed raw UTF-8 and escape", e_acute ^ "\\u{20ac}",
      [233, 8364]),
    ("fixed lowercase", "\\u0041", [65]),
    ("fixed uppercase", "\\uFfFf", [65535]),
    ("braced one digit", "\\u{7}", [7]),
    ("braced two digits", "\\u{20}", [32]),
    ("braced three digits", "\\u{123}", [291]),
    ("braced four digits", "\\u{27E8}", [10216]),
    ("braced five digits", "\\u{1f642}", [128578]),
    ("braced uppercase", "\\u{2FFFF}", [196607]),
    ("mixed", "A\\u0042\\u{43}Z", [65, 66, 67, 90]),
    ("quote value", "\"", [34]),
    ("literal backslash", "\\", [92]),
    ("verbatim unknown escape", "\\n", [92, 110]),
    ("verbatim malformed fixed", "\\u12xz", [92, 117, 49, 50, 120, 122]),
    ("verbatim empty braces", "\\u{}", [92, 117, 123, 125]),
    ("verbatim long braces", "\\u{000001}",
      [92, 117, 123, 48, 48, 48, 48, 48, 49, 125])
  ]
  val canonical =
    "\\u{0}\\u{1f} \\u{22}#\\~\\u{7f}\\u{1f600}\\u{2ffff}"
  val canonical_values =
    [0, 31, 32, 34, 35, 92, 126, 127, 128512, 196607]
  val canonical_literals =
    ["", "ASCII", "\\", "\\u{0}", "\\u{22}", "\\u{7f}",
     "\\u{1f642}", "\\u{2ffff}"]
  val literal_escape_sequences = [
    ("literal fixed escape", [92, 117, 48, 48, 52, 49],
      "\\u{5c}u0041"),
    ("literal braced escape", [92, 117, 123, 49, 102, 54, 52, 50, 125],
      "\\u{5c}u{1f642}"),
    ("literal out-of-range escape",
      [92, 117, 123, 51, 48, 48, 48, 48, 125],
      "\\u{5c}u{30000}"),
    ("repeated backslash before escape",
      [92, 92, 117, 48, 48, 52, 49],
      "\\\\u{5c}u0041"),
    ("verbatim unknown escape", [92, 110], "\\n")
  ]
  val z3_pinned = [
    ("\"", [34]),
    ("A\\u{1f642}", [65, 128578]),
    ("\\", [92]),
    ("\\u{2ffff}", [196607]),
    ("\\u{7}", [7])
  ]
  fun check_decode (label, literal, expected) =
    assert (decode_string_literal literal = expected,
      "string literal decoder mismatch for " ^ label)
  fun check_roundtrip values =
    assert
      (decode_string_literal (encode_string_literal values) = values,
       "string literal decode/encode round-trip mismatch")
  fun check_canonical_roundtrip literal =
    assert
      (encode_string_literal (decode_string_literal literal) = literal,
       "canonical string literal encode/decode round-trip mismatch for '" ^
       literal ^ "'")
  fun check_literal_escape_sequence (label, values, expected) =
    let val encoded = encode_string_literal values
    in
      assert (encoded = expected,
        "string literal encoder mismatch for " ^ label);
      assert (decode_string_literal encoded = values,
        "string literal round-trip mismatch for " ^ label)
    end
  fun check_pinned (literal, expected) =
    assert (decode_string_literal literal = expected,
      "string literal decoder rejected pinned Z3 spelling '" ^
      literal ^ "'")
in
  List.app check_decode decode_cases;
  assert (encode_string_literal canonical_values = canonical,
    "string literal encoder did not produce canonical escapes");
  List.app check_canonical_roundtrip canonical_literals;
  List.app check_literal_escape_sequence literal_escape_sequences;
  check_roundtrip [];
  check_roundtrip [65, 34, 92, 0, 196607];
  List.app check_pinned z3_pinned
end

fun smtlib_string_literal_typecheck_success () =
let
  val e_acute = String.implode (List.map Char.chr [195, 169])
  fun single_assertion script =
    case #assertions (SmtLib_Parser.typecheck_script_string script) of
      [assertion] => assertion
    | _ => die "expected exactly one string-literal assertion"
  val assertion =
    single_assertion
      ("(set-logic QF_UF)\n" ^
       "(assert (= \"A\\u0042\\u{1f642}\" " ^
       "\"A\\u{42}\\u{1F642}\"))")
  val (left, right) = boolSyntax.dest_eq assertion
  fun dest_code_points term =
    let
      val (constructor, payload) = Term.dest_comb term
      val () = assert
        (#Name (Term.dest_thy_const constructor) = "SmtStr",
         "SMT-LIB string literal did not use the smtstr wrapper")
      val (elements, ty) = listSyntax.dest_list payload
    in
      assert (ty = numSyntax.num,
        "SMT-LIB string literal payload was not a num list");
      List.map
        (Arbnum.toInt o numSyntax.dest_numeral)
        elements
    end
  val doubled_quote =
    single_assertion
      "(set-logic QF_UF)\n(assert (= \"\"\"\" \"\\u0022\"))"
  val (doubled_left, doubled_right) = boolSyntax.dest_eq doubled_quote
  val raw_utf8 =
    single_assertion
      ("(set-logic QF_UF)\n(assert (= \"" ^ e_acute ^
       "\" \"\\u{e9}\"))")
  val (raw_left, raw_right) = boolSyntax.dest_eq raw_utf8
in
  assert (dest_code_points left = [65, 66, 128578],
    "left SMT-LIB string literal decoded incorrectly");
  assert (dest_code_points right = [65, 66, 128578],
    "right SMT-LIB string literal decoded incorrectly");
  assert (dest_code_points doubled_left = [34] andalso
      dest_code_points doubled_right = [34],
    "doubled quote did not decode as an SMT-LIB quote");
  assert (dest_code_points raw_left = [233] andalso
      dest_code_points raw_right = [233],
    "raw UTF-8 SMT-LIB literal was decoded as bytes")
end

fun smtlib_string_literal_out_of_range_diagnostic () =
let
  val _ = SmtLib_Parser.typecheck_script_string
    "(set-logic QF_UF)\n(assert (= \"\\u{30000}\" \"\"))"
in
  die "out-of-range SMT-LIB string escape typechecked successfully"
end
handle Feedback.HOL_ERR holerr =>
  let val msg = Feedback.message_of holerr
  in
    assert
      (contains "line 2, column 12" msg andalso
       contains "Unicode escape '\\u{30000}' denotes code point 0x30000" msg
       andalso contains "above the SMT-LIB maximum 0x2ffff" msg,
       "out-of-range SMT-LIB string escape diagnostic mismatch: " ^ msg)
  end

fun smtlib_indexed_char_out_of_range_diagnostic () =
let
  val _ = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(assert (= (_ char #x30000) \"\"))")
in
  die "out-of-range indexed SMT-LIB character typechecked successfully"
end
handle Feedback.HOL_ERR holerr =>
  let val msg = Feedback.message_of holerr
  in
    assert
      (contains "could not resolve indexed symbol 'char'" msg andalso
       contains "0x30000" msg,
       "out-of-range indexed character diagnostic mismatch: " ^ msg)
  end

fun smtlib_indexed_char_hex_index_success () =
let
  fun char_assertion index =
    List.hd (parse_smtlib_assertions
      ("(set-logic QF_SLIA)\n" ^
       "(declare-const sC1 String)\n" ^
       "(assert (= (_ char " ^ index ^ ") sC1))\n" ^
       "(exit)\n"))
in
  assert (Term.aconv (char_assertion "#x41") (char_assertion "65"),
    "hexadecimal character index did not parse as the numeral 65")
end

fun smtlib_indexed_char_outbound_range_diagnostic () =
let
  val char_const =
    Term.prim_mk_const {Thy = "smtstring", Name = "smtstr_char"}
  val out_of_range =
    numSyntax.mk_numeral
      (Arbnum.fromInt (SmtLib_String_Literal.max_code_point + 1))
  val char_term = Term.mk_comb (char_const, out_of_range)
  val valid_char =
    Term.mk_comb (char_const, numSyntax.mk_numeral Arbnum.zero)
  val (_, strings) =
    SmtLib.goal_to_SmtLib_translation NONE
      ([], boolSyntax.mk_eq (char_term, valid_char))
in
  die ("out-of-range HOL character was emitted as an SMT-LIB character:\n" ^
    String.concat strings)
end
handle Feedback.HOL_ERR holerr =>
  let val msg = Feedback.message_of holerr
  in
    assert
      (contains "character index 0x30000" msg andalso
       contains "above the SMT-LIB maximum 0x2ffff" msg,
       "outbound indexed character diagnostic mismatch: " ^ msg)
  end

fun smtlib_proof_stream_tokenizer_success () =
let
  val e_acute = String.implode (List.map Char.chr [195, 169])
  val tokens =
    with_temp_file ("(proof \"\" \"" ^ e_acute ^ "\") trailing")
      (fn path =>
        let
          val instream = TextIO.openIn path
          val get_token =
            SmtLib_Parser.make_proof_stream_tokenizer instream
          val result =
            [get_token (), get_token (), get_token (),
             get_token (), get_token ()]
          val _ = TextIO.closeIn instream
        in
          result
        end)
in
  case tokens of
    ["(", "proof", empty_string, raw_string, ")"] =>
      (assert
         (SmtLib_Parser.proof_string_token empty_string = SOME "",
          "stream tokenizer lost the empty String token kind");
       assert
         (SmtLib_Parser.proof_string_token raw_string = SOME e_acute,
          "stream tokenizer changed raw UTF-8 String token bytes"))
  | _ => die "stream proof tokenizer returned unexpected tokens"
end

fun smtlib_proof_stream_tokenizer_marker_collision () =
let
  (* A quoted symbol whose text is the internal String marker must fail
     loudly, not be decoded as a string literal. *)
  val forged = "|\001HolSmtString:x|"
  val tokens =
    with_temp_file ("(proof " ^ forged ^ ")")
      (fn path =>
        let
          val instream = TextIO.openIn path
          val get_token =
            SmtLib_Parser.make_proof_stream_tokenizer instream
          val result =
            Lib.total (fn () => [get_token (), get_token (), get_token ()]) ()
          val _ = TextIO.closeIn instream
        in
          result
        end)
in
  case tokens of
    NONE => ()
  | SOME _ =>
      die "proof tokenizer accepted a symbol forging the string marker"
end

val smt_string_ty =
  Type.mk_thy_type {Thy = "smtstring", Tyop = "smtstr", Args = []}

fun assert_term_alpha label expected actual =
  assert (expected ~~ actual,
    label ^ " mismatch\nexpected: " ^ term_with_types expected ^
    "\nactual: " ^ term_with_types actual)

fun smtlib_string_typed_declaration_success () =
let
  val state =
    SmtLib_Parser.typecheck_script_string
      ("(set-logic ALL)\n" ^
       "(declare-const s String)\n" ^
       "(declare-fun t () String)\n" ^
       "(declare-fun f (String Int) String)\n" ^
       "(declare-fun g (String) Int)\n" ^
       "(assert (distinct s t))\n" ^
       "(check-sat)\n")
  val user_assertion =
    case #assertions state of
      [assertion] => assertion
    | assertions =>
        die ("String declarations produced " ^
          Int.toString (List.length assertions) ^
          " assertions, expected one")
  val s = Term.mk_var ("s", smt_string_ty)
  val t = Term.mk_var ("t", smt_string_ty)
  val query_assertions =
    case #queries state of
      [SmtLib_Parser.QueryCheckSat {assertions, ...}] => assertions
    | _ => die "String declaration elaboration lost check-sat query"
in
  assert_term_alpha "typed String declaration assertion"
    (listSyntax.mk_all_distinct
      (listSyntax.mk_list ([s, t], smt_string_ty)))
    user_assertion;
  assert (ListPair.allEq (fn (x, y) => x ~~ y)
      (query_assertions, #assertions state),
    "check-sat query changed typed String assertions")
end

fun smtlib_string_typed_binder_success () =
let
  val assertion =
    case #assertions
        (SmtLib_Parser.typecheck_script_string
          ("(set-logic ALL)\n" ^
           "(assert (forall ((s String) (i Int))\n" ^
           "  (exists ((t String) (j Int)) (= t s))))\n")) of
      [assertion] => assertion
    | _ => die "String binder elaboration produced the wrong assertion count"
  val s = Term.mk_var ("s", smt_string_ty)
  val i = Term.mk_var ("i", intSyntax.int_ty)
  val t = Term.mk_var ("t", smt_string_ty)
  val j = Term.mk_var ("j", intSyntax.int_ty)
  val equality = boolSyntax.mk_eq (t, s)
  val existential =
    boolSyntax.list_mk_exists ([t, j], equality)
  val expected =
    boolSyntax.list_mk_forall ([s, i], existential)
in
  assert_term_alpha "nested typed String forall/exists"
    expected assertion
end

fun smtlib_string_typed_reset_assertions_success () =
let
  val state =
    SmtLib_Parser.typecheck_script_string
      ("(set-logic QF_S)\n" ^
       "(declare-const s String)\n" ^
       "(assert false)\n" ^
       "(reset-assertions)\n" ^
       "(assert (= s s))\n" ^
       "(check-sat)\n")
  val s = Term.mk_var ("s", smt_string_ty)
in
  case #assertions state of
    [assertion] =>
      assert (assertion ~~ boolSyntax.mk_eq (s, s),
        "reset-assertions retained an old assertion")
  | assertions =>
      die ("reset-assertions String typing produced " ^
        Int.toString (List.length assertions) ^ " assertions, expected one")
end

fun smtlib_string_typed_definitions_success () =
let
  val {assertions, local_definitions, ...} =
    SmtLib_Parser.typecheck_script_string
      ("(set-logic ALL)\n" ^
       "(define-const c String \"x\")\n" ^
       "(define-fun f ((s String)) Int (str.len s))\n" ^
       "(define-fun g ((i Int)) String (str.from_int i))\n" ^
       "(define-fun-rec r ((s String)) Int (str.len s))\n" ^
       "(define-funs-rec\n" ^
       " ((h ((s String)) Int) (k ((i Int)) String))\n" ^
       " ((str.len s) (str.from_int i)))\n")
  val (_, strings) =
    SmtLib.goal_to_SmtLib_translation NONE
      (assertions @ local_definitions, boolSyntax.T)
  val text = String.concat strings
in
  assert (List.null assertions,
    "String definitions introduced synthetic assertions");
  assert (List.length local_definitions = 6,
    "String definition family lost a local definition");
  assert (contains "(Array String Int)" text,
    "String-domain definition was declared with a non-String domain:\n" ^
    text);
  assert (contains "(Array Int String)" text,
    "String-valued definition was declared with a non-String range:\n" ^
    text);
  assert (not (contains "List_Num" text),
    "String definition translation leaked the num-list representation")
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
  (* 'TypeBase.is_constructor' is total, so wrapping it in 'Lib.can' would
     make the test vacuous rather than checking for a constructor. *)
  fun has_typebase_constructor tm =
    term_has_subterm TypeBase.is_constructor tm
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

fun parse_file_match_binder_surface_sort_success () =
let
  val options = {dict_logic = NONE, elaborate_datatypes = true}
  val state =
    SmtLib_Parser.typecheck_script_string_with_options options
      ("(set-logic ALL)\n" ^
       "(declare-datatype PairB16 " ^
       "(par (A) ((mkB16 (fstB16 A) (sndB16 A)))))\n" ^
       "(declare-datatype WrapB16 " ^
       "((wB16 (getB16 (PairB16 Int))) (eB16)))\n" ^
       "(declare-const pB16 (PairB16 Int))\n" ^
       "(declare-const xB16 WrapB16)\n" ^
       "(assert (= pB16 (match xB16 (((wB16 vB16) vB16) (eB16 pB16)))))\n" ^
       "(exit)\n")
  val assertions = #assertions state
in
  assert (List.length assertions = 1,
    "match binder surface sort script produced the wrong assertion count");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "match binder surface sort assertion did not parse as Bool")
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
  assert (SmtLib_Logics.fragment_violation_diagnostic "QF_UF"
          SmtLib_Logics.empty_surface_flags assertions = NONE,
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

(* The mirror image of the test above: a macro body is not an assertion, but
   whatever it contains still reaches the solver through the drivers' goal,
   so the definiens must answer the fragment check.  The outer closure and
   the definiendum application must not: they are artefacts of the equational
   encoding. *)
fun parse_file_define_fun_body_fragment_violation_success () =
let
  val {local_definitions, ...} =
    parse_smtlib_state
      ("(set-logic QF_UF)\n" ^
       "(declare-sort U 0)\n" ^
       "(declare-fun p (U) Bool)\n" ^
       "(define-fun q () Bool (forall ((x U)) (p x)))\n" ^
       "(assert q)\n" ^
       "(check-sat)\n")
  fun definiens definition =
    let
      val (vars, body) = boolSyntax.strip_forall definition
      val rhs = Lib.snd (boolSyntax.dest_eq body)
        handle Feedback.HOL_ERR _ => body
    in
      rhs :: vars
    end
in
  assert (List.length local_definitions = 1,
    "define-fun definition was not tracked as a local definition");
  assert (Option.isSome (SmtLib_Logics.fragment_violation_diagnostic "QF_UF"
      SmtLib_Logics.empty_surface_flags
      (List.concat (List.map definiens local_definitions))),
    "quantifier in a define-fun body escaped the QF_UF fragment check")
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
  assert (SmtLib_Logics.fragment_violation_diagnostic "QF_UF"
          SmtLib_Logics.empty_surface_flags assertions = NONE,
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

fun typechecked_single_assertion script =
  case #assertions (SmtLib_Parser.typecheck_script_string script) of
    [assertion] => assertion
  | _ => die "expected exactly one typechecked assertion"

fun smtlib_lambda_abstraction_alpha_success () =
let
  val state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(assert (= (lambda ((x Int)) (+ x 1)) " ^
     "(lambda ((renamed Int)) (+ renamed 1))))\n")
  val assertion = hd (#assertions state)
  val (left, right) = boolSyntax.dest_eq assertion
  val flags = #surface_flags state
in
  assert (Lib.can Term.dest_abs left andalso Lib.can Term.dest_abs right,
    "lambda did not typecheck to a genuine HOL abstraction");
  assert (Term.aconv left right,
    "alpha-renamed SMT-LIB lambdas were not alpha-equivalent");
  assert (#lambda_used flags,
    "lambda surface event was not recorded in command state");
  assert (not (#arrow_sort_used flags) andalso
      not (#apply_operator_used flags) andalso
      not (#partial_application_used flags),
    "lambda typechecking set an unrelated surface flag")
end

fun smtlib_lambda_nesting_equivalence_success () =
let
  val assertion = typechecked_single_assertion
    ("(set-logic ALL)\n" ^
     "(assert (= (lambda ((x Int) (y Int)) (+ x y)) " ^
     "(lambda ((a Int)) (lambda ((b Int)) (+ a b)))))\n")
  val (flat, nested) = boolSyntax.dest_eq assertion
  fun abstraction_count tm =
    case Lib.total Term.dest_abs tm of
      SOME (_, body) => 1 + abstraction_count body
    | NONE => 0
in
  assert (abstraction_count flat = 2 andalso abstraction_count nested = 2,
    "multi-variable lambda did not build nested HOL abstractions");
  assert (Term.aconv flat nested,
    "multi-variable lambda was not equivalent to nested lambdas")
end

fun smtlib_lambda_under_quantifier_success () =
let
  val assertion = typechecked_single_assertion
    ("(set-logic ALL)\n" ^
     "(assert (forall ((n Int)) " ^
     "(= (lambda ((x Int)) (+ x n)) " ^
     "(lambda ((y Int)) (+ y n)))))\n")
  val (_, body) = boolSyntax.dest_forall assertion
  val (left, right) = boolSyntax.dest_eq body
in
  assert (Lib.can Term.dest_abs left andalso Term.aconv left right,
    "lambda under a quantifier was not preserved alpha-invariantly");
  assert (List.null (Term.free_vars assertion),
    "lambda under a quantifier leaked a bound variable")
end

fun smtlib_lambda_body_sort_diagnostic () =
  let
    val _ = SmtLib_Parser.typecheck_script_string
      ("(set-logic ALL)\n" ^
       "(assert (= (lambda ((x Int)) (+ x true)) " ^
       "(lambda ((y Int)) y)))\n")
  in
    die "ill-sorted lambda body typechecked successfully"
  end
  handle HOL_ERR holerr =>
    let val msg = message_of holerr
    in
      assert (contains "in command 'assert'" msg andalso
          contains "could not resolve symbol '+'" msg andalso
          contains "actual sorts [:int, :bool]" msg,
        "lambda body sort diagnostic was imprecise: " ^ msg)
    end

fun smtlib_lambda_surface_syntax_hygiene () =
let
  fun typecheck text () =
    ignore (SmtLib_Parser.typecheck_script_string text)
  val quoted_state = SmtLib_Parser.typecheck_script_string
    ("(set-logic QF_LIA)\n" ^
     "(declare-fun |lambda| (Int) Int)\n" ^
     "(assert (= (|lambda| 1) 1))\n")
in
  assert (List.length (#assertions quoted_state) = 1,
    "quoted lambda symbol did not remain an ordinary identifier");
  assert (not (#lambda_used (#surface_flags quoted_state)),
    "quoted lambda symbol set the lambda surface flag");
  expect_hol_error_contains "empty lambda binder list"
    "lambda requires at least one sorted variable"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(assert (= (lambda () true) true))\n"));
  expect_hol_error_contains "duplicate lambda binder"
    "duplicate lambda binder 'x'"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(assert (= (lambda ((x Int) (x Int)) x) " ^
       "(lambda ((x Int)) x)))\n"))
end

fun smtlib_apply_operators_success () =
let
  val state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(declare-const f (-> Int Int Int))\n" ^
     "(assert (= (_ f 1 2) (@ f 1 2)))\n" ^
     "(assert (= (_ (lambda ((x Int)) (+ x 1)) 2) " ^
     "(@ (lambda ((renamed Int)) (+ renamed 1)) 2)))\n")
  val (curried_equality, lambda_equality) =
    case #assertions state of
      [first, second] => (first, second)
    | _ => die "apply operator script produced wrong assertion count"
  val (underscore, at_sign) = boolSyntax.dest_eq curried_equality
  val (f_head, args) = strip_comb underscore
  val (lambda_underscore, lambda_at_sign) =
    boolSyntax.dest_eq lambda_equality
  val (lambda_head, _) = Term.dest_comb lambda_underscore
  val flags = #surface_flags state
  val nested_state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(declare-const a (Array Int (-> Int Bool)))\n" ^
     "(assert (_ (select a 0) 1))\n" ^
     "(define-fun use ((g (-> Int Bool))) Bool (_ g 0))\n" ^
     "(assert (use (lambda ((x Int)) true)))\n" ^
     "(declare-const real_indices (Array Real Bool))\n" ^
     "(assert (select real_indices 1))\n" ^
     "(assert (= (ite true 1 2.0) 1.0))\n" ^
     "(declare-datatype D ((mkD (getF (-> Int Bool)))))\n" ^
     "(declare-const d D)\n" ^
     "(assert (_ (getF d) 1))\n" ^
     "(declare-datatype Box (par (T) ((box (value T)))))\n" ^
     "(declare-const b (Box (-> Int Bool)))\n" ^
     "(assert (_ (value b) 1))\n" ^
     "(declare-const mixed (-> Int Real Bool))\n" ^
     "(assert (= (_ mixed 1 2) (@ mixed 1 2)))\n")
  val elaborated_state =
    SmtLib_Parser.typecheck_script_string_with_options
      {dict_logic = NONE, elaborate_datatypes = true}
      ("(set-logic ALL)\n" ^
       "(declare-datatype ApplyBoxA2_06 " ^
       "(par (T) ((applyBoxA2_06 (applyValueA2_06 T)))))\n" ^
       "(declare-const b (ApplyBoxA2_06 (-> Int Bool)))\n" ^
       "(assert (_ (applyValueA2_06 b) 1))\n")
in
  assert (Term.aconv underscore at_sign,
    "_ and @ did not build the same HOL application");
  assert (Lib.fst (Term.dest_var f_head) = "f" andalso
      List.length args = 2,
    "(_ f 1 2) was not built as a left-associated application");
  assert (Term.aconv lambda_underscore lambda_at_sign andalso
      Lib.can Term.dest_abs lambda_head,
    "apply operators did not apply a TASK_05 lambda abstraction");
  assert (#apply_operator_used flags,
    "apply operator surface event was not recorded");
  assert (#lambda_used flags andalso not (#partial_application_used flags),
    "apply operator typechecking set incorrect related surface flags");
  assert (List.length (#assertions nested_state) = 7 andalso
      List.length (#assertions elaborated_state) = 1,
    "apply lost map provenance or existing Int-to-Real coercions")
end

fun smtlib_apply_indexed_ambiguity_success () =
let
  val state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(declare-const w (_ BitVec 8))\n" ^
     "(assert (= ((_ extract 3 0) w) (_ bv3 4)))\n")
  val assertion = hd (#assertions state)
  val w =
    case List.find
        (fn tm => Lib.fst (Term.dest_var tm) = "w")
        (Term.free_vars assertion) of
      SOME tm => tm
    | NONE => die "indexed ambiguity script lost BitVec variable w"
  val word8 = wordsSyntax.mk_word_type
    (fcpLib.index_type (Arbnum.fromInt 8))
in
  assert (Term.type_of assertion = Type.bool,
    "indexed extract ambiguity pin did not produce Bool");
  assert (Type.compare (Term.type_of w, word8) = EQUAL,
    "(_ BitVec 8) no longer denotes the expected word sort");
  assert (not (#apply_operator_used (#surface_flags state)),
    "indexed identifiers were misclassified as the _ apply operator")
end

fun smtlib_apply_operator_diagnostics () =
let
  fun typecheck text () =
    ignore (SmtLib_Parser.typecheck_script_string text)
  fun expect_sort_mismatch () =
    let
      val _ = typecheck
        ("(set-logic ALL)\n" ^
         "(declare-const f (-> Int Bool))\n" ^
         "(assert (_ f true))\n") ()
    in
      die "apply operator accepted an argument of the wrong sort"
    end
    handle HOL_ERR holerr =>
      let val msg = message_of holerr in
        assert (contains "apply operator '_' argument 1 sort mismatch" msg andalso
            contains "expected sort :int" msg andalso
            contains "actual sort :bool" msg,
          "apply operator sort diagnostic was imprecise: " ^ msg)
      end
in
  expect_sort_mismatch ();
  expect_hol_error_contains "apply non-map head"
    "expected a map-sorted term before argument 1"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(assert (= (_ 1 2) 0))\n"));
  expect_hol_error_contains "apply rigid declared sort mismatch"
    "apply operator '_' argument 1 sort mismatch"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(declare-sort U 0)\n" ^
       "(declare-const f (-> U U))\n" ^
       "(assert (= (_ f 1) 1))\n"));
  expect_hol_error_contains "apply rigid composite sort mismatch"
    "apply operator '_' argument 1 sort mismatch"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(declare-sort U 0)\n" ^
       "(declare-const f (-> U Bool))\n" ^
       "(declare-const g (-> U Bool))\n" ^
       "(assert (_ (ite true f g) 1))\n"));
  expect_hol_error_contains "array is not an HO-Core map"
    "expected a map-sorted term before argument 1"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(declare-const a (Array Int Bool))\n" ^
       "(assert (@ a 0))\n"));
  expect_hol_error_contains "array does not match a map argument sort"
    "apply operator '_' argument 1 sort mismatch"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(declare-const f (-> (-> Int Bool) Bool))\n" ^
       "(declare-const a (Array Int Bool))\n" ^
       "(assert (_ f a))\n"));
  expect_hol_error_contains "array cannot define a map-sorted value"
    "surface sort mismatch"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(declare-const a (Array Int Bool))\n" ^
       "(define-const f (-> Int Bool) a)\n"));
  expect_hol_error_contains "curried apply second argument mismatch"
    "apply operator '@' argument 2 sort mismatch"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(declare-const f (-> Int Bool Real))\n" ^
       "(assert (= (@ f 1 2) 0.0))\n"));
  expect_hol_error_contains "indexed family precedence"
    "could not resolve indexed symbol 'extract'"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(declare-const extract (-> Int Int Int))\n" ^
       "(assert (= (_ extract 3 0) 0))\n"));
  expect_hol_error_contains "underscore apply missing argument"
    "expects a map term and at least one argument"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(declare-const f (-> Int Bool))\n" ^
       "(assert (= (_ f) f))\n"));
  expect_hol_error_contains "at-sign apply missing argument"
    "expects a map term and at least one argument"
    (typecheck
      ("(set-logic ALL)\n" ^
       "(declare-const f (-> Int Bool))\n" ^
       "(assert (= (@ f) f))\n"));
  expect_hol_error_contains "apply operator theory scope"
    "is unavailable in the selected theory"
    (typecheck
      ("(set-logic QF_UF)\n" ^
       "(declare-const f (-> Bool Bool))\n" ^
       "(declare-fun |@| ((-> Bool Bool) Bool) Bool)\n" ^
       "(assert (@ f true))\n"))
end

fun smtlib_apply_operator_metadata_success () =
let
  val metadata = SmtLib_Logics.metadata_of_logic "ALL"
  val underscore = find_symbol_metadata "HO-Core" "term" "_" metadata
  val at_sign = find_symbol_metadata "HO-Core" "term" "@" metadata
  val quoted_state = SmtLib_Parser.typecheck_script_string
    ("(set-logic QF_LIA)\n" ^
     "(declare-fun |@| (Int) Int)\n" ^
     "(assert (= (|@| 1) 1))\n")
  val quoted_underscore_state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(declare-const |_| (-> Bool Bool))\n" ^
     "(assert (= (_ |_| true) (@ |_| true)))\n")
in
  assert (metadata_is_official underscore,
    "HO-Core _ apply metadata is not marked official");
  assert (metadata_is_extension at_sign,
    "HO-Core @ apply metadata is not marked as a cvc5 extension");
  assert (#left_associative (#attributes underscore) andalso
      #left_associative (#attributes at_sign),
    "HO-Core apply metadata did not preserve left associativity");
  assert (not (#apply_operator_used (#surface_flags quoted_state)),
    "quoted @ symbol was misclassified as the cvc5 apply operator");
  assert (#apply_operator_used (#surface_flags quoted_underscore_state),
    "quoted |_| map term was misclassified as an indexed family")
end

fun smtlib_partial_application_success () =
let
  val state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(declare-const f (-> Int Bool Real))\n" ^
     "(declare-const residual (-> Bool Real))\n" ^
     "(assert (= (f 1) residual))\n" ^
     "(assert (= (f 1 true) (_ f 1 true)))\n" ^
     "(assert (= ((f 1) true) (f 1 true)))\n")
  val (residual_equality, sugar_equality, nested_equality) =
    case #assertions state of
      [first, second, third] => (first, second, third)
    | _ => die "partial application script produced wrong assertion count"
  val (partial, _) = boolSyntax.dest_eq residual_equality
  val (sugar, explicit) = boolSyntax.dest_eq sugar_equality
  val (nested, flat) = boolSyntax.dest_eq nested_equality
  val flags = #surface_flags state
  val partial_only_state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(declare-const f (-> Int Bool Real))\n" ^
     "(declare-const residual (-> Bool Real))\n" ^
     "(assert (= (f 1) residual))\n")
  val explicit_partial_state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(declare-const f (-> Int Bool Real))\n" ^
     "(declare-const residual (-> Bool Real))\n" ^
     "(assert (= (_ f 1) residual))\n")
  val full_state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(declare-const f (-> Int Bool Real))\n" ^
     "(assert (= (f 1 true) 0.0))\n")
  val coercion_state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(declare-const f (-> Int Real Bool))\n" ^
     "(assert (= ((f 1) 2) (f 1 2)))\n")
  val lambda_state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(assert (= ((lambda ((x Int)) x) 1) 1))\n")
in
  assert (Type.compare
      (Term.type_of partial, Type.--> (Type.bool, realSyntax.real_ty)) = EQUAL,
    "(f 1) did not retain residual sort (-> Bool Real)");
  assert (Term.aconv sugar explicit,
    "full omission sugar did not equal full application via _");
  assert (Term.aconv nested flat,
    "nested omission sugar did not preserve the map-sorted residual");
  assert (#partial_application_used flags andalso
      #apply_operator_used flags,
    "partial map application did not set the expected surface flags");
  assert (#partial_application_used (#surface_flags partial_only_state),
    "partial map-sorted head did not set its surface flag");
  assert (#partial_application_used (#surface_flags explicit_partial_state)
      andalso #apply_operator_used (#surface_flags explicit_partial_state),
    "explicit partial application did not set both surface flags");
  assert (not (#partial_application_used (#surface_flags full_state)),
    "fully applied map-sorted head was marked as partial");
  assert (List.length (#assertions coercion_state) = 1,
    "nested omission sugar lost Int-to-Real argument coercion");
  assert (#partial_application_used (#surface_flags lambda_state),
    "non-atom higher-order application did not set its surface flag")
end

fun smtlib_ranked_partial_application_diagnostic () =
let
  val pinned =
    "function symbol 'g' of rank 2 cannot be partially applied; " ^
    "wrap it in a lambda (SMT-LIB 2.7 §3.9)"
  val partial_script =
    "(set-logic ALL)\n" ^
    "(declare-fun g (Int Bool) Real)\n" ^
    "(assert (= (g 0) (lambda ((b Bool)) 0.0)))\n"
  val exact_state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(declare-fun g (Int Bool) Real)\n" ^
     "(assert (= (g 0 true) 0.0))\n")
  val map_result_state = SmtLib_Parser.typecheck_script_string
    ("(set-logic ALL)\n" ^
     "(declare-fun h (Int) (-> Bool Real))\n" ^
     "(assert (= ((h 0) true) 0.0))\n")
  fun reject_partial () =
    ignore (SmtLib_Parser.typecheck_script_string partial_script)
  val _ =
    (reject_partial ();
     die "ranked function symbol was partially applied")
    handle HOL_ERR holerr =>
      let val msg = message_of holerr in
        assert (String.isSuffix pinned msg,
          "ranked partial-application diagnostic changed: " ^ msg)
      end
in
  assert (List.length (#assertions exact_state) = 1,
    "exact application of a ranked function symbol stopped typechecking");
  assert (List.length (#assertions map_result_state) = 1,
    "map result of an exact ranked application could not be applied")
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
    let
      val state = SmtLib_Parser.typecheck_script_string
        ("(set-logic QF_UF)\n" ^
         "(declare-fun h ((-> Bool Bool)) Bool)\n" ^
         "(check-sat)\n")
      val diagnostic = SmtLib_Logics.fragment_violation_diagnostic "QF_UF"
        (#surface_flags state) (#assertions state)
    in
      assert (diagnostic = SOME
          ("higher-order construct (arrow sort) is outside logic fragment " ^
           "QF_UF"),
        "arrow sort in QF_UF did not produce its fragment violation")
    end;
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
        SmtLib_Logics.fragment_violation_diagnostic logic
          (#surface_flags state) (#assertions state)
      end
    fun fragment_with_options options logic text =
      let
        val state = parse_smtlib_state_with_options options text
      in
        SmtLib_Logics.fragment_violation_diagnostic logic
          (#surface_flags state) (#assertions state)
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
    fun expect_fragment_with_options label options logic text expected =
      case fragment_with_options options logic text of
        SOME msg =>
          assert (contains expected msg,
            label ^ " diagnostic missed '" ^ expected ^ "': " ^ msg)
      | NONE => die (label ^ " fragment violation was not detected")
    fun expect_no_fragment_with_options label options logic text =
      case fragment_with_options options logic text of
        SOME msg =>
          die (label ^ " reported a spurious fragment violation: " ^ msg)
      | NONE => ()
    fun expect_term_fragment label logic term expected =
      case SmtLib_Logics.fragment_violation_diagnostic logic
          SmtLib_Logics.empty_surface_flags [term] of
        SOME msg =>
          assert (contains expected msg,
            label ^ " diagnostic missed '" ^ expected ^ "': " ^ msg)
      | NONE => die (label ^ " fragment violation was not detected")
    fun expect_no_term_fragment label logic term =
      case SmtLib_Logics.fragment_violation_diagnostic logic
          SmtLib_Logics.empty_surface_flags [term] of
        SOME msg =>
          die (label ^ " reported a spurious fragment violation: " ^ msg)
      | NONE => ()
    fun script logic body =
      "(set-logic " ^ logic ^ ")\n" ^ body ^ "(check-sat)\n"
    fun script_for_checker parse_logic body =
      script parse_logic body
    val all_dicts = {dict_logic = SOME "ALL", elaborate_datatypes = false}
    val all_elaborated =
      {dict_logic = SOME "ALL", elaborate_datatypes = true}
  in
    expect_fragment "FO arrow sort" "QF_LIA"
      (script "QF_LIA"
       ("(declare-const f (-> Int Int))\n" ^
        "(assert (= f f))\n"))
      "higher-order construct (arrow sort) is outside logic fragment QF_LIA";
    expect_fragment_with_options "FO elaborated datatype arrow sort"
      all_elaborated "QF_UF"
      (script "QF_UF"
       ("(declare-datatype FragArrowA4_08 " ^
        "((mkFragArrowA4_08 " ^
        "(fragMapA4_08 (-> Bool Bool)))))\n" ^
        "(declare-const fragValueA4_08 FragArrowA4_08)\n" ^
        "(assert (= (fragMapA4_08 fragValueA4_08) " ^
        "(fragMapA4_08 fragValueA4_08)))\n"))
      ("higher-order construct (arrow sort) is outside logic fragment " ^
       "QF_UF");
    expect_hol_error_contains "malformed elaborated datatype arrow sort"
      "function sort '->' expects at least one domain sort and one range sort"
      (fn () => ignore (parse_smtlib_state_with_options all_elaborated
        ("(set-logic ALL)\n" ^
         "(declare-datatype FragBadArrowA4_08 " ^
         "((mkFragBadArrowA4_08 (fragBadMapA4_08 (-> Bool)))))\n")));
    expect_fragment "FO lambda" "QF_UF"
      (script "QF_UF"
       ("(assert (= (lambda ((x Bool)) x) " ^
        "(lambda ((y Bool)) y)))\n"))
      "higher-order construct (lambda) is outside logic fragment QF_UF";
    expect_fragment_with_options "FO apply operator" all_dicts "QF_AUFLIA"
      (script "QF_AUFLIA"
       ("(declare-const f (-> Int Bool))\n" ^
        "(assert (_ f 0))\n"))
      ("higher-order construct (apply operator) is outside logic fragment " ^
       "QF_AUFLIA");
    expect_fragment_with_options "FO partial application" all_dicts
      "QF_UFLIA"
      (script "QF_UFLIA"
       ("(declare-const f (-> Int Bool Bool))\n" ^
        "(declare-const residual (-> Bool Bool))\n" ^
        "(assert (= (f 0) residual))\n"))
      ("higher-order construct (partial application) is outside logic " ^
       "fragment QF_UFLIA");
    expect_no_fragment "ALL arrow sort" "ALL"
      (script "ALL"
       ("(declare-const f (-> Int Int))\n" ^
        "(assert (= f f))\n"));
    expect_no_fragment "ALL lambda" "ALL"
      (script "ALL"
       ("(assert (= (lambda ((x Bool)) x) " ^
        "(lambda ((y Bool)) y)))\n"));
    expect_no_fragment "ALL apply operator" "ALL"
      (script "ALL"
       ("(declare-const f (-> Int Bool))\n" ^
        "(assert (_ f 0))\n"));
    expect_no_fragment "ALL partial application" "ALL"
      (script "ALL"
       ("(declare-const f (-> Int Bool Bool))\n" ^
        "(declare-const residual (-> Bool Bool))\n" ^
        "(assert (= (f 0) residual))\n"));
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
    expect_no_fragment "SMT String literal payload is not a datatype sort"
      "QF_S"
      (script "QF_S"
       "(assert (= \"a\" \"a\"))\n");
    expect_fragment "RegLan operator unavailable" "QF_UF"
      (script_for_checker "ALL"
       "(declare-const s String)\n" ^
       "(assert (str.in_re s (re.comp (str.to_re s))))\n")
      "string term sort";
    expect_no_fragment "RegLan operator available" "QF_S"
      (script "QF_S"
       "(declare-const s String)\n" ^
       "(assert (str.in_re s (re.comp (str.to_re s))))\n");
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
    expect_no_term_fragment "native HOL string is not a datatype sort"
      "QF_UF" ``("" : string) = ""``;
    expect_no_fragment "Core distinct internal list wrapper" "QF_LIA"
      (script "QF_LIA"
       "(assert (distinct 0 1 2))\n");
    expect_no_fragment "nested Core distinct internal list wrapper" "QF_LIA"
      (script "QF_LIA"
       "(assert (not (distinct 0 1)))\n");
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
    expect_no_gap "UnicodeStrings replay" "QF_SLIA"
      ("(set-logic QF_SLIA)\n" ^
       "(declare-const s String)\n" ^
       "(assert (str.prefixof s (str.++ s s)))\n" ^
       "(check-sat)\n");
    expect_no_gap "RegLan replay" "QF_SLIA"
      ("(set-logic QF_SLIA)\n" ^
       "(declare-const s String)\n" ^
       "(assert (str.in_re s (str.to_re s)))\n" ^
       "(check-sat)\n");
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
  val str_lt = find_symbol_metadata "UnicodeStrings" "term" "str.<"
    string_metadata
  val str_le = find_symbol_metadata "UnicodeStrings" "term" "str.<="
    string_metadata
  val char_symbol = find_symbol_metadata "UnicodeStrings" "term" "char"
    string_metadata
  val re_union = find_symbol_metadata "UnicodeStrings" "term" "re.union"
    string_metadata
  val re_inter = find_symbol_metadata "UnicodeStrings" "term" "re.inter"
    string_metadata
  val re_comp = find_symbol_metadata "UnicodeStrings" "term" "re.comp"
    string_metadata
  val re_power = find_symbol_metadata "UnicodeStrings" "term" "re.^"
    string_metadata
  val re_loop = find_symbol_metadata "UnicodeStrings" "term" "re.loop"
    string_metadata
  val string_term_names = [
    "str.++", "str.len", "str.<", "str.<=", "str.at", "str.substr",
    "str.prefixof", "str.suffixof", "str.contains", "str.indexof",
    "str.replace", "str.replace_all", "str.is_digit", "str.to_code",
    "str.from_code", "str.to_int", "str.from_int", "str.to_re",
    "str.in_re", "str.replace_re", "str.replace_re_all", "char",
    "re.none", "re.all", "re.allchar", "re.++", "re.union", "re.inter",
    "re.diff", "re.comp", "re.*", "re.+", "re.opt", "re.range",
    "re.^", "re.loop"
  ]
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
  assert (#chainable (#attributes str_lt) andalso
      #chainable (#attributes str_le),
    "string ordering metadata did not preserve chainability");
  assert (#indexed (#attributes char_symbol),
    "indexed Unicode character metadata was not preserved");
  assert (#left_associative (#attributes re_union) andalso
      #left_associative (#attributes re_inter),
    "regex union/intersection metadata did not preserve left associativity");
  assert (metadata_is_official re_comp,
    "re.comp metadata is not marked official");
  assert (#indexed (#attributes re_power) andalso
      #indexed (#attributes re_loop),
    "regex power/loop metadata did not preserve indexed attributes");
  List.app
    (fn name =>
      assert (metadata_is_official
        (find_symbol_metadata "UnicodeStrings" "term" name string_metadata),
        "missing official UnicodeStrings metadata for " ^ name))
    string_term_names;
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
       "(declare-const u String)\n" ^
       "(assert (and " ^
       "(= (str.++ s t) s) " ^
       "(= (str.len s) 0) " ^
       "(str.< s t) (str.<= s t) " ^
       "(= (str.at s 0) t) " ^
       "(= (str.substr s 0 1) t) " ^
       "(str.prefixof s t) (str.suffixof s t) (str.contains s t) " ^
       "(= (str.indexof s t 0) 0) " ^
       "(= (str.replace s t u) s) " ^
       "(= (str.replace_all s t u) s) " ^
       "(str.is_digit s) " ^
       "(= (str.to_code s) 0) " ^
       "(= (str.from_code 65) s) " ^
       "(= (str.to_int s) 0) " ^
       "(= (str.from_int 65) s) " ^
       "(= (str.replace_re s (str.to_re t) u) s) " ^
       "(= (str.replace_re_all s (str.to_re t) u) s) " ^
       "(= (_ char #x41) s) " ^
       "(str.in_re s re.none) " ^
       "(str.in_re s re.all) " ^
       "(str.in_re s re.allchar) " ^
       "(str.in_re s (re.++ (str.to_re s) (str.to_re t))) " ^
       "(str.in_re s (re.union (str.to_re s) (str.to_re t))) " ^
       "(str.in_re s (re.inter (str.to_re s) (str.to_re t))) " ^
       "(str.in_re s (re.diff (str.to_re s) (str.to_re t))) " ^
       "(str.in_re s (re.comp (str.to_re t))) " ^
       "(str.in_re s (re.* (str.to_re t))) " ^
       "(str.in_re s (re.+ (str.to_re t))) " ^
       "(str.in_re s (re.opt (str.to_re t))) " ^
       "(str.in_re s (re.range s t)) " ^
       "(str.in_re s ((_ re.^ 2) (str.to_re t))) " ^
       "(str.in_re s ((_ re.loop 1 3) (str.to_re t)))))\n" ^
       "(exit)\n")
  val expected_constants = [
    "smtstr_concat", "smtstr_len", "smtstr_lt", "smtstr_le",
    "smtstr_at", "smtstr_substr", "smtstr_prefixof",
    "smtstr_suffixof", "smtstr_contains", "smtstr_indexof",
    "smtstr_replace", "smtstr_replace_all", "smtstr_is_digit",
    "smtstr_to_code", "smtstr_from_code", "smtstr_to_int",
    "smtstr_from_int", "smtstr_char", "reglan_to_re", "smt_in_re",
    "smtstr_replace_re", "smtstr_replace_re_all", "reglan_none",
    "reglan_all", "reglan_allchar", "reglan_concat", "reglan_union",
    "reglan_inter", "reglan_diff", "reglan_comp", "reglan_star",
    "reglan_plus", "reglan_opt", "reglan_range", "reglan_power",
    "reglan_loop"
  ]
  fun is_smtstring_const name tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Thy = "smtstring" andalso Name = name end
  fun has_smtstring_const name =
    List.exists (term_has_subterm (is_smtstring_const name)) assertions
  fun is_placeholder tm =
    Term.is_var tm andalso
    String.isPrefix "smtlib_" (Lib.fst (Term.dest_var tm))
  fun has_old_reglan_type tm =
    Library.type_contains
      (fn ty =>
        Type.is_vartype ty andalso
        String.isPrefix "'smtlib_RegLan" (Type.dest_vartype ty))
      (Term.type_of tm)
in
  assert (List.length assertions = 1,
    "string/regex signature script introduced synthetic assertions");
  assert (Term.type_of (List.hd assertions) = Type.bool,
    "string/regex signature assertion did not parse as Bool");
  List.app
    (fn name =>
      assert (has_smtstring_const name,
        "string/regex surface did not produce smtstringTheory." ^ name))
    expected_constants;
  assert (not (List.exists (term_has_subterm is_placeholder) assertions),
    "string/regex surface retained an smtlib_* placeholder");
  assert (not (List.exists
      (fn assertion =>
        List.exists has_old_reglan_type (Library.subterms assertion))
      assertions),
    "string/regex surface retained the 'smtlib_RegLan type")
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

fun smtlib_ho_logic_packets_success () =
let
  val logic_pairs = [
    ("HO_ALL", "ALL"),
    ("HO_UF", "UF"),
    ("HO_QF_UF", "QF_UF"),
    ("HO_UFLIA", "UFLIA"),
    ("HO_QF_UFLIA", "QF_UFLIA"),
    ("HO_UFLRA", "UFLRA"),
    ("HO_QF_UFLRA", "QF_UFLRA"),
    ("HO_AUFLIA", "AUFLIA"),
    ("HO_AUFLIRA", "AUFLIRA"),
    ("HO_QF_AUFLIA", "QF_AUFLIA")
  ]
  fun same_base_fragment
      ((ho : SmtLib_Logics.logic_fragment),
       (base : SmtLib_Logics.logic_fragment)) =
    #quantifiers ho = #quantifiers base andalso
    #uninterpreted ho = #uninterpreted base andalso
    #arrays ho = #arrays base andalso
    #arith ho = #arith base andalso
    #ints ho = #ints base andalso
    #reals ho = #reals base andalso
    #bitvectors ho = #bitvectors base andalso
    #strings ho = #strings base andalso
    #floatingpoint ho = #floatingpoint base andalso
    #datatypes ho = #datatypes base
  fun metadata_is_cvc5_extension
      ({source = SmtLib_Theories.Extension "cvc5", ...}
         : SmtLib_Theories.symbol_metadata) = true
    | metadata_is_cvc5_extension _ = false
  fun require_packet (logic, base_logic) =
    let
      val _ = SmtLib_Logics.parsedicts_of_logic logic
      val metadata = SmtLib_Logics.metadata_of_logic logic
      val underscore = find_symbol_metadata "HO-Core" "term" "_" metadata
      val at_sign = find_symbol_metadata "HO-Core" "term" "@" metadata
      val ho_fragment = SmtLib_Logics.logic_fragment_of_logic logic
      val base_fragment = SmtLib_Logics.logic_fragment_of_logic base_logic
      val state = SmtLib_Parser.typecheck_script_string
        ("(set-logic " ^ logic ^ ")\n" ^
         "(assert (= (lambda ((x Bool)) x) " ^
         "(lambda ((y Bool)) y)))\n")
      val diagnostic = SmtLib_Logics.fragment_violation_diagnostic logic
        (#surface_flags state) (#assertions state)
    in
      assert (metadata_is_official underscore,
        logic ^ " did not expose the official HO-Core apply operator");
      assert (metadata_is_cvc5_extension at_sign,
        logic ^ " did not expose the cvc5 HO-Core apply extension");
      assert (#higher_order ho_fragment andalso
          same_base_fragment (ho_fragment, base_fragment),
        logic ^ " did not inherit the fragment of " ^ base_logic);
      assert (List.length (#assertions state) = 1,
        logic ^ " did not typecheck its higher-order smoke case");
      assert (diagnostic = NONE,
        logic ^ " rejected its higher-order smoke case")
    end
  fun unknown_dicts () =
    ignore (SmtLib_Logics.parsedicts_of_logic "HO_XYZ")
  fun unknown_metadata () =
    ignore (SmtLib_Logics.metadata_of_logic "HO_XYZ")
in
  List.app require_packet logic_pairs;
  assert (not (#quantifiers
      (SmtLib_Logics.logic_fragment_of_logic "HO_QF_UF")),
    "HO_QF_UF unexpectedly permits quantifiers");
  assert (#arrays
      (SmtLib_Logics.logic_fragment_of_logic "HO_AUFLIA"),
    "HO_AUFLIA did not inherit array support");
  expect_hol_error_contains "unknown HO logic dictionaries"
    "unknown logic 'HO_XYZ'" unknown_dicts;
  expect_hol_error_contains "unknown HO logic metadata"
    "unknown logic 'HO_XYZ'" unknown_metadata
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
        "datatype fragment bit was wrong for " ^ logic);
      assert (#higher_order fragment = (logic = "ALL"),
        "higher-order fragment bit was wrong for " ^ logic)
    end
in
  List.app require_logic logics;
  assert (#higher_order (SmtLib_Logics.logic_fragment_of_logic "HO_QF_UF")
      andalso
      not (#quantifiers
        (SmtLib_Logics.logic_fragment_of_logic "HO_QF_UF")) andalso
      #uninterpreted
        (SmtLib_Logics.logic_fragment_of_logic "HO_QF_UF"),
    "HO_QF_UF fragment did not inherit its QF_UF stem");
  assert (SmtLib_Logics.logic_fragment_of_logic "HO_ALL" =
      SmtLib_Logics.logic_fragment_of_logic "ALL",
    "HO_ALL fragment did not inherit ALL");
  assert (#higher_order
      (SmtLib_Logics.logic_fragment_of_logic "HO_AUFLIA") andalso
      #arrays (SmtLib_Logics.logic_fragment_of_logic "HO_AUFLIA") andalso
      SmtLib_Logics.is_linear_arith_logic "HO_AUFLIA",
    "HO_AUFLIA fragment did not inherit its AUFLIA stem")
end

fun smtlib_translation_logic_inference_success () =
let
  fun mk_features (quantifiers, uninterpreted, arrays, bitvectors,
                   integers, reals, strings, nonlinear) =
    SmtLib.LogicFeatures {
      quantifiers = quantifiers, uninterpreted = uninterpreted,
      arrays = arrays, bitvectors = bitvectors, integers = integers,
      reals = reals, strings = strings, datatypes = false,
      nonlinear = nonlinear, higher_order = false}
  fun mk_datatype_features (quantifiers, uninterpreted, arrays, bitvectors,
                            integers, reals, strings, nonlinear) =
    SmtLib.LogicFeatures {
      quantifiers = quantifiers, uninterpreted = uninterpreted,
      arrays = arrays, bitvectors = bitvectors, integers = integers,
      reals = reals, strings = strings, datatypes = true,
      nonlinear = nonlinear, higher_order = false}
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
  expect_logic "QF_NIA" ``ediv (x:int) y = x``;
  expect_logic "QF_NIA" ``emod (x:int) y = x``;
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
    datatypes = true, nonlinear = false, higher_order = false}
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

fun smtlib_distinct_translation_success () =
let
  val one = intSyntax.term_of_int (Arbint.fromInt 1)
  fun all_distinct elements = listSyntax.mk_all_distinct
    (listSyntax.mk_list (elements, intSyntax.int_ty))
  fun smtlib_text goal =
    let val (_, strings) = SmtLib.goal_to_SmtLib_translation NONE ([], goal)
    in String.concat strings end
  val assertion = listSyntax.mk_all_distinct
    (listSyntax.mk_list ([one, one], intSyntax.int_ty))
  val (translation, strings) =
    SmtLib.goal_to_SmtLib_with_get_proof_translation NONE
      ([], boolSyntax.mk_neg assertion)
  val text = String.concat strings
  val empty_text = smtlib_text (all_distinct [])
  val singleton_text = smtlib_text (all_distinct [one])
in
  assert (SmtLib.translation_logic translation = "QF_LIA",
    "Core.distinct internal list wrapper widened inferred logic to " ^
    SmtLib.translation_logic translation);
  assert (contains "(distinct 1 1)" text,
    "Core.distinct did not translate to direct SMT-LIB arguments:\n" ^ text);
  assert (not (contains "declare-datatypes" text),
    "Core.distinct internal list wrapper leaked a datatype declaration:\n" ^
    text);
  assert (contains "(assert (not true))" empty_text andalso
      not (contains "distinct" empty_text),
    "empty ALL_DISTINCT did not translate to true:\n" ^ empty_text);
  assert (contains "(assert (not true))" singleton_text andalso
      not (contains "distinct" singleton_text),
    "singleton ALL_DISTINCT did not translate to true:\n" ^ singleton_text)
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
  assert_has "HOL string uninterpreted sort" "(declare-sort t0 0)"
    builtin_text;
  assert_has "HOL string uninterpreted sort" "(declare-fun v0 () t0)"
    builtin_text;
  assert_lacks "HOL string uninterpreted sort" "String" builtin_text;
  assert_lacks "HOL string uninterpreted sort" "(declare-datatypes"
    builtin_text;
  assert (has_datatype_record,
    "translation records did not include datatype declaration record")
end

fun smtlib_extended_hol_encoding_records_success () =
let
  (* HOL strings reach SMT-LIB only through str_inj, so the encoding records
     are driven from the injected surface. *)
  val term =
    ``smtstring$smtstr_concat
        (smtstring$str_inj s) (smtstring$str_inj t) =
      smtstring$smtstr_concat
        (smtstring$str_inj t) (smtstring$str_inj s)``
  val (logic, _, records, translation) = inferred_logic term
  val has_string_encoding =
    List.exists
      (fn SmtLib.HOLTheoryEncoding {
            feature, smt_theory = "UnicodeStrings",
            mode = SmtLib.NativeSMTLIB, parse = true,
            typecheck = true, translate = true, replay = false,
            proof_obligation, ...} =>
            contains "HOL strings" feature
            andalso contains "Checked replay" proof_obligation
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
  val has_regex_translation_row =
    List.exists
      (fn SmtLib.HOLTheoryEncoding {
            smt_theory = "UnicodeStrings RegLan",
            translate = true, replay = false, notes, ...} =>
            contains "no implicit RegLan injection" notes
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
    "translation records lacked sequence/set/bag matrix row");
  assert (has_regex_translation_row,
    "translation records lacked native RegLan translation row")
end

fun smtlib_hol_string_injection_translation_success () =
let
  val original =
    ([], ``STRCAT (s:string) t = STRCAT t s``)
  val (goal as (assumptions, conclusion), _) =
    SolverSpec.simplify (SmtLib.SIMP_TAC true) original
  val expected =
    ``smtstring$smtstr_concat
        (smtstring$str_inj s) (smtstring$str_inj t) =
      smtstring$smtstr_concat
        (smtstring$str_inj t) (smtstring$str_inj s)``
  val (translation, strings) =
    SmtLib.goal_to_SmtLib_translation NONE goal
  val text = String.concat strings
  val (_, standard_strings) =
    SmtLib.goal_to_SmtLib_translation_with_regime
      (SmtLib.HigherOrder SmtLib.Standard27) NONE goal
  val standard_text = String.concat standard_strings
  val (z3_translation, z3_strings) =
    Z3.goal_to_SmtLib_translation_for_version (SOME "4.15.3") goal
  val z3_text = String.concat z3_strings
in
  assert (List.null assumptions andalso Term.aconv conclusion expected,
    "HOL string preprocessing did not expose the str_inj surface");
  assert (contains "(set-logic QF_S)\n" text,
    "injected HOL string goal inferred " ^
    SmtLib.translation_logic translation ^ ":\n" ^ text);
  assert (contains "(declare-fun v0 () String)\n" text andalso
      contains "(declare-fun v1 () String)\n" text,
    "injected HOL strings were not generalized to String variables");
  assert (contains "(declare-const v0 String)\n" standard_text andalso
      contains "(declare-const v1 String)\n" standard_text,
    "Standard27 did not thread its declaration regime through injection");
  assert (contains
      "(= (str.++ v0 v1) (str.++ v1 v0))" text,
    "injected HOL string goal changed the pinned operator emission");
  assert (SmtLib.translation_logic z3_translation = "QF_S" andalso
      contains "(set-logic QF_S)\n" z3_text,
    "Z3 adapter widened the injected HOL string goal to " ^
    SmtLib.translation_logic z3_translation ^ ":\n" ^ z3_text);
  assert (not (contains "List_Num" text) andalso
      not (contains "str_inj" text),
    "injection internals leaked into emitted SMT-LIB");
  assert_goal_roundtrip "HOL string injection" goal;
  ignore (SmtLib.translation_records translation)
end

fun smtlib_native_string_translation_success () =
let
  fun translate_assertions assertions =
    case List.rev assertions of
      conclusion :: reversed_assumptions =>
        SmtLib.goal_to_SmtLib_translation NONE
          (List.rev reversed_assumptions, conclusion)
    | [] => die "native string script produced no assertions"
  fun translate_script script =
    translate_assertions (parse_smtlib_assertions script)
  fun text_of result = String.concat (Lib.snd result)
  fun assert_has label text snippet =
    assert (contains snippet text,
      label ^ " missed SMT-LIB snippet '" ^ snippet ^ "':\n" ^ text)
  fun assert_lacks label text snippet =
    assert (not (contains snippet text),
      label ^ " unexpectedly emitted '" ^ snippet ^ "':\n" ^ text)
  val full_surface =
    translate_script
      ("(set-logic QF_SLIA)\n" ^
       "(declare-const s String)\n" ^
       "(declare-const t String)\n" ^
       "(declare-const u String)\n" ^
       "(assert (and " ^
       "(= (str.++ s t) s) (= (str.len s) 0) " ^
       "(str.< s t) (str.<= s t) " ^
       "(= (str.at s 0) t) (= (str.substr s 0 1) t) " ^
       "(str.prefixof s t) (str.suffixof s t) (str.contains s t) " ^
       "(= (str.indexof s t 0) 0) " ^
       "(= (str.replace s t u) s) " ^
       "(= (str.replace_all s t u) s) " ^
       "(str.is_digit s) (= (str.to_code s) 0) " ^
       "(= (str.from_code 65) s) (= (str.to_int s) 0) " ^
       "(= (str.from_int 65) s) " ^
       "(= (str.replace_re s (str.to_re t) u) s) " ^
       "(= (str.replace_re_all s (str.to_re t) u) s) " ^
       "(= (_ char #x41) s) " ^
       "(str.in_re s re.none) (str.in_re s re.all) " ^
       "(str.in_re s re.allchar) " ^
       "(str.in_re s (re.++ (str.to_re s) (str.to_re t))) " ^
       "(str.in_re s (re.union (str.to_re s) (str.to_re t))) " ^
       "(str.in_re s (re.inter (str.to_re s) (str.to_re t))) " ^
       "(str.in_re s (re.diff (str.to_re s) (str.to_re t))) " ^
       "(str.in_re s (re.comp (str.to_re t))) " ^
       "(str.in_re s (re.* (str.to_re t))) " ^
       "(str.in_re s (re.+ (str.to_re t))) " ^
       "(str.in_re s (re.opt (str.to_re t))) " ^
       "(str.in_re s (re.range s t)) " ^
       "(str.in_re s ((_ re.^ 2) (str.to_re t))) " ^
       "(str.in_re s ((_ re.loop 1 3) (str.to_re t)))))\n")
  val full_translation = Lib.fst full_surface
  val full_text = text_of full_surface
  val expected_symbols = [
    "str.++", "str.len", "str.<", "str.<=", "str.at", "str.substr",
    "str.prefixof", "str.suffixof", "str.contains", "str.indexof",
    "str.replace", "str.replace_all", "str.is_digit", "str.to_code",
    "str.from_code", "str.to_int", "str.from_int", "str.replace_re",
    "str.replace_re_all", "(_ char #x41)", "str.in_re", "str.to_re",
    "re.none", "re.all", "re.allchar", "re.++", "re.union", "re.inter",
    "re.diff", "re.comp", "re.*", "re.+", "re.opt", "re.range",
    "(_ re.^ 2)", "(_ re.loop 1 3)"
  ]
  val string_ty = smt_string_ty
  val s = Term.mk_var ("literal_s", string_ty)
  val literal =
    Term.mk_comb
      (Term.prim_mk_const {Thy = "smtstring", Name = "SmtStr"},
       listSyntax.mk_list
         (List.map (numSyntax.mk_numeral o Arbnum.fromInt)
           [0, 31, 32, 34, 65, 127, 128512, 196607],
          numSyntax.num))
  val literal_result =
    SmtLib.goal_to_SmtLib_translation NONE
      ([], boolSyntax.mk_eq (s, literal))
  val literal_text = text_of literal_result
  val binder_result =
    translate_script
      ("(set-logic QF_S)\n" ^
       "(assert (forall ((s String)) (= (str.++ s \"\") s)))\n")
  val binder_text = text_of binder_result
  val qf_s_result =
    translate_script
      ("(set-logic QF_S)\n" ^
       "(declare-const s String)\n" ^
       "(declare-const t String)\n" ^
       "(assert (= (str.++ s t) (str.++ t s)))\n")
  val nonlinear_result =
    translate_script
      ("(set-logic QF_SNIA)\n" ^
       "(declare-const s String)\n" ^
       "(declare-const t String)\n" ^
       "(assert (= (* (str.len s) (str.len t)) 0))\n")
  val raw_list_text = text_of
    (SmtLib.goal_to_SmtLib_translation NONE
      ([], ``(raw_xs:num list) = raw_ys``))
in
  assert
    (SmtLib.translation_logic full_translation = "QF_SLIA",
     "full native string surface inferred " ^
     SmtLib.translation_logic full_translation ^ ":\n" ^ full_text);
  List.app (assert_has "full native string surface" full_text)
    expected_symbols;
  assert_has "native String declaration" full_text
    "(declare-fun v0 () String)";
  assert_lacks "native String guards" full_text "wfstr";
  assert_lacks "native String representation" full_text "List_Num";
  assert_lacks "native RegLan representation" full_text
    "declare-datatypes";
  assert_has "native string literal" literal_text
    "\"\\u{0}\\u{1f} \\u{22}A\\u{7f}\\u{1f600}\\u{2ffff}\"";
  assert_has "typed String binder" binder_text
    "(forall ((b0 String)) (= (str.++ b0 \"\") b0))";
  assert_lacks "typed String binder" binder_text "wfstr";
  assert
    (SmtLib.translation_logic (Lib.fst binder_result) = "ALL",
     "quantified native string goal did not select conservative ALL");
  assert
    (SmtLib.translation_logic (Lib.fst qf_s_result) = "QF_S",
     "pure native string goal did not infer QF_S");
  assert
    (SmtLib.translation_logic (Lib.fst nonlinear_result) = "QF_SNIA",
     "nonlinear native string goal did not infer QF_SNIA");
  assert_has "raw num list" raw_list_text "(List_Num 0)";
  assert_lacks "raw num list" raw_list_text " String)";
  ignore (SmtLib.translation_records full_translation)
end

fun smtlib_native_string_sort_propagation_success () =
let
  fun translate_script script =
    case List.rev (parse_smtlib_assertions script) of
      conclusion :: reversed_assumptions =>
        SmtLib.goal_to_SmtLib_translation NONE
          (List.rev reversed_assumptions, conclusion)
    | [] => die "native String propagation script produced no assertions"
  fun text_of script = String.concat (Lib.snd (translate_script script))
  fun check label script snippet =
    let val text = text_of script in
      assert (contains snippet text,
        label ^ " missed SMT-LIB snippet '" ^ snippet ^ "':\n" ^ text);
      assert (not (contains "List_Num" text),
        label ^ " lost a native String sort:\n" ^ text)
    end
in
  check "String conditional propagation"
    ("(set-logic QF_SLIA)\n" ^
     "(declare-const c Bool)\n" ^
     "(assert (= 1 (str.len (ite c \"a\" \"bb\"))))\n")
    "(str.len (ite v0 \"a\" \"bb\"))";
  check "String let propagation"
    ("(set-logic QF_SLIA)\n" ^
     "(assert (= 1 (str.len (let ((x \"a\")) x))))\n")
    "(str.len (let ((b0 \"a\")) b0))";
  check "String lambda propagation"
    ("(set-logic ALL)\n" ^
     "(assert (= (lambda ((x String)) (str.++ x \"a\")) " ^
     "(lambda ((y String)) (str.++ y \"a\"))))\n")
    "(lambda ((b0 String)) (str.++ b0 \"a\"))"
end

fun smtlib_native_string_carrier_success () =
let
  val s = Term.mk_var ("typed_s", smt_string_ty)
  val t = Term.mk_var ("typed_t", smt_string_ty)
  val concat =
    Term.list_mk_comb
      (Term.prim_mk_const
        {Thy = "smtstring", Name = "smtstr_concat"},
       [s, t])
  val (_, strings) =
    SmtLib.goal_to_SmtLib_translation NONE
      ([], boolSyntax.mk_eq (concat, s))
  val text = String.concat strings
in
  assert (contains "(str.++ v0 v1)" text,
    "typed SMT String carrier did not emit str.++:\n" ^ text);
  assert (not (contains "List_Num" text) andalso
      not (contains "wfstr" text),
    "typed SMT String carrier leaked representation machinery:\n" ^ text)
end

(* P3.4 leaves this function-valued argument on the byte-identical FO route:
   nested Arrays preserve it without encountering an HO-trigger shape. *)
fun smtlib_higher_order_translation_abstraction_success () =
let
  val goal = ([], ``(H:('a -> 'b) -> bool) f``)
  val (logic, _, records, translation) = inferred_logic (Lib.snd goal)
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
  val has_ho_core_array_audit =
    List.exists
      (fn SmtLib.HOLTheoryEncoding {
            smt_theory = "HO-Core",
            mode = SmtLib.ConservativeEmbedding,
            parse = true, typecheck = true, translate = true, ...} => true
        | _ => false) records
  val has_fo_selection =
    List.exists
      (fn SmtLib.RegimeSelection {
            regime = SmtLib.FirstOrder,
            reason = "automatic:no-ho-trigger"} => true
        | _ => false) records
  val _ = SmtLib.parser_dicts_for_translation translation
in
  assert (not (SmtLib.goal_requires_ho goal),
    "function-valued FO witness unexpectedly triggered HigherOrder");
  assert (SmtLib.translation_regime translation = SmtLib.FirstOrder,
    "function-valued FO witness did not route through FirstOrder");
  assert (has_fo_selection,
    "function-valued FO witness lacked its automatic FirstOrder record");
  assert (logic = "QF_AX",
    "function-valued FO witness expected QF_AX, got " ^ logic);
  assert (has_array_sort_decl,
    "function-valued FO witness lacked nested array sort declaration");
  assert (has_h_decl,
    "function-valued FO witness lacked a declaration for H");
  assert (has_ho_core_array_audit,
    "function-valued FO witness lacked the HO-Core Array audit row")
end

fun smtlib_ho_parser_dict_currying_success () =
let
  val standard_regime = SmtLib.HigherOrder SmtLib.Standard27
  val z3_regime = SmtLib.HigherOrder SmtLib.Z3LambdaArray
  val h = ``H:(int -> int) -> bool``
  val lambda = ``\n:int. n + 1``
  val lambda_application = Term.mk_comb (h, lambda)
  val rank2 = ``smtlib_ho_rank2``
  val x = ``x:int``
  val p = ``p:bool``
  val partial = Term.mk_comb (rank2, x)
  val full = Term.mk_comb (partial, p)
  val goal = ([], boolSyntax.mk_conj
    (lambda_application, boolSyntax.mk_eq (full, ``y:int``)))
  fun translate regime =
    Lib.fst (SmtLib.goal_to_SmtLib_translation_with_regime
      regime NONE goal)
  val standard_translation = translate standard_regime
  val z3_translation = translate z3_regime
  fun generated_name translation wanted =
    case List.find
        (fn SmtLib.TermDeclaration {hol_term, ...} =>
              Term.aconv hol_term wanted
          | _ => false)
        (SmtLib.translation_records translation) of
      SOME (SmtLib.TermDeclaration {smt_name, ...}) => smt_name
    | _ => die ("FAIL: no generated declaration for " ^
        term_with_types wanted)
  fun parse_generated translation wanted args =
    let
      val (_, tm_dict) =
        SmtLib.parser_dicts_for_translation translation
      val name = generated_name translation wanted
      val parsefn = List.hd (Redblackmap.find (tm_dict, name))
    in
      parsefn name [] args
    end
  fun has_native_ho_core_audit translation =
    List.exists
      (fn SmtLib.HOLTheoryEncoding {
            smt_theory = "HO-Core", mode = SmtLib.NativeSMTLIB,
            parse = true, typecheck = true, translate = true, ...} => true
        | _ => false)
      (SmtLib.translation_records translation)
  val parsed_lambda = parse_generated standard_translation h [lambda]
  val parsed_atom = parse_generated standard_translation rank2 []
  val parsed_partial = parse_generated standard_translation rank2 [x]
  val parsed_full = parse_generated standard_translation rank2 [x, p]
  val parsed_z3_partial = parse_generated z3_translation rank2 [x]
  val (fo_translation, _) =
    SmtLib.goal_to_SmtLib_translation NONE
      ([], boolSyntax.mk_eq (full, ``y:int``))
  val parsed_fo_full = parse_generated fo_translation rank2 [x, p]
in
  assert (Term.aconv parsed_lambda lambda_application,
    "HO dictionary did not round-trip a lambda-containing application");
  assert (Term.aconv parsed_atom rank2,
    "HO dictionary did not accept a bare ranked symbol");
  assert (Term.aconv parsed_partial partial andalso
      Type.compare (Term.type_of parsed_partial, ``:bool -> int``) = EQUAL,
    "Standard27 curried entry did not build the residual application");
  assert (Term.aconv parsed_full full,
    "Standard27 curried entry did not accept the full arity");
  assert (Term.aconv parsed_z3_partial partial,
    "Z3LambdaArray curried entry did not build a residual application");
  assert (has_native_ho_core_audit standard_translation andalso
      has_native_ho_core_audit z3_translation,
    "an HO regime lacked its native HO-Core audit row");
  expect_hol_error_contains "HO dictionary over-application"
    "wrong number of arguments"
    (fn () => ignore
      (parse_generated standard_translation rank2 [x, p, ``q:bool``]));
  assert (SmtLib.translation_regime fo_translation = SmtLib.FirstOrder,
    "pinned FO dictionary translation did not select FirstOrder");
  assert (Term.aconv parsed_fo_full full,
    "pinned FO dictionary changed its exact-arity behavior");
  expect_hol_error_contains "FO dictionary partial application"
    "wrong number of arguments"
    (fn () => ignore (parse_generated fo_translation rank2 [x]))
end

fun smtlib_regime_trigger_success () =
let
  fun preprocess goal =
    Lib.fst (SolverSpec.simplify (SmtLib.SIMP_TAC true) goal)
  fun regime_record translation =
    case List.find
      (fn SmtLib.RegimeSelection _ => true | _ => false)
      (SmtLib.translation_records translation) of
      SOME (SmtLib.RegimeSelection selection) => selection
    | _ => die "FAIL: translation lacked RegimeSelection record"
  fun expect_record expected expected_reason translation =
    let
      val {regime, reason} = regime_record translation
    in
      assert (SmtLib.translation_regime translation = expected,
        "translation regime accessor disagreed with expected regime");
      assert (regime = expected,
        "RegimeSelection recorded the wrong regime");
      assert (reason = expected_reason,
        "RegimeSelection reason was '" ^ reason ^ "', expected '" ^
        expected_reason ^ "'")
    end
  fun translate_with regime goal =
    Lib.fst (SmtLib.goal_to_SmtLib_translation_with_regime regime NONE goal)
  val fo_goals = [
    ([], ``(x:int) + 7 <= y - ~3``),
    ([], ``!x:int. ?y:int. x + 2 <= y``),
    ([], ``(f:'a -> 'b) x = g y``),
    ([], ``(H:('a -> 'b) -> bool) f``),
    ([], ``option_CASE (SOME (x:int)) n s = s x``),
    preprocess ([],
      ``option_CASE (box:int option) 0 (\z. z + 1) = y``)
  ]
  val surviving =
    preprocess ([], ``(H:(int -> int) -> bool) (\x. x + 1)``)
  val complex_rator =
    ([], ``((\f:int -> int. f) g) (x:int) = y``)
  val reduced_rator = preprocess complex_rator
  val datatype_rator = preprocess ([],
    ``option_CASE (box:(int -> int) option) 0 (\f. f (x:int)) = y``)
  val function_conditional =
    ([], ``(H:(int -> int) -> bool)
      (if p then (f:int -> int) else g)``)
  val automatic_fo =
    Lib.fst (SmtLib.goal_to_SmtLib_translation NONE (List.hd fo_goals))
  val forced_fo = translate_with SmtLib.FirstOrder (List.hd fo_goals)
  val forced_standard =
    translate_with (SmtLib.HigherOrder SmtLib.Standard27)
      (List.hd fo_goals)
  val forced_z3 =
    translate_with (SmtLib.HigherOrder SmtLib.Z3LambdaArray)
      (List.hd fo_goals)
  val (surviving_regime, surviving_reason) =
    SmtLib.regime_for_goal SmtLib.Standard27 surviving
  val (datatype_regime, datatype_reason) =
    SmtLib.regime_for_goal SmtLib.Z3LambdaArray datatype_rator
  val (function_conditional_regime, function_conditional_reason) =
    SmtLib.regime_for_goal SmtLib.Z3LambdaArray function_conditional
  val automatic_surviving = Lib.fst
    (SmtLib.goal_to_SmtLib_translation NONE surviving)
  val automatic_complex = Lib.fst
    (SmtLib.goal_to_SmtLib_translation NONE complex_rator)
  val automatic_datatype = Lib.fst
    (SmtLib.goal_to_SmtLib_translation NONE datatype_rator)
in
  List.app
    (fn goal => assert (not (SmtLib.goal_requires_ho goal),
      "first-order trigger-table goal selected HigherOrder"))
    fo_goals;
  assert (SmtLib.goal_requires_ho surviving,
    "surviving first-class lambda did not select HigherOrder");
  assert (SmtLib.goal_requires_ho complex_rator,
    "non-constant/non-variable rator did not select HigherOrder");
  assert (not (SmtLib.goal_requires_ho reduced_rator),
    "preprocessing-reduced rator did not return to FirstOrder");
  assert (SmtLib.goal_requires_ho datatype_rator,
    "datatype branch normalization missed a complex rator");
  assert (SmtLib.goal_requires_ho function_conditional,
    "function-valued conditional did not select HigherOrder");
  assert (function_conditional_regime =
      SmtLib.HigherOrder SmtLib.Z3LambdaArray andalso
      function_conditional_reason =
        "automatic:function-valued-conditional",
    "function-valued conditional lost its automatic regime reason");
  assert (surviving_regime =
      SmtLib.HigherOrder SmtLib.Standard27 andalso
      surviving_reason = "automatic:surviving-abstraction",
    "Standard27 automatic selection lost the surviving-lambda reason");
  assert (datatype_regime =
      SmtLib.HigherOrder SmtLib.Z3LambdaArray andalso
      datatype_reason =
        "automatic:non-constant/non-variable-rator",
    "Z3 automatic selection lost the normalized-rator reason");
  expect_record (SmtLib.HigherOrder SmtLib.Standard27)
    "automatic:surviving-abstraction" automatic_surviving;
  expect_record (SmtLib.HigherOrder SmtLib.Standard27)
    "automatic:non-constant/non-variable-rator" automatic_complex;
  expect_record (SmtLib.HigherOrder SmtLib.Standard27)
    "automatic:non-constant/non-variable-rator" automatic_datatype;
  expect_hol_error_contains "forced FirstOrder surviving lambda"
    "unsupported higher-order rator expression"
    (fn () => ignore
      (SmtLib.goal_to_SmtLib_translation_with_regime
        SmtLib.FirstOrder NONE surviving));
  expect_record SmtLib.FirstOrder "automatic:no-ho-trigger" automatic_fo;
  expect_record SmtLib.FirstOrder "explicit override" forced_fo;
  expect_record (SmtLib.HigherOrder SmtLib.Standard27)
    "explicit override" forced_standard;
  expect_record (SmtLib.HigherOrder SmtLib.Z3LambdaArray)
    "explicit override" forced_z3
end

fun smtlib_driver_regime_selection_success () =
let
  val goal = ([], ``(H:(int -> int) -> bool) (\x. x + 1)``)
  fun selection translation =
    case List.find
      (fn SmtLib.RegimeSelection _ => true | _ => false)
      (SmtLib.translation_records translation) of
      SOME (SmtLib.RegimeSelection selected) => selected
    | _ => die "FAIL: driver-shaped translation lacked RegimeSelection"
  fun expect label expected translation =
    let
      val {regime, reason} = selection translation
    in
      assert (SmtLib.translation_regime translation = expected,
        label ^ " translation accessor recorded the wrong regime");
      assert (regime = expected,
        label ^ " RegimeSelection recorded the wrong regime");
      assert (reason = "automatic:surviving-abstraction",
        label ^ " RegimeSelection recorded reason '" ^ reason ^ "'")
    end
  val z3_plain = Lib.fst
    (Z3.goal_to_SmtLib_translation_for_version (SOME "4.15.3") goal)
  val z3_proof = Lib.fst
    (Z3.goal_to_SmtLib_with_get_proof_translation_for_version
      (SOME "4.15.3") goal)
  val cvc_plain = Lib.fst (CVC.goal_to_SmtLib_translation goal)
  val cvc_proof = Lib.fst
    (CVC.goal_to_SmtLib_with_get_proof_translation goal)
in
  expect "Z3 oracle driver" (SmtLib.HigherOrder SmtLib.Z3LambdaArray)
    z3_plain;
  expect "Z3 proof driver" (SmtLib.HigherOrder SmtLib.Z3LambdaArray)
    z3_proof;
  expect "cvc5 oracle driver" (SmtLib.HigherOrder SmtLib.Standard27)
    cvc_plain;
  expect "cvc5 proof driver" (SmtLib.HigherOrder SmtLib.Standard27)
    cvc_proof
end

fun smtlib_standard27_translation_success () =
let
  val standard_regime = SmtLib.HigherOrder SmtLib.Standard27
  fun translate goal =
    SmtLib.goal_to_SmtLib_translation_with_regime
      standard_regime NONE goal
  fun translate_apply operator goal =
    SmtLib.goal_to_SmtLib_translation_with_regime_and_apply_operator
      standard_regime operator NONE goal
  fun text_of result = String.concat (Lib.snd result)
  fun assert_has name text snippet =
    assert (contains snippet text,
      name ^ " missed SMT-LIB snippet '" ^ snippet ^
      "'\nSMT-LIB:\n" ^ text)
  fun assert_lacks name text snippet =
    assert (not (contains snippet text),
      name ^ " unexpectedly emitted SMT-LIB snippet '" ^ snippet ^
      "'\nSMT-LIB:\n" ^ text)
  fun logic_selection_of translation =
    case List.find
      (fn SmtLib.LogicSelection _ => true | _ => false)
      (SmtLib.translation_records translation) of
      SOME (SmtLib.LogicSelection selection) => selection
    | _ => die "FAIL: translation lacked LogicSelection features"
  fun features_of translation = #features (logic_selection_of translation)
  fun reason_of translation = #reason (logic_selection_of translation)
  fun feature_vector {quantifiers, uninterpreted, arrays, bitvectors,
      integers, reals, strings, datatypes, nonlinear} =
    SmtLib.LogicFeatures {
      quantifiers = quantifiers, uninterpreted = uninterpreted,
      arrays = arrays, bitvectors = bitvectors, integers = integers,
      reals = reals, strings = strings, datatypes = datatypes,
      nonlinear = nonlinear, higher_order = true}
  fun expect_ho_logic expected name fields =
    let
      val (logic, _) = SmtLib.infer_logic_from_features_with_regime
        standard_regime (feature_vector fields)
    in
      assert (logic = expected,
        "Standard27 logic inference '" ^ name ^ "' expected " ^ expected ^
        ", got " ^ logic)
    end
  val arrow_result = translate
    ([], ``(ff:int -> bool -> int) = gg``)
  val arrow_translation = Lib.fst arrow_result
  val arrow_text = text_of arrow_result
  val pure_ho_translation = Lib.fst (translate
    ([], ``(puref:'a -> 'b -> 'c) = pureg``))
  val symbol_text = text_of (translate
    ([], ``(u:int -> bool -> int) x p = y``))
  val ranked_result = translate
    ([], ``smtlib_ho_rank2 (x:int) = (f:bool -> int) /\
           smtlib_ho_rank2 x p = y``)
  val ranked_translation = Lib.fst ranked_result
  val ranked_text = text_of ranked_result
  val builtin_eta_text = text_of (translate
    ([], ``(H:(int -> int) -> bool) ($+ 1) ==>
           H (\x. 1 + x)``))
  val constructor_eta_text = text_of (translate
    ([], ``(H:(int -> smt_tri) -> bool) SmtTriB ==>
           H (\x. SmtTriB x)``))
  val lambda_text = text_of (translate
    ([], ``(H:((int -> int) -> int -> int) -> bool)
      (\f x. f x)``))
  val complex_goal =
    ([], ``((\f:int -> int. f) g) (x:int) = y``)
  val underscore_text = text_of
    (translate_apply SmtLib.ApplyUnderscore complex_goal)
  val at_text = text_of (translate_apply SmtLib.ApplyAt complex_goal)
  val update_array = ``updatef:int -> int``
  val update_index = ``update_i:int``
  val update_value = ``update_x:int``
  val update_query = ``update_j:int``
  val updated = Term.mk_comb
    (combinSyntax.mk_update (update_index, update_value), update_array)
  val update_result = translate
    ([], boolSyntax.mk_eq (Term.mk_comb (updated, update_query),
      ``update_y:int``))
  val update_translation = Lib.fst update_result
  val update_text = text_of update_result
  val feature_goal = ([], ``(mapf:'a -> 'b) x = mapf x``)
  val fo_translation = Lib.fst
    (SmtLib.goal_to_SmtLib_translation_with_regime
      SmtLib.FirstOrder NONE feature_goal)
  val ho_translation = Lib.fst (translate feature_goal)
  val z3_translation = Lib.fst
    (SmtLib.goal_to_SmtLib_translation_with_regime
      (SmtLib.HigherOrder SmtLib.Z3LambdaArray) NONE feature_goal)
  val SmtLib.LogicFeatures {
    arrays = fo_arrays, higher_order = fo_higher_order, ...} =
    features_of fo_translation
  val SmtLib.LogicFeatures {
    arrays = ho_arrays, higher_order = ho_higher_order, ...} =
    features_of ho_translation
  val SmtLib.LogicFeatures {
    arrays = update_arrays, higher_order = update_higher_order, ...} =
    features_of update_translation
  val rank2_declarations =
    List.filter
      (fn SmtLib.TermDeclaration {hol_term, ...} =>
            Term.is_const hol_term andalso
            Term.same_const hol_term ``smtlib_ho_rank2``
        | _ => false)
      (SmtLib.translation_records ranked_translation)
in
  assert (SmtLib.translation_logic arrow_translation = "HO_ALL",
    "uncurated Standard27 integer stem did not fall back to HO_ALL");
  assert (SmtLib.translation_logic pure_ho_translation = "HO_QF_UF",
    "Standard27 pure HO goal did not select HO_QF_UF");
  assert (contains "higher-order" (reason_of arrow_translation),
    "higher-order feature was absent from the logic-selection reason");
  assert_has "curried arrow declaration" arrow_text
    "(declare-const v0 (-> Int Bool Int))";
  assert_lacks "curried arrow declaration" arrow_text "(Array ";
  assert_has "symbol omission sugar" symbol_text "(v0 v1 v2)";
  assert_lacks "symbol omission sugar" symbol_text "(select ";
  assert_lacks "symbol omission sugar" symbol_text "(@ ";
  assert_has "ranked true-type declaration" ranked_text
    "(declare-fun v0 (Int Bool) Int)";
  assert_has "ranked partial omission sugar" ranked_text "(v0 v1)";
  assert_has "ranked full omission sugar" ranked_text "(v0 v1 v3)";
  assert (List.length rank2_declarations = 1,
    "Standard27 split one ranked symbol into multiple declarations");
  assert_has "built-in eta expansion" builtin_eta_text
    "(lambda ((b0 Int)) (+ 1 b0))";
  assert_lacks "built-in eta expansion" builtin_eta_text
    "(declare-fun v1 (Int Int) Int)";
  assert_lacks "built-in eta expansion" builtin_eta_text
    "(lambda ((b0 Int)) (lambda";
  assert_has "constructor eta expansion" constructor_eta_text
    "(lambda ((b0 Int)) (ctor_Smt_tri_SmtTriB b0))";
  assert_lacks "constructor eta expansion" constructor_eta_text
    "(declare-fun v1 (Int) Smt_tri)";
  assert_has "native lambda" lambda_text
    "(lambda ((b0 (-> Int Int))) (lambda ((b1 Int)) (b0 b1)))";
  assert_lacks "native lambda" lambda_text "(select ";
  assert_has "standard explicit apply" underscore_text
    "(_ (_ (lambda ((b0 (-> Int Int))) b0) v0) v1)";
  assert_lacks "standard explicit apply" underscore_text "(@ ";
  assert_has "cvc5 explicit apply" at_text
    "(@ (@ (lambda ((b0 (-> Int Int))) b0) v0) v1)";
  assert_lacks "cvc5 explicit apply" at_text "(_ (";
  assert_has "native map update" update_text
    "(_ (lambda ((b0 Int)) (ite (= b0 v1) v2 (v0 b0))) v3)";
  assert_lacks "native map update" update_text "(store ";
  assert (update_arrays andalso update_higher_order,
    "Standard27 UPDATE did not retain the arrays feature");
  assert (fo_arrays andalso not fo_higher_order,
    "FO function variable lost its arrays-only feature classification");
  assert (not ho_arrays andalso ho_higher_order,
    "HO function variable retained the FO arrays coupling");
  assert (SmtLib.translation_logic z3_translation = "ALL",
    "Z3LambdaArray set-logic choice changed from TASK_11");
  List.app (fn (expected, name, fields) =>
      expect_ho_logic expected name fields) [
    ("HO_QF_UF", "core",
      {quantifiers = false, uninterpreted = false, arrays = false,
       bitvectors = false, integers = false, reals = false,
       strings = false, datatypes = false, nonlinear = false}),
    ("HO_UF", "quantified core",
      {quantifiers = true, uninterpreted = false, arrays = false,
       bitvectors = false, integers = false, reals = false,
       strings = false, datatypes = false, nonlinear = false}),
    ("HO_QF_UFLIA", "curated integer UF",
      {quantifiers = false, uninterpreted = true, arrays = false,
       bitvectors = false, integers = true, reals = false,
       strings = false, datatypes = false, nonlinear = false}),
    ("HO_UFLIA", "quantified integer UF",
      {quantifiers = true, uninterpreted = true, arrays = false,
       bitvectors = false, integers = true, reals = false,
       strings = false, datatypes = false, nonlinear = false}),
    ("HO_QF_UFLRA", "curated real UF",
      {quantifiers = false, uninterpreted = true, arrays = false,
       bitvectors = false, integers = false, reals = true,
       strings = false, datatypes = false, nonlinear = false}),
    ("HO_UFLRA", "quantified real UF",
      {quantifiers = true, uninterpreted = true, arrays = false,
       bitvectors = false, integers = false, reals = true,
       strings = false, datatypes = false, nonlinear = false}),
    ("HO_QF_AUFLIA", "curated array integer",
      {quantifiers = false, uninterpreted = false, arrays = true,
       bitvectors = false, integers = true, reals = false,
       strings = false, datatypes = false, nonlinear = false}),
    ("HO_AUFLIA", "quantified array integer UF",
      {quantifiers = true, uninterpreted = true, arrays = true,
       bitvectors = false, integers = true, reals = false,
       strings = false, datatypes = false, nonlinear = false}),
    ("HO_AUFLIRA", "quantified array mixed arithmetic UF",
      {quantifiers = true, uninterpreted = true, arrays = true,
       bitvectors = false, integers = true, reals = true,
       strings = false, datatypes = false, nonlinear = false}),
    ("HO_ALL", "uncurated integer",
      {quantifiers = false, uninterpreted = false, arrays = false,
       bitvectors = false, integers = true, reals = false,
       strings = false, datatypes = false, nonlinear = false})
  ]
end

fun smtlib_z3_lambda_array_translation_success () =
let
  val z3_regime = SmtLib.HigherOrder SmtLib.Z3LambdaArray
  fun translate goal =
    SmtLib.goal_to_SmtLib_translation_with_regime z3_regime NONE goal
  fun translate_automatic goal =
    SmtLib.goal_to_SmtLib_translation_with_dialect
      SmtLib.Z3LambdaArray NONE goal
  fun text_of result = String.concat (Lib.snd result)
  fun assert_has name text snippet =
    assert (contains snippet text,
      name ^ " missed SMT-LIB snippet '" ^ snippet ^
      "'\nSMT-LIB:\n" ^ text)
  fun assert_lacks name text snippet =
    assert (not (contains snippet text),
      name ^ " unexpectedly emitted SMT-LIB snippet '" ^ snippet ^
      "'\nSMT-LIB:\n" ^ text)
  val lambda_result = translate_automatic
    ([], ``(H:(int -> int) -> bool) (\x. x + 1)``)
  val lambda_translation = Lib.fst lambda_result
  val lambda_text = text_of lambda_result
  val arrows_text = text_of (translate
    ([], ``(ff:int -> bool -> int) = gg``))
  val eta_result = translate
    ([], ``smtlib_ho_rank2 (x:int) = (f:bool -> int) /\
           smtlib_ho_rank2 x p = y``)
  val eta_translation = Lib.fst eta_result
  val eta_text = text_of eta_result
  val rank2_declarations =
    List.filter
      (fn SmtLib.TermDeclaration {hol_term, ...} =>
            Term.is_const hol_term andalso
            Term.same_const hol_term ``smtlib_ho_rank2``
        | _ => false)
      (SmtLib.translation_records eta_translation)
  val selects_text = text_of (translate
    ([], ``(u:int -> int -> int) x y = z``))
  val ite_result = translate_automatic
    ([], ``(if p then (f:int -> int) else g) x = y``)
  val ite_translation = Lib.fst ite_result
  val ite_text = text_of ite_result
  val conditional_value_result = translate_automatic
    ([], ``(H:(int -> int) -> bool)
      (if p then (f:int -> int) else g)``)
  val conditional_value_translation = Lib.fst conditional_value_result
  val conditional_value_text = text_of conditional_value_result
  val selector_text = text_of (translate
    ([], ``((r:smt_fun_rec).smt_fun) x p = y``))
  val complex_result = translate_automatic
    ([], ``((\f:int -> int. f) g) (x:int) = y``)
  val complex_translation = Lib.fst complex_result
  val complex_text = text_of complex_result
in
  assert (SmtLib.translation_regime lambda_translation = z3_regime,
    "automatic lambda translation selected the wrong dialect");
  assert_has "lambda lowering" lambda_text "(set-logic ALL)\n";
  assert_has "lambda lowering" lambda_text
    "(declare-fun v0 () (Array (Array Int Int) Bool))";
  assert_has "lambda lowering" lambda_text
    "(select v0 (lambda ((b0 Int)) (+ b0 1)))";
  assert_has "nested arrow lowering" arrows_text
    "(Array Int (Array Bool Int))";
  assert_lacks "nested arrow lowering" arrows_text "(-> ";
  assert_has "ranked eta expansion" eta_text
    "(declare-fun v0 (Int Bool) Int)";
  assert_has "ranked eta expansion" eta_text
    "(lambda ((b0 Bool)) (v0 v1 b0))";
  assert_has "ranked eta expansion" eta_text "(v0 v1 v3)";
  assert_lacks "ranked eta expansion" eta_text
    "(declare-fun v0 (Int) (Array Bool Int))";
  assert (List.length rank2_declarations = 1,
    "partial and full ranked applications did not share one declaration");
  (case List.hd rank2_declarations of
     SmtLib.TermDeclaration {arity, ...} =>
       assert (arity = 2, "ranked constant was not declared at full rank")
   | _ => raise Fail "impossible non-declaration record");
  assert_has "nested select application" selects_text
    "(select (select v0 v1) v2)";
  assert_lacks "nested select application" selects_text
    "(select v0 v1 v2)";
  assert (SmtLib.translation_regime ite_translation = z3_regime,
    "applied function-valued conditional selected the wrong dialect");
  assert_has "function-valued builtin application" ite_text
    "(select (ite v0 v1 v2) v3)";
  assert_lacks "function-valued builtin application" ite_text
    "(ite v0 v1 v2 v3)";
  assert (SmtLib.translation_regime conditional_value_translation =
      z3_regime,
    "automatic function-valued built-in selected the wrong dialect");
  assert_has "automatic function-valued built-in" conditional_value_text
    "(select v0 (ite v1 v2 v3))";
  assert_has "function-valued record selector" selector_text
    "(select (select (recordtype_smt_fun_rec_seldef_smt_fun v1) v2) v3)";
  assert_lacks "function-valued record selector" selector_text
    "(declare-fun v0 (Smt_fun_rec Int Bool) Int)";
  assert (SmtLib.translation_regime complex_translation = z3_regime,
    "automatic complex-rator translation selected the wrong dialect");
  assert_has "complex-rator application" complex_text
    "(select (select (lambda ((b0 (Array Int Int))) b0) v0) v1)"
end

(* D10 enforcement: the P3.4 regime trigger leaves every one of these
   first-order translations byte-identical.  In particular, the final case
   is the abstraction witness that must continue to take the FO route. *)
fun smtlib_fo_emission_golden_success () =
let
  fun prelude logic = [
    "(set-logic " ^ logic ^ ")\n",
    "(set-info :source |Automatically generated from HOL4 by " ^
      "SmtLib.goal_to_SmtLib.\n",
    "Copyright (c) 2011 Tjark Weber. All rights reserved.|)\n",
    "(set-info :smt-lib-version 2.7)\n"
  ]
  fun first_byte_difference expected actual =
    let
      val expected_size = String.size expected
      val actual_size = String.size actual
      val common_size = Int.min (expected_size, actual_size)
      fun find n =
        if n = common_size then
          if expected_size = actual_size then NONE else SOME n
        else if String.sub (expected, n) = String.sub (actual, n) then
          find (n + 1)
        else
          SOME n
    in
      find 0
    end
  fun line_number text position =
    let
      val stop = Int.min (position, String.size text)
      fun count (n, lines) =
        if n = stop then lines
        else count (n + 1,
          if String.sub (text, n) = #"\n" then lines + 1 else lines)
    in
      count (0, 1)
    end
  fun line_at text position =
    if position >= String.size text then
      "<end of benchmark>"
    else
      let
        fun start n =
          if n = 0 orelse String.sub (text, n - 1) = #"\n" then n
          else start (n - 1)
        fun finish n =
          if n = String.size text then n
          else if String.sub (text, n) = #"\n" then n + 1
          else finish (n + 1)
        val first = start position
      in
        "\"" ^ String.toString
          (String.substring (text, first, finish position - first)) ^ "\""
      end
  fun first_list_difference expected actual =
    let
      fun find (_, _, [], []) = NONE
        | find (n, position, expected :: expected_rest,
            actual :: actual_rest) =
          if expected = actual then
            find (n + 1, position + String.size expected,
              expected_rest, actual_rest)
          else
            SOME (n, position, SOME expected, SOME actual)
        | find (n, position, expected :: _, []) =
            SOME (n, position, SOME expected, NONE)
        | find (n, position, [], actual :: _) =
            SOME (n, position, NONE, SOME actual)
      fun render NONE = "<end of string list>"
        | render (SOME text) = "\"" ^ String.toString text ^ "\""
    in
      case find (1, 0, expected, actual) of
        NONE => NONE
      | SOME (element, position, expected, actual) =>
          SOME (element, position, render expected, render actual)
    end
  fun assert_golden goal_name variant expected actual =
    if expected = actual then
      ()
    else
      let
        val expected_text = String.concat expected
        val actual_text = String.concat actual
        fun prefix line =
          "FAIL: FO emission golden '" ^ goal_name ^ "' (" ^ variant ^
          ") first diverging line " ^ Int.toString line
      in
        case first_byte_difference expected_text actual_text of
          SOME position =>
            die (prefix (line_number expected_text position) ^
              "\nexpected: " ^ line_at expected_text position ^
              "\nactual:   " ^ line_at actual_text position)
        | NONE =>
            case first_list_difference expected actual of
              SOME (element, position, expected, actual) =>
                die (prefix (line_number expected_text position) ^
                  " (string-list boundary differs at element " ^
                  Int.toString element ^ ")\nexpected element: " ^ expected ^
                  "\nactual element:   " ^ actual)
            | NONE =>
                raise Fail "unequal golden lists unexpectedly compare equal"
      end
  fun check {name, goal, body} =
    let
      val expected = body @ ["(exit)\n"]
      val expected_with_proof =
        body @ ["(get-proof)\n", "(exit)\n"]
      val (translation, actual) =
        SmtLib.goal_to_SmtLib_translation NONE goal
      val (proof_translation, actual_with_proof) =
        SmtLib.goal_to_SmtLib_with_get_proof_translation NONE goal
      fun recorded_first_order tr =
        SmtLib.translation_regime tr = SmtLib.FirstOrder andalso
        List.exists
          (fn SmtLib.RegimeSelection {regime = SmtLib.FirstOrder, ...} =>
                true
            | _ => false)
          (SmtLib.translation_records tr)
    in
      assert (not (SmtLib.goal_requires_ho goal),
        "FO golden '" ^ name ^ "' triggered HigherOrder");
      assert (recorded_first_order translation andalso
          recorded_first_order proof_translation,
        "FO golden '" ^ name ^ "' lacked FirstOrder regime records");
      assert_golden name "goal_to_SmtLib" expected actual;
      assert_golden name "goal_to_SmtLib_with_get_proof"
        expected_with_proof actual_with_proof
    end
  val array = ``a:int -> int``
  val other_array = ``b:int -> int``
  val index = ``i:int``
  val value = ``x:int``
  val updated =
    Term.mk_comb (combinSyntax.mk_update (index, value), array)
  val array_goal : term list * term =
    ([], boolSyntax.mk_conj
      (boolSyntax.mk_eq (Term.mk_comb (array, index), value),
       boolSyntax.mk_eq (updated, other_array)))
  val cases = [
    {name = "qf-integer-linear",
     goal = ([], ``(x:int) + 7 <= y - ~3``),
     body = prelude "QF_LIA" @ [
       "(declare-fun v0 () Int)\n",
       "(declare-fun v1 () Int)\n",
       "(assert (not (<= (+ v0 7) (- v1 (- 3)))))\n",
       "(check-sat)\n"]},
    {name = "quantified-integer-linear",
     goal = ([], ``!x:int. ?y:int. x + 2 <= y``),
     body = prelude "LIA" @ [
       "(assert (not (forall ((b0 Int)) (exists ((b1 Int)) " ^
         "(<= (+ b0 2) b1)))))\n",
       "(check-sat)\n"]},
    {name = "qf-real-linear",
     goal = ([], ``(x:real) + 7r <= y + 2r``),
     body = prelude "QF_LRA" @ [
       "(declare-fun v0 () Real)\n",
       "(declare-fun v1 () Real)\n",
       "(assert (not (<= (+ v0 7.0) (+ v1 2.0))))\n",
       "(check-sat)\n"]},
    {name = "quantified-real-linear",
     goal = ([], ``!x:real. ?y:real. x + 2r <= y``),
     body = prelude "LRA" @ [
       "(assert (not (forall ((b0 Real)) (exists ((b1 Real)) " ^
         "(<= (+ b0 2.0) b1)))))\n",
       "(check-sat)\n"]},
    {name = "bit-vectors",
     goal = ([], ``((x:word8) && 3w) = (y || 1w)``),
     body = prelude "QF_BV" @ [
       "(declare-fun v0 () (_ BitVec 8))\n",
       "(declare-fun v1 () (_ BitVec 8))\n",
       "(assert (not (= (bvand v0 (_ bv3 8)) " ^
         "(bvor v1 (_ bv1 8)))))\n",
       "(check-sat)\n"]},
    {name = "native-string-concat",
     goal = ([],
       ``smtstring$smtstr_concat
           (smtstring$str_inj s) (smtstring$str_inj t) =
         smtstring$smtstr_concat
           (smtstring$str_inj t) (smtstring$str_inj s)``),
     body = prelude "QF_S" @ [
       "(declare-fun v0 () String)\n",
       "(declare-fun v1 () String)\n",
       "(assert (not (= (str.++ v0 v1) (str.++ v1 v0))))\n",
       "(check-sat)\n"]},
    {name = "native-string-prefix",
     goal = ([],
       ``smtstring$smtstr_prefixof
           (smtstring$str_inj s) (smtstring$str_inj t)``),
     body = prelude "QF_S" @ [
       "(declare-fun v0 () String)\n",
       "(declare-fun v1 () String)\n",
       "(assert (not (str.prefixof v0 v1)))\n",
       "(check-sat)\n"]},
    {name = "native-string-less",
     goal = ([],
       ``smtstring$smtstr_lt (smtstring$str_inj s) (smtstring$str_inj t)``),
     body = prelude "QF_S" @ [
       "(declare-fun v0 () String)\n",
       "(declare-fun v1 () String)\n",
       "(assert (not (str.< v0 v1)))\n",
       "(check-sat)\n"]},
    {name = "native-string-less-equal",
     goal = ([],
       ``smtstring$smtstr_le (smtstring$str_inj s) (smtstring$str_inj t)``),
     body = prelude "QF_S" @ [
       "(declare-fun v0 () String)\n",
       "(declare-fun v1 () String)\n",
       "(assert (not (str.<= v0 v1)))\n",
       "(check-sat)\n"]},
    {name = "arrays-select-store-equality",
     goal = array_goal,
     body = prelude "QF_AUFLIA" @ [
       "(declare-fun v0 () (Array Int Int))\n",
       "(declare-fun v1 () Int)\n",
       "(declare-fun v2 () Int)\n",
       "(declare-fun v3 () (Array Int Int))\n",
       "(assert (not (and (= (select v0 v1) v2) " ^
         "(= (store v0 v1 v2) v3))))\n",
       "(check-sat)\n"]},
    {name = "function-variable-arrays",
     goal = ([], ``(f:'a -> 'b) x = g y``),
     body = prelude "QF_AX" @ [
       "(declare-sort t0 0)\n",
       "(declare-sort t1 0)\n",
       "(declare-fun v0 () (Array t0 t1))\n",
       "(declare-fun v1 () t0)\n",
       "(declare-sort t2 0)\n",
       "(declare-fun v2 () (Array t2 t1))\n",
       "(declare-fun v3 () t2)\n",
       "(assert (not (= (select v0 v1) (select v2 v3))))\n",
       "(check-sat)\n"]},
    {name = "fo-abstraction-witness",
     goal = ([], ``(H:('a -> 'b) -> bool) f``),
     body = prelude "QF_AX" @ [
       "(declare-sort t0 0)\n",
       "(declare-sort t1 0)\n",
       "(declare-fun v0 () (Array (Array t0 t1) Bool))\n",
       "(declare-fun v1 () (Array t0 t1))\n",
       "(assert (not (select v0 v1)))\n",
       "(check-sat)\n"]}
  ]
in
  List.app check cases
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
       ``smtstring$smtstr_concat
           (smtstring$str_inj s) (smtstring$str_inj t) =
         smtstring$smtstr_concat
           (smtstring$str_inj t) (smtstring$str_inj s)``),
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
       ``smtstring$smtstr_prefixof (smtstring$str_inj s)
           (smtstring$smtstr_concat
              (smtstring$str_inj s) (smtstring$str_inj t)) /\
         smtstring$smtstr_lt (smtstring$str_inj s) (smtstring$str_inj t) /\
         smtstring$smtstr_le (smtstring$str_inj s) (smtstring$str_inj t)``),
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

fun cpc_string_registry_and_literal_parser_success () =
let
  val proof = parse_cpc_proof_string
    "((step @p1 (= \"\" \"\") :rule refl :args (\"\")))"
  val theorem = CPC_ProofReplay.replay_root_for_test proof
  val concat_proof = parse_cpc_proof_string
    "((assume @p1 (= (str.++ \"a\") \"a\")))"
  val proof_rules =
    ["str", "string_eager_reduction", "string_length_pos",
     "string_reduction"]
  val rare_rules =
    ["re-all-elim", "re-concat-merge", "re-diff-elim",
     "re-in-comp", "re-in-cstring", "re-inter-cstring",
     "re-loop-elim", "re-opt-elim", "re-plus-elim",
     "re-repeat-elim", "str-concat-clash-rev",
     "str-concat-unify-rev", "str-contains-concat-find",
     "str-in-re-eval", "str-in-re-range-elim",
     "str-in-re-union-elim", "str-is-digit-elim",
     "str-len-concat-rec", "str-lt-elim",
     "str-replace-re-all-eval", "str-replace-re-eval",
     "str-substr-empty-range", "str-substr-empty-str",
     "str-substr-eq-empty"]
  fun check namespace handler name =
    case CPC_Proof.lookup_rule "1.3.4" name of
      SOME rule =>
        assert (#namespace rule = namespace andalso
                #replay_handler rule = handler,
          "CPC string registry metadata is wrong for " ^ name)
    | NONE => die ("FAIL: CPC string registry omitted " ^ name)
  fun check_rare name =
    check CPC_Proof.RareRewrite
      (if name = "str-is-digit-elim" orelse name = "str-lt-elim" then
         "rewrite"
       else
         "string")
      name
in
  assert (Thm.concl theorem ~~
      ``smtstring$SmtStr [] = smtstring$SmtStr []``,
    "CPC empty string literal was not preserved");
  (case CPC_Proof.proof_commands concat_proof of
     [CPC_Proof.ASSUME (_, equality)] =>
       assert (boolSyntax.lhs equality ~~ boolSyntax.rhs equality,
         "CPC unary str.++ annotation did not preserve its payload")
   | _ => die "FAIL: CPC unary str.++ annotation did not parse");
  List.app (check CPC_Proof.ProofRule "string") proof_rules;
  List.app check_rare rare_rules;
  Library.check_oracle_tags "CPC string literal parser" theorem
end

fun cpc_proof_replay_string_rules_success () =
let
  val lt_proof = parse_cpc_proof_string
      "((step @p1 \
      \(= (str.< \"a\" \"b\") \
      \(and (not (= \"a\" \"b\")) (str.<= \"a\" \"b\"))) \
      \:rule str-lt-elim :args (\"a\" \"b\")))"
  val digit_proof = parse_cpc_proof_string
      "((step @p1 \
      \(= (str.is_digit \"7\") \
      \(and (<= 48 (str.to_code \"7\")) \
      \     (<= (str.to_code \"7\") 57))) \
      \:rule str-is-digit-elim :args (\"7\")))"
  val lt = CPC_ProofReplay.replay_root_for_test lt_proof
  val digit = CPC_ProofReplay.replay_root_for_test digit_proof
  val lt_omitted = CPC_ProofReplay.replay_root_for_test
    (parse_cpc_proof_string
      "((step @p1 :rule str-lt-elim :args (\"a\" \"b\")))")
  val digit_omitted = CPC_ProofReplay.replay_root_for_test
    (parse_cpc_proof_string
      "((step @p1 :rule str-is-digit-elim :args (\"7\")))")
  fun explicit_conclusion proof =
    case CPC_Proof.proof_commands proof of
      [CPC_Proof.STEP {conclusion = SOME target, ...}] => target
    | _ => die "FAIL: CPC string test lost its explicit conclusion"
in
  assert (Thm.concl lt ~~ explicit_conclusion lt_proof,
    "CPC str-lt-elim replay returned the wrong equality");
  assert (Thm.concl digit ~~ explicit_conclusion digit_proof,
    "CPC str-is-digit-elim replay returned the wrong equality");
  assert (Thm.concl lt_omitted ~~ Thm.concl lt,
    "CPC str-lt-elim omitted-conclusion reconstruction disagrees");
  assert (Thm.concl digit_omitted ~~ Thm.concl digit,
    "CPC str-is-digit-elim omitted-conclusion reconstruction disagrees");
  List.app (Library.check_oracle_tags "CPC string RARE rewrite")
    [lt, digit, lt_omitted, digit_omitted]
end

fun cpc_proof_replay_string_obligation_diagnostic () =
  expect_hol_error_contains "CPC re-all-elim obligation"
    "rule=re-all-elim"
    (fn () => ignore (CPC_ProofReplay.replay_root_for_test
      (parse_cpc_proof_string
        "((step @p1 (= re.all (re.* re.allchar)) \
        \:rule re-all-elim))")))

(* A CPC string step whose premise is an earlier derived lemma must not leak
   that lemma's conclusion as a hypothesis: the contextual rung feeds it to
   ASM_SIMP_TAC and has to discharge it against the premise again. *)
fun cpc_proof_replay_string_premise_hypotheses () =
let
  val proof = parse_cpc_proof_string
      "((declare-const s String) (declare-const t String) \
      \(declare-const u String) \
      \(assume @p1 (= s t)) (assume @p2 (= t u)) \
      \(step @p3 (= s u) :rule trans :premises (@p1 @p2)) \
      \(step @p4 (= (str.len s) (str.len u)) \
      \:rule string_reduction :premises (@p3)))"
  val theorem = CPC_ProofReplay.replay_root_for_test proof
  val assumed =
    List.foldl
      (fn (command, accumulated) =>
        case command of
          CPC_Proof.ASSUME (_, tm) => HOLset.add (accumulated, tm)
        | _ => accumulated)
      Term.empty_tmset (CPC_Proof.proof_commands proof)
  val leaked = HOLset.difference (Thm.hypset theorem, assumed)
in
  assert (HOLset.numItems assumed = 2,
    "CPC string premise test lost its assumptions");
  assert (HOLset.isEmpty leaked,
    "CPC string step leaked premise conclusions as hypotheses: " ^
    String.concatWith ", "
      (List.map Library.term_to_string (HOLset.listItems leaked)));
  Library.check_oracle_tags "CPC string contextual premise unit test" theorem
end

(* Captured cvc5 1.3.4 CPC spelling: binders may be inline @var terms and
   partial application is printed with CPC's `_` application constructor. *)
fun cpc_proof_parser_lambda_inline_var_apply_success () =
let
  val proof = parse_cpc_proof_string
    "((declare-const cpc_fun (-> Int Bool Int)) \
    \(declare-const cpc_arg Int) \
    \(define @t1 () (@var \"b0\" Bool)) \
    \(define @t2 () (lambda (@list (@var \"b0\" Bool)) \
    \ (cpc_fun cpc_arg @t1))) \
    \(define @t3 () (_ cpc_fun cpc_arg)) \
    \(assume @p1 (= @t2 @t3)))"
in
  case CPC_Proof.proof_commands proof of
    [CPC_Proof.ASSUME (_, equality)] =>
      let val (lambda, partial) = boolSyntax.dest_eq equality in
        assert (Term.is_abs lambda,
          "CPC lambda definition did not preserve a HOL abstraction");
        assert (Term.type_of partial =
            boolSyntax.list_mk_fun ([Type.bool], intSyntax.int_ty),
          "CPC `_` application did not preserve the residual function type");
        assert (Term.aconv
            (boolSyntax.rhs (Thm.concl (Drule.ETA_CONV lambda))) partial,
          "captured lambda and partial application are not eta-equivalent")
      end
  | _ => die "FAIL: CPC lambda capture did not preserve its assumption"
end

fun cpc_proof_replay_ho_conversion_rules_success () =
let
  val beta = CPC_ProofReplay.replay_root_for_test
    (parse_cpc_proof_string
      "((define @t1 () (@var \"x\" Int)) \
      \(define @t2 () (_ (lambda (@list @t1) (+ @t1 1)) 2)) \
      \(step @p1 :rule beta-reduce :args ((= @t2 (+ 2 1)))))")
  val eta = CPC_ProofReplay.replay_root_for_test
    (parse_cpc_proof_string
      "((declare-const f (-> Bool Int)) \
      \(define @t1 () (@var \"x\" Bool)) \
      \(define @t2 () (lambda (@list @t1) (f @t1))) \
      \(step @p1 :rule lambda-elim :args ((= @t2 f))))")
  val alpha = CPC_ProofReplay.replay_root_for_test
    (parse_cpc_proof_string
      "((define @t1 () (@var \"x\" Int)) \
      \(define @t2 () (lambda (@list @t1) @t1)) \
      \(define @t3 () (@var \"y\" Int)) \
      \(step @p1 :rule alpha_equiv :args (@t2 (@list @t1) @t3)))")
in
  assert (Thm.concl beta ~~ ``(\x:int. x + 1) 2 = 2 + 1``,
    "CPC beta-reduce returned the wrong equality");
  let
    val (eta_left, eta_right) = boolSyntax.dest_eq (Thm.concl eta)
    val eta_reduced =
      boolSyntax.rhs (Thm.concl (Drule.ETA_CONV eta_left))
  in
    assert (Term.aconv eta_reduced eta_right,
      "CPC lambda-elim returned the wrong eta equality")
  end;
  assert (Thm.concl alpha ~~ ``(\x:int. x) = (\y:int. y)``,
    "CPC alpha_equiv did not replay abstraction renaming");
  List.app (Library.check_oracle_tags "CPC HO conversion unit test")
    [beta, eta, alpha]
end

fun cpc_proof_replay_ho_cong_and_ite_success () =
let
  val ho_proof = parse_cpc_proof_string
      "((declare-const f (-> Int Int)) (declare-const g (-> Int Int)) \
      \(declare-const x Int) (declare-const y Int) \
      \(assume @p1 (= f g)) (assume @p2 (= x y)) \
      \(step @p3 :rule ho_cong :premises (@p1 @p2)))"
  val ho_cong = CPC_ProofReplay.replay_root_for_test ho_proof
  val expected_ho_cong =
    case CPC_Proof.proof_commands ho_proof of
      [CPC_Proof.ASSUME (_, function_equality),
       CPC_Proof.ASSUME (_, argument_equality), _] =>
        let
          val (left_function, right_function) =
            boolSyntax.dest_eq function_equality
          val (left_argument, right_argument) =
            boolSyntax.dest_eq argument_equality
        in
          boolSyntax.mk_eq
            (Term.mk_comb (left_function, left_argument),
             Term.mk_comb (right_function, right_argument))
        end
    | _ => die "FAIL: CPC ho_cong capture lost its premise assumptions"
  val ite = CPC_ProofReplay.replay_root_for_test
    (parse_cpc_proof_string
      "((declare-const c Bool) (declare-const t Bool) \
      \(declare-const e Bool) (assume @p1 (= (not e) t)) \
      \(step @p2 :rule ite-neg-branch :premises (@p1) \
      \:args (c t e)))")
in
  assert (Thm.concl ho_cong ~~ expected_ho_cong,
    "CPC ho_cong did not apply MK_COMB to both premises");
  assert (Thm.concl ite ~~ ``(if c then t else e) = (c = t)``,
    "CPC ite-neg-branch returned the wrong equality");
  List.app (Library.check_oracle_tags "CPC HO congruence unit test")
    [ho_cong, ite]
end

(* cvc5 emits HO_CONG with n+1 premises for an n-ary application: the
   function equality followed by one equality per argument.  The shape above
   is only the unary case. *)
fun cpc_proof_replay_ho_cong_nary_success () =
let
  val proof = parse_cpc_proof_string
      "((declare-const f (-> Int Int Int)) \
      \(declare-const g (-> Int Int Int)) \
      \(declare-const x Int) (declare-const y Int) \
      \(declare-const u Int) (declare-const v Int) \
      \(assume @p1 (= f g)) (assume @p2 (= x y)) (assume @p3 (= u v)) \
      \(step @p4 :rule ho_cong :premises (@p1 @p2 @p3)))"
  val theorem = CPC_ProofReplay.replay_root_for_test proof
  val expected =
    case CPC_Proof.proof_commands proof of
      [CPC_Proof.ASSUME (_, function_equality),
       CPC_Proof.ASSUME (_, first_equality),
       CPC_Proof.ASSUME (_, second_equality), _] =>
        let
          val (left_function, right_function) =
            boolSyntax.dest_eq function_equality
          val (left_first, right_first) = boolSyntax.dest_eq first_equality
          val (left_second, right_second) =
            boolSyntax.dest_eq second_equality
        in
          boolSyntax.mk_eq
            (Term.list_mk_comb (left_function, [left_first, left_second]),
             Term.list_mk_comb (right_function, [right_first, right_second]))
        end
    | _ => die "FAIL: CPC n-ary ho_cong capture lost its premise assumptions"
in
  assert (Thm.concl theorem ~~ expected,
    "CPC ho_cong did not fold MK_COMB over every argument equality");
  Library.check_oracle_tags "CPC n-ary HO congruence unit test" theorem
end

fun cpc_proof_replay_ho_rare_rewrites_success () =
let
  val proof = parse_cpc_proof_string
    "((declare-const cpc_condition Bool) \
    \(declare-const cpc_then Bool) (declare-const cpc_else Bool) \
    \(declare-const cpc_rhs Bool) \
    \(step @p1 :rule bool-not-eq-elim1 :args (true false)) \
    \(step @p2 :rule eq-ite-lift \
    \ :args (cpc_condition cpc_then cpc_else cpc_rhs)) \
    \(step @p3 :rule distinct-false \
    \ :args ((= (distinct true true) false))) \
    \(step @p4 :rule distinct-elim \
    \ :args ((= (distinct true false) (not (= true false))))))"
  val theorem = CPC_ProofReplay.replay_root_for_test proof
in
  assert (List.length (CPC_Proof.proof_commands proof) = 4,
    "CPC HO RARE capture did not parse all inventoried rewrite steps");
  assert (Thm.concl theorem ~~
      ``ALL_DISTINCT [T; F] = ~(T = F)``,
    "CPC distinct-elim returned the wrong equality");
  Library.check_oracle_tags "CPC HO RARE rewrite unit test" theorem
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

fun cpc_proof_parser_totalized_arithmetic_success () =
let
  val proof = parse_cpc_proof_string
    "((declare-const a Int) (declare-const b Int) \
    \(declare-const x Real) (declare-const y Real) \
    \(assume @p1 (div_total a b a b)) \
    \(assume @p2 (mod_total a b)) \
    \(assume @p3 (/_total x y a)) \
    \(assume @p4 (@int_div_by_zero a)) \
    \(assume @p5 (@mod_by_zero a)) \
    \(assume @p6 (@div_by_zero x)) \
    \(assume @p8 @int_div_by_zero) \
    \(assume @p9 @mod_by_zero) \
    \(assume @p10 @div_by_zero) \
    \(define @t1 () (@purify (div_total a b))) \
    \(assume @p7 @t1))"
  val commands = CPC_Proof.proof_commands proof
  val smt_ediv_total = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_ediv_total"}
  val smt_emod_total = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_emod_total"}
  val smt_rdiv = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_rdiv"}
  val a = ``a:int``
  val b = ``b:int``
  val x = ``x:real``
  val y = ``y:real``
  val ra = intrealSyntax.mk_real_of_int a
  val nullary_ediv = Term.mk_var ("@int_div_by_zero", intSyntax.int_ty)
  val nullary_emod = Term.mk_var ("@mod_by_zero", intSyntax.int_ty)
  val nullary_rdiv = Term.mk_var ("@div_by_zero", realSyntax.real_ty)
  fun app (constant, terms) = Term.list_mk_comb (constant, terms)
  fun assumption_terms [] = []
    | assumption_terms (CPC_Proof.ASSUME (_, tm) :: rest) =
        tm :: assumption_terms rest
    | assumption_terms (_ :: rest) = assumption_terms rest
  val terms = assumption_terms commands
in
  assert (List.exists (fn tm => tm ~~ app (smt_ediv_total,
      [app (smt_ediv_total, [app (smt_ediv_total, [a, b]), a]), b])) terms,
    "div_total did not fold left-associatively");
  assert (List.exists (fn tm => tm ~~ app (smt_emod_total, [a, b])) terms,
    "mod_total did not map to smt_emod_total");
  assert (List.exists (fn tm => tm ~~
      realSyntax.mk_div (realSyntax.mk_div (x, y), ra) ) terms,
    "/_total did not fold or coerce Int arguments");
  assert (List.exists (fn tm => tm ~~ SmtLib_Theories.mk_int_ediv
      (a, intSyntax.zero_tm)) terms,
    "@int_div_by_zero did not preserve underspecified ediv");
  assert (List.exists (fn tm => tm ~~ SmtLib_Theories.mk_int_emod
      (a, intSyntax.zero_tm)) terms,
    "@mod_by_zero did not preserve underspecified emod");
  assert (List.exists (fn tm => tm ~~ app (smt_rdiv,
      [x, realSyntax.zero_tm])) terms,
    "@div_by_zero did not preserve underspecified smt_rdiv");
  assert (List.exists (fn tm => tm ~~ nullary_ediv) terms,
    "nullary @int_div_by_zero did not parse as an Int value");
  assert (List.exists (fn tm => tm ~~ nullary_emod) terms,
    "nullary @mod_by_zero did not parse as an Int value");
  assert (List.exists (fn tm => tm ~~ nullary_rdiv) terms,
    "nullary @div_by_zero did not parse as a Real value");
  assert (List.exists (fn tm => tm ~~ app (smt_ediv_total, [a, b])) terms,
    "@purify did not expose its totalized payload")
end

fun cpc_proof_parser_totalized_arithmetic_diagnostic () =
  (ignore (parse_cpc_proof_string
    "((declare-const a Int) (assume @p1 (**_total a a)))");
   die "FAIL: unsupported totalized arithmetic symbol parsed successfully")
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (String.isSubstring "**_total" msg,
        "unsupported totalized arithmetic diagnostic omitted the symbol: " ^ msg)
    end

fun cpc_totalized_outbound_exclusions_success () =
let
  fun no_builtin term =
    case SmtLib.builtin_encoding_for_test term of
      NONE => true
    | SOME (name, _) =>
        die ("FAIL: outbound translation unexpectedly exposes " ^ name)
in
  assert (no_builtin intSyntax.exp_tm,
    "integer power unexpectedly has an outbound SMT mapping");
  assert (no_builtin realSyntax.exp_tm,
    "real power unexpectedly has an outbound SMT mapping")
end

fun cpc_totalized_replay_success () =
let
  val a = ``a:int``
  val b = ``b:int``
  val x = ``x:real``
  val y = ``y:real``
  val int_ediv = SmtLib_Theories.mk_int_ediv (a, b)
  val int_emod = SmtLib_Theories.mk_int_emod (a, b)
  val smt_ediv_total = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_ediv_total"}
  val smt_emod_total = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_emod_total"}
  val smt_rdiv = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_rdiv"}
  fun app (constant, terms) = Term.list_mk_comb (constant, terms)
  fun list terms = listSyntax.mk_list (terms, intSyntax.int_ty)
  fun check_rare (name, args) =
    let val thm = CPC_ProofReplay.replay_rare_rewrite_for_test name args
      handle e => die (name ^ " replay failed: " ^ exnMessage e)
    in
      assert (Term.type_of (Thm.concl thm) = Type.bool,
        name ^ " did not replay to a proposition")
    end
  fun check_reduction (name, term) =
    let val thm = CPC_ProofReplay.replay_arith_reduction_for_test [term]
      handle e => die (name ^ " reduction failed: " ^ exnMessage e)
    in
      assert (Term.type_of (Thm.concl thm) = Type.bool,
        "arithmetic reduction did not replay to a proposition")
    end
  val rare =
    [("arith-div-total-zero-real", [x]),
     ("arith-div-total-zero-int", [a]),
     ("arith-int-div-total", [a, b]),
     ("arith-int-div-total-one", [a]),
     ("arith-int-div-total-zero", [a]),
     ("arith-int-div-total-neg", [a, b]),
     ("arith-int-mod-total", [a, b]),
     ("arith-int-mod-total-one", [a]),
     ("arith-int-mod-total-zero", [a]),
     ("arith-int-mod-total-neg", [a, b]),
     ("arith-mod-over-mod-1", [b, a]),
     ("arith-mod-over-mod", [b, list [], a, list []]),
     ("arith-mod-over-mod-mult", [b, list [], a, list []]),
     ("arith-divisible-elim", [b, a])]
  val reductions =
    [("ediv", int_ediv), ("emod", int_emod),
     ("smt_rdiv", app (smt_rdiv, [x, y])),
     ("div_total", app (smt_ediv_total, [a, b])),
     ("mod_total", app (smt_emod_total, [a, b])),
     ("real_div_total", realSyntax.mk_div (x, y))]
  val seven = ``(7:int)``
  val two = ``(2:int)``
  val neg_seven = intSyntax.mk_negated seven
  val neg_two = intSyntax.mk_negated two
  val eval_cases =
    [(app (smt_ediv_total, [seven, two]), ``(3:int)``),
     (app (smt_ediv_total, [neg_seven, two]),
       intSyntax.mk_negated ``(4:int)``),
     (app (smt_ediv_total, [neg_seven, neg_two]), ``(4:int)``),
     (app (smt_emod_total, [seven, two]), ``(1:int)``),
     (app (smt_emod_total, [neg_seven, two]), ``(1:int)``),
     (app (smt_emod_total, [neg_seven, neg_two]), ``(1:int)``)]
  fun check_eval (term, expected) =
    assert (Thm.concl (bossLib.EVAL term) ~~
      boolSyntax.mk_eq (term, expected),
      "totalized integer arithmetic did not evaluate to its CPC value")
  val abs_a = intSyntax.mk_absval a
  val abs_b = intSyntax.mk_absval b
  val abs_two = intSyntax.mk_absval ``2i``
  val abs_eq = CPC_ProofReplay.replay_arith_abs_eq_for_test [a, b]
  val abs_gt = CPC_ProofReplay.replay_arith_abs_int_gt_for_test [a, b]
  val abs_gt_target = boolSyntax.mk_eq
    (intSyntax.mk_greater (abs_a, abs_b),
     boolSyntax.mk_cond
       (intSyntax.mk_geq (a, intSyntax.zero_tm),
        boolSyntax.mk_cond
          (intSyntax.mk_geq (b, intSyntax.zero_tm),
           intSyntax.mk_greater (a, b),
           intSyntax.mk_greater (a, intSyntax.mk_negated b)),
        boolSyntax.mk_cond
          (intSyntax.mk_geq (b, intSyntax.zero_tm),
           intSyntax.mk_greater (intSyntax.mk_negated a, b),
           intSyntax.mk_greater
             (intSyntax.mk_negated a, intSyntax.mk_negated b))))
  val abs_product_target = boolSyntax.mk_eq
    (intSyntax.mk_absval (intSyntax.mk_mult (a, ``2i``)),
     intSyntax.mk_absval (intSyntax.mk_mult (b, ``2i``)))
  val abs_product =
    CPC_ProofReplay.replay_arith_mult_abs_comparison_for_test
      [Thm.ASSUME (boolSyntax.mk_eq (abs_a, abs_b)), Thm.REFL abs_two]
      abs_product_target
  val abs_product_gt_target = intSyntax.mk_greater
    (intSyntax.mk_absval (intSyntax.mk_mult (a, ``2i``)),
     intSyntax.mk_absval (intSyntax.mk_mult (b, ``2i``)))
  val abs_product_gt =
    CPC_ProofReplay.replay_arith_mult_abs_comparison_for_test
      [Thm.ASSUME (intSyntax.mk_greater (abs_a, abs_b)),
       Thm.CONJ (Thm.REFL abs_two)
         (Drule.EQT_ELIM (bossLib.EVAL ``(2:int) <> 0``))]
      abs_product_gt_target
  val c = ``c:bool``
  val t = ``t:bool``
  val e = ``e:bool``
  val ite = boolSyntax.mk_cond (c, t, e)
  fun disj [term] = term
    | disj (term :: terms) = boolSyntax.mk_disj (term, disj terms)
    | disj [] = boolSyntax.F
  fun neg term = boolSyntax.mk_neg term
  val cnf_ite_cases =
    [("cnf_ite_pos1", disj [neg ite, neg c, t]),
     ("cnf_ite_pos2", disj [neg ite, c, e]),
     ("cnf_ite_pos3", disj [neg ite, t, e]),
     ("cnf_ite_neg1", disj [ite, neg c, neg t]),
     ("cnf_ite_neg2", disj [ite, c, neg e]),
     ("cnf_ite_neg3", disj [ite, neg t, neg e])]
  fun check_cnf_ite (name, expected) =
    let val theorem = CPC_ProofReplay.replay_cnf_for_test name [ite]
    in assert (Thm.concl theorem ~~ expected,
      name ^ " replay produced the wrong conclusion") end
in
  List.app check_rare rare;
  List.app check_reduction reductions;
  List.app check_eval eval_cases;
  List.app check_cnf_ite cnf_ite_cases;
  assert (Thm.concl abs_eq ~~ boolSyntax.mk_eq
      (boolSyntax.mk_eq (abs_a, abs_b),
       boolSyntax.mk_disj (boolSyntax.mk_eq (a, b),
         boolSyntax.mk_eq (a, intSyntax.mk_negated b))),
    "arith-abs-eq replay produced the wrong conclusion");
  assert (Thm.concl abs_gt ~~ abs_gt_target,
    "arith-abs-int-gt replay produced the wrong conclusion");
  assert (Thm.concl abs_product ~~ abs_product_target,
    "arith_mult_abs_comparison equality replay produced the wrong conclusion");
  assert (Thm.concl abs_product_gt ~~ abs_product_gt_target,
    "arith_mult_abs_comparison strict replay produced the wrong conclusion")
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

(* An untested cvc5 version is never a reason to refuse a proof: it resolves
   to the nearest tested version and replays under that dialect.  A patch
   release shares its series' dialect, and an undiscoverable version falls
   back to the latest tested one. *)
fun cpc_proof_parser_version_resolution_success () =
let
  fun expect_resolved version expected =
    let val resolved = CPC_Proof.resolve_version version in
      assert (resolved = expected,
        "cvc5 version " ^ version ^ " resolved to " ^ resolved ^
        ", expected " ^ expected)
    end
  val dicts = SmtLib_Logics.parsedicts_of_logic "ALL"
  val instream = TextIO.openString
    "((step @p1 :rule refl :args (false)))"
in
  (* same major.minor series as the tested 1.3.4 *)
  expect_resolved "1.3.0" "1.3.4";
  (* untested versions resolve to the nearest tested one, either side *)
  expect_resolved "1.4.0" "1.3.4";
  expect_resolved "1.1.2" "1.3.4";
  (* an undiscoverable version resolves to the latest tested one *)
  expect_resolved CPC_Proof.unknown_cvc_version "1.3.4";
  (* a rule pinned to 1.3.4 resolves once the version has been resolved *)
  assert (Option.isSome
      (CPC_Proof.lookup_rule (CPC_Proof.resolve_version "1.4.0") "refl"),
    "CPC rule did not resolve under a resolved untested cvc5 version");
  (* and parsing an untested version succeeds rather than failing *)
  ignore (CPC_ProofParser.parse_stream_with_version dicts "1.4.0" instream)
  handle Feedback.HOL_ERR holerr =>
    die ("FAIL: untested cvc5 version failed to parse: " ^
      Feedback.message_of holerr)
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

fun cpc_profile_call_count name =
  case List.find (fn (result_name, _) => result_name = name)
      (Profile.results ()) of
    SOME (_, info) => #n info
  | NONE => 0

fun cpc_cache_repeated_conclusion_bypasses_handler_success () =
if not CPC_ProofReplay.theorem_cache_enabled_for_test then () else let
  val proof = parse_cpc_proof_string
    "((step @p1 (= true true) :rule refl :args (true)) \
    \(step @p2 (= true true) :rule contra))"
  val () = Profile.reset_all ()
  val (thm, stats) =
    CPC_ProofReplay.replay_root_with_cache_stats_for_test proof
in
  assert (Thm.concl thm ~~ ``T = T``,
    "CPC cache hit returned the wrong explicit conclusion");
  assert (#hits stats = 1,
    "repeated CPC conclusion did not produce exactly one cache hit");
  assert (#misses stats = 1,
    "first CPC explicit conclusion did not produce exactly one miss");
  assert (cpc_profile_call_count "CPC(cache:hypfree_hit)" = 1,
    "CPC cache test did not record its hypothesis-free hit under a stable key");
  assert (cpc_profile_call_count "CPC(handler:ProofRule/refl)" = 1,
    "CPC cache test did not execute its seed handler exactly once");
  assert (cpc_profile_call_count "CPC(handler:ProofRule/contra)" = 0,
    "CPC cache hit did not bypass the deliberately invalid handler");
  assert (cpc_profile_call_count "CPC(check:step_conclusion)" = 2,
    "CPC cache reuse bypassed the certificate conclusion check")
end

fun cpc_cache_popped_scope_is_rejected_success () =
if not CPC_ProofReplay.theorem_cache_enabled_for_test then () else let
  val proof = parse_cpc_proof_string
    "((assume-push @p1 true) \
    \(step @p2 :rule scope :premises (@p1)) \
    \(step @p3 :rule refl :args (true)) \
    \(step @p4 true :rule true_elim :premises (@p3)))"
  val (thm, stats) =
    CPC_ProofReplay.replay_root_with_cache_stats_for_test proof
in
  assert (Thm.concl thm ~~ ``T``,
    "CPC scope cache regression replayed to the wrong conclusion");
  assert (#context_rejections stats >= 1,
    "theorem depending on a popped CPC scope was not context-rejected");
  assert (#misses stats >= 1,
    "popped-scope CPC theorem unexpectedly produced a cache hit")
end

fun cpc_cache_prefers_derived_over_assumption_success () =
if not CPC_ProofReplay.theorem_cache_enabled_for_test then () else let
  val proof = parse_cpc_proof_string
    "((step @p1 (= true true) :rule refl :args (true)) \
    \(assume @p2 (= true true)) \
    \(step @p3 (= true true) :rule contra))"
  val () = Profile.reset_all ()
  val (thm, stats) =
    CPC_ProofReplay.replay_root_with_cache_stats_for_test proof
in
  assert (List.null (Thm.hyp thm),
    "raw CPC assumption displaced a derived theorem in the cache");
  assert (#hits stats = 1,
    "derived/assumption CPC cache regression did not hit the cache");
  assert (cpc_profile_call_count "CPC(handler:ProofRule/contra)" = 0,
    "derived CPC cache theorem did not bypass the invalid handler")
end

fun cpc_cache_omitted_conclusion_bypasses_success () =
if not CPC_ProofReplay.theorem_cache_enabled_for_test then () else let
  val proof = parse_cpc_proof_string
    "((step @p1 :rule refl :args (true)))"
  val (thm, stats) =
    CPC_ProofReplay.replay_root_with_cache_stats_for_test proof
in
  assert (Thm.concl thm ~~ ``T = T``,
    "omitted-conclusion CPC step replayed incorrectly");
  assert (#omitted_bypasses stats = 1,
    "omitted CPC conclusion did not record a cache bypass");
  assert (#hits stats = 0 andalso #misses stats = 0,
    "omitted CPC conclusion incorrectly probed the theorem cache");
  assert (#cardinality stats = 1 andalso #peak_cardinality stats = 1,
    "CPC per-proof cache cardinality counters are inconsistent");
  assert (#step_cardinality stats = 1,
    "CPC per-proof step cardinality counter is inconsistent")
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

fun z3_proof_parser_verbatim_lambda_binding_success () =
let
  (* Pinned from the 4.11.2 lambda-equality proof family. *)
  val proof = parse_z3_proof_string "4.11.2"
    "((proof (let ((?x28 (lambda ((x Int)) \
    \(! (+ x 1) :qid k!4)))) (asserted (= ?x28 ?x28)))))"
  val expected = ``\x:int. x + 1``
in
  case Redblackmap.peek (Z3_Proof.proof_steps proof, 0) of
    SOME (Z3_Proof.ASSERTED concl) =>
      let val (lhs, rhs) = boolSyntax.dest_eq concl in
        assert (lhs ~~ expected andalso rhs ~~ expected,
          "verbatim proof lambda did not alpha-match its HOL abstraction");
        assert (List.null (Term.free_vars lhs),
          "verbatim proof lambda leaked its bound variable")
      end
  | SOME _ => die "FAIL: verbatim lambda parsed to unexpected constructor"
  | NONE => die "FAIL: verbatim lambda proof did not define root proof step"
end

fun z3_proof_parser_structures_proof_bind_success () =
let
  (* Pinned from the 4.15.3 named-lambda-def proof family. *)
  val proof = parse_z3_proof_string "4.15.3"
    "((proof (let ((?x67 (lambda ((x Int)) \
    \(refl (~ (= x x) (= x x)))))) \
    \(let ((?x80 (lambda ((x Int)) \
    \(rewrite (= (= x x) (= x x)))))) \
    \(mp (nnf-pos (proof-bind ?x67) false) \
    \(quant-intro (proof-bind ?x80) false) false)))))"
  val pinned_versions = ["4.11.2", "4.12.4", "4.13.0", "4.14.1",
    "4.15.3"]
  val _ = List.app (fn version => assert (Option.isSome
      (Z3_Proof.lookup_rule version "proof-bind"),
    "proof-bind was not enabled for pinned Z3 " ^ version)) pinned_versions
  val _ = assert (not (Option.isSome
      (Z3_Proof.lookup_rule "4.10.2" "proof-bind")),
    "proof-bind accepted an unpinned raw registry version")
in
  case Redblackmap.peek (Z3_Proof.proof_steps proof, 0) of
    SOME (Z3_Proof.MP
      (Z3_Proof.NNF_POS
         ([Z3_Proof.PROOF_BIND ([nnf_var], Z3_Proof.REFL nnf_body)],
          nnf_concl),
       Z3_Proof.QUANT_INTRO
         (Z3_Proof.PROOF_BIND
            ([quant_var], Z3_Proof.REWRITE quant_body), quant_concl),
       root_concl)) =>
        (assert (nnf_var ~~ ``x:int`` andalso quant_var ~~ ``x:int``,
          "proof-bind did not preserve its bound variables");
         assert (List.exists (fn free => free ~~ nnf_var)
             (Term.free_vars nnf_body) andalso
           List.exists (fn free => free ~~ quant_var)
             (Term.free_vars quant_body),
          "proof-bind bodies do not refer to their preserved variables");
         assert (nnf_concl ~~ ``F`` andalso quant_concl ~~ ``F`` andalso
             root_concl ~~ ``F``,
          "proof-bind consumers parsed unexpected conclusions"))
  | SOME _ => die "FAIL: proof-bind parsed to unexpected structure"
  | NONE => die "FAIL: proof-bind proof did not define root proof step"
end

fun z3_proof_parser_erases_inert_proof_bind_success () =
let
  (* A `proof-bind` binds nothing without a lambda operand, and binds
     nothing a consumer reads when the enclosing rule ignores bound
     variables; both erase to the wrapped proofterm. *)
  val no_lambda = parse_z3_proof_string "4.15.3"
    "((proof (nnf-pos (proof-bind (refl false)) false)))"
  val no_consumer = parse_z3_proof_string "4.15.3"
    "((proof (mp (proof-bind (lambda ((x Int)) (asserted false))) \
    \(asserted (= false false)) false)))"
in
  (case Redblackmap.peek (Z3_Proof.proof_steps no_lambda, 0) of
     SOME (Z3_Proof.NNF_POS ([Z3_Proof.REFL _], _)) => ()
   | SOME _ =>
       die "FAIL: non-lambda proof-bind parsed to unexpected structure"
   | NONE =>
       die "FAIL: non-lambda proof-bind did not define root proof step");
  case Redblackmap.peek (Z3_Proof.proof_steps no_consumer, 0) of
    SOME (Z3_Proof.MP (Z3_Proof.ASSERTED _, Z3_Proof.ASSERTED _, _)) => ()
  | SOME _ => die "FAIL: inert proof-bind parsed to unexpected structure"
  | NONE => die "FAIL: inert proof-bind did not define root proof step"
end

fun z3_proof_bind_replay_success () =
let
  val var = ``x:int``
  val body = Z3_Proof.REFL (boolSyntax.mk_eq (var, var))
  val initial = Z3_Proof.empty_proof "4.15.3"
  val steps = Redblackmap.insert (Z3_Proof.proof_steps initial, 0,
    Z3_Proof.PROOF_BIND ([var], body))
  val proof = Z3_Proof.update_proof_steps initial steps
  val thm = Z3_ProofReplay.replay_root_for_test proof
in
  assert (Thm.concl thm ~~ boolSyntax.mk_eq (var, var),
    "structured proof-bind did not replay its body theorem");
  Library.check_oracle_tags "Z3 structured proof-bind replay" thm
end

fun z3_proof_bind_empty_annotation_replay_success () =
let
  val body = Z3_Proof.REFL ``T = T``
  val initial = Z3_Proof.empty_proof "4.15.3"
  val steps = Redblackmap.insert (Z3_Proof.proof_steps initial, 0,
    Z3_Proof.PROOF_BIND ([], body))
  val proof = Z3_Proof.update_proof_steps initial steps
  val thm = Z3_ProofReplay.replay_root_for_test proof
in
  (* proof-bind is an annotation, not a rule: an empty annotation erases to
     its body rather than rejecting the certificate. *)
  assert (Thm.concl thm ~~ ``T = T``,
    "empty proof-bind annotation did not replay its body theorem");
  Library.check_oracle_tags "Z3 empty proof-bind annotation replay" thm
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

(* An untested Z3 version is never a reason to refuse a proof: it resolves to
   the nearest tested anchor and replays under that dialect.  A patch release
   shares its series' dialect, and an undiscoverable version falls back to the
   latest anchor. *)
fun z3_proof_parser_version_resolution_success () =
let
  fun expect_resolved version expected =
    let val resolved = Z3_Proof.resolve_version version in
      assert (resolved = expected,
        "Z3 version " ^ version ^ " resolved to " ^ resolved ^
        ", expected " ^ expected)
    end
in
  (* patch releases share their series' anchor *)
  expect_resolved "4.13.7" "4.13.0";
  expect_resolved "4.11.0" "4.11.2";
  (* untested versions resolve to the nearest anchor *)
  expect_resolved "4.9.1" "4.11.2";
  expect_resolved "4.16.0" "4.15.3";
  (* a pre-4 version is untested rather than fatal *)
  expect_resolved "3.0.0" "4.11.2";
  (* an undiscoverable version resolves to the latest anchor *)
  expect_resolved Z3_Proof.unknown_z3_version "4.15.3";
  (* `apply-def` is gated to the "4." prefix; it resolves once the version
     has been resolved, even though "3.0.0" itself would not match *)
  assert (Option.isSome
      (Z3_Proof.lookup_rule (Z3_Proof.resolve_version "3.0.0") "apply-def"),
    "Z3 rule did not resolve under a resolved untested version");
  (* and parsing an untested version succeeds rather than failing *)
  ignore (parse_z3_proof_string "3.0.0"
    "((proof (apply-def (asserted false) false)))")
  handle Feedback.HOL_ERR holerr =>
    die ("FAIL: untested Z3 version failed to parse: " ^
      Feedback.message_of holerr)
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

fun z3_proof_parser_is_int_translation_collision_success () =
let
  val five_halves = realSyntax.mk_div
    (realSyntax.term_of_int (Arbint.fromInt 5),
     realSyntax.term_of_int (Arbint.fromInt 2))
  val is_int_term = intrealSyntax.mk_is_int five_halves
  val (translation, _) =
    SmtLib.goal_to_SmtLib_with_get_proof_translation NONE
      ([], boolSyntax.mk_neg is_int_term)
  val dicts = SmtLib.parser_dicts_for_translation translation
  val proof = parse_z3_proof_string_with_dicts dicts "4.15.3"
    "((set-logic QF_NIRA)\n\
    \(proof\n\
    \(mp (asserted (is_int (/ 5.0 2.0)))\
    \ (rewrite (= (is_int (/ 5.0 2.0)) false)) false)))"
in
  ignore proof
end

fun z3_proof_parser_string_internal_symbols_success () =
let
  val fragment =
    "((declare-fun x () String)\n\
    \(declare-fun ch () Char)\n\
    \(proof\n\
    \(asserted\n\
    \(and\n\
    \ (= x \"a\")\n\
    \ (= ch (_ Char 97))\n\
    \ (= (seq.unit (_ Char 97)) (seq.unit (_ Char 97)))\n\
    \ (= (seq.nth_i x 0) (seq.nth_i x 0))\n\
    \ ((_ seq.eq seq.eq) x ((_ seq.tail seq.tail) x 0))\n\
    \ (= ((_ seq.stoi seq.stoi) x 0) (seq.stoi x 0))\n\
    \ (= ((_ seq.digit2int seq.digit2int) ch)\n\
    \    (seq.digit2int ch))\n\
    \ (= (seq.digit ch) (seq.digit ch))\n\
    \ (char.is_digit ch)\n\
    \ (char.<= ch ch)\n\
    \ ((_ char.bit char.bit 0) ch)\n\
    \ (= (seq.digit ((_ bits2char bits2char)\n\
    \      true false false false false false false false false\n\
    \      false false false false false false false false false))\n\
    \    (seq.digit ch))\n\
    \ ((_ aut.accept aut.accept) x 0 (str.to_re x))\n\
    \ (= ((_ seq.prefix.c seq.prefix.c) x x)\n\
    \    ((_ seq.prefix.d seq.prefix.d) x x))\n\
    \ ((_ seq.eq seq.eq)\n\
    \   ((_ seq.prefix.x seq.prefix.x) x x)\n\
    \   (str.++ ((_ seq.prefix.y seq.prefix.y) x x)\n\
    \           ((_ seq.prefix.z seq.prefix.z) x x)))\n\
    \ (= ((_ str.<.c str.<.c) x x)\n\
    \    ((_ str.<.d str.<.d) x x))\n\
    \ ((_ seq.eq seq.eq)\n\
    \   ((_ str.<.x str.<.x) x x)\n\
    \   (str.++ ((_ str.<.y str.<.y) x x)\n\
    \           ((_ str.<.z str.<.z) x x))))))))"
  val expected_constants = [
    "seq_unit", "seq_nth_i", "seq_tail", "seq_eq", "seq_stoi",
    "seq_digit2int", "seq_digit", "char_is_digit", "char_bit",
    "aut_accept"
  ]
  val expected_witnesses = [
    "seq.prefix.c", "seq.prefix.d", "seq.prefix.x",
    "seq.prefix.y", "seq.prefix.z", "str.<.c", "str.<.d",
    "str.<.x", "str.<.y", "str.<.z"
  ]
  val expected_char_ty = wordsSyntax.mk_word_type
    (fcpLib.index_type (Arbnum.fromInt 18))
  fun root_conclusion proof =
    case Redblackmap.peek (Z3_Proof.proof_steps proof, 0) of
      SOME (Z3_Proof.ASSERTED concl) => concl
    | SOME _ => die "FAIL: string-internal fragment parsed to wrong rule"
    | NONE => die "FAIL: string-internal fragment has no root proof step"
  fun has_constant name concl =
    Lib.can (HolKernel.find_term (fn tm =>
      Term.is_const tm andalso
      let val {Thy, Name, ...} = Term.dest_thy_const tm
      in Thy = "smtstringz3" andalso Name = name end)) concl
  fun has_witness name concl =
    List.exists (fn tm =>
      Term.is_var tm andalso Lib.fst (Term.dest_var tm) = name)
      (Term.free_vars concl)
  fun check_version version =
    let
      val proof = parse_z3_proof_string version fragment
      val concl = root_conclusion proof
      val ch = List.find (fn tm =>
        Term.is_var tm andalso Lib.fst (Term.dest_var tm) = "ch")
        (Term.free_vars concl)
    in
      List.app (fn name => assert (has_constant name concl,
        "Z3 " ^ version ^ " did not resolve " ^ name ^
        " to smtstringz3Theory")) expected_constants;
      List.app (fn name => assert (has_witness name concl,
        "Z3 " ^ version ^ " did not retain proof-local witness " ^
        name)) expected_witnesses;
      if version = "4.15.3" then
        assert (HOLset.member (Z3_Proof.proof_vars proof,
            Term.mk_var ("seq.p.suffix",
              boolSyntax.list_mk_fun
                ([smt_string_ty, smt_string_ty],
                 smt_string_ty))),
          "Z3 4.15.3 did not register seq.p.suffix as proof-local")
      else ();
      case ch of
        SOME tm => assert (Term.type_of tm = expected_char_ty,
          "Z3 " ^ version ^ " Char sort did not resolve to 18 word")
      | NONE => die ("FAIL: Z3 " ^ version ^
          " string-internal fragment lost its Char variable")
    end
in
  check_version "4.11.2";
  check_version "4.15.3"
end

fun z3_proof_parser_char_th_lemma_index_success () =
let
  val proof = parse_z3_proof_string "4.15.3"
    "((proof ((_ th-lemma char) false)))"
in
  case Redblackmap.peek (Z3_Proof.proof_steps proof, 0) of
    SOME (Z3_Proof.TH_LEMMA_CHAR
      ({theory, subkind, indices}, [], concl)) =>
        assert (theory = "char" andalso subkind = NONE andalso
            List.null indices andalso concl ~~ ``F``,
          "char th-lemma index metadata was not preserved")
  | SOME _ => die "FAIL: char th-lemma parsed to unexpected constructor"
  | NONE => die "FAIL: char th-lemma proof has no root step"
end

fun benchmark_rejects_z3_string_internal_symbols () =
let
  val cases = [
    ("Char", "(declare-const ch Char)\n(assert (= ch ch))\n"),
    ("Char", "(assert (= x (_ Char 97)))\n"),
    ("seq.unit", "(assert (= x (seq.unit 97)))\n"),
    ("seq.nth_i", "(assert (= (seq.nth_i x 0) 0))\n"),
    ("seq.tail",
      "(assert (= x ((_ seq.tail seq.tail) x 0)))\n"),
    ("seq.eq", "(assert ((_ seq.eq seq.eq) x x))\n"),
    ("seq.stoi", "(assert (= (seq.stoi x 0) 0))\n"),
    ("seq.digit2int", "(assert (= (seq.digit2int 48) 0))\n"),
    ("seq.digit", "(assert (= (seq.digit 48) 0))\n"),
    ("char.is_digit", "(assert (char.is_digit 48))\n"),
    ("char.<=", "(assert (char.<= 48 57))\n"),
    ("bits2char",
      "(assert (= ((_ bits2char bits2char)\
      \ true false false false false false false false false\
      \ false false false false false false false false false) 1))\n"),
    ("char.bit", "(assert ((_ char.bit char.bit 0) 48))\n"),
    ("aut.accept",
      "(assert ((_ aut.accept aut.accept) x 0 (str.to_re x)))\n"),
    ("seq.prefix.c",
      "(assert (= ((_ seq.prefix.c seq.prefix.c) x x) 0))\n"),
    ("str.<.c",
      "(assert (= ((_ str.<.c str.<.c) x x) 0))\n"),
    ("seq.p.suffix",
      "(assert (= ((_ seq.p.suffix seq.p.suffix) x x) x))\n")
  ]
  fun check (symbol, command) =
    expect_hol_error_contains ("benchmark Z3 internal " ^ symbol)
      symbol (fn () => ignore (parse_legacy_smtlib_assertions
        ("(set-logic QF_S)\n(declare-const x String)\n" ^
         command ^ "(exit)\n")))
in
  List.app check cases
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

fun z3_beta_eta_replay_rungs_success () =
let
  val beta_var = ``beta_x:int``
  val beta_lhs = Term.mk_comb
    (Term.mk_abs (beta_var, beta_var), ``2i``)
  val beta_rhs = ``2i``
  val beta_thm = Z3_ProofReplay.beta_equal_for_test (beta_lhs, beta_rhs)
  val eta_lhs = ``\x:bool. (p:bool->bool) x``
  val eta_rhs = ``p:bool->bool``
  val eta_thm = Z3_ProofReplay.eta_equal_for_test (eta_lhs, eta_rhs)
  val beta_mono = Z3_ProofReplay.monotonicity_prove_for_test
    ([], boolSyntax.mk_eq (beta_lhs, beta_rhs))
  val eta_mono = Z3_ProofReplay.monotonicity_prove_for_test
    ([], boolSyntax.mk_eq (eta_lhs, eta_rhs))
in
  assert (Thm.concl beta_thm ~~ boolSyntax.mk_eq (beta_lhs, beta_rhs),
    "beta replay rung returned the wrong equality");
  assert (Thm.concl eta_thm ~~ boolSyntax.mk_eq (eta_lhs, eta_rhs),
    "eta replay rung returned the wrong equality");
  assert (Thm.concl beta_mono ~~ boolSyntax.mk_eq (beta_lhs, beta_rhs),
    "monotonicity beta rung returned the wrong equality");
  assert (Thm.concl eta_mono ~~ boolSyntax.mk_eq (eta_lhs, eta_rhs),
    "monotonicity eta rung returned the wrong equality");
  Library.check_oracle_tags "Z3 beta replay rung" beta_thm;
  Library.check_oracle_tags "Z3 eta replay rung" eta_thm;
  Library.check_oracle_tags "Z3 monotonicity beta rung" beta_mono;
  Library.check_oracle_tags "Z3 monotonicity eta rung" eta_mono
end

fun z3_beta_eta_replay_rungs_shaped_failure () =
let
  fun expect_failure name thunk =
    (ignore (thunk ());
     die ("FAIL: malformed " ^ name ^ " replay rung succeeded"))
    handle Feedback.HOL_ERR _ => ()
in
  expect_failure "beta"
    (fn () =>
      let
        val x = ``beta_x:int``
        val redex = Term.mk_comb (Term.mk_abs (x, x), ``2i``)
      in
        Z3_ProofReplay.beta_equal_for_test (redex, ``4i``)
      end);
  expect_failure "eta"
    (fn () => Z3_ProofReplay.eta_equal_for_test
      (``\x:bool. (p:bool->bool) x``, ``q:bool->bool``))
end

fun z3_rewrite_beta_eta_abs_rungs_success () =
let
  val beta = replay_z3_proof_string
    "((declare-fun k () Int) \
    \(proof (rewrite (= \
    \(select (lambda ((x Int)) (+ x k)) 7) (+ 7 k))))))"
  val eta = replay_z3_proof_string
    "((declare-fun f () (Array Int Int)) \
    \(proof (rewrite (= \
    \(lambda ((x Int)) (select f x)) f))))"
  val abs = replay_z3_proof_string
    "((proof (rewrite (= \
    \(lambda ((x Int)) (+ x 1)) \
    \(lambda ((x Int)) (+ 1 x))))))"
in
  assert (Thm.concl beta ~~ ``(\x:int. x + k) 7 = 7 + k``,
    "rewrite beta rung returned the wrong equality");
  assert (Thm.concl eta ~~ ``(\x:int. (f:int->int) x) = f``,
    "rewrite eta rung returned the wrong equality");
  assert (Thm.concl abs ~~ ``(\x:int. x + 1) = (\x. 1 + x)``,
    "rewrite ABS rung returned the wrong equality");
  Library.check_oracle_tags "Z3 rewrite beta rung" beta;
  Library.check_oracle_tags "Z3 rewrite eta rung" eta;
  Library.check_oracle_tags "Z3 rewrite ABS rung" abs
end

fun z3_rewrite_abs_rung_shaped_failure () =
  expect_hol_error_contains "rewrite ABS body mismatch"
    "proof rule: rewrite"
    (fn () => ignore (replay_z3_proof_string
      "((proof (rewrite (= \
      \(lambda ((x Int)) (+ x 1)) \
      \(lambda ((x Int)) (+ x 2))))))"))

fun z3_abs_congruence_replay_rung_success () =
let
  val x = ``x:int``
  val premise = intLib.ARITH_PROVE ``x + 0i = x``
  val target = ``(\x:int. x + 0i) = (\x. x)``
  val thm = Z3_ProofReplay.monotonicity_prove_for_test ([premise], target)
  val capture_safe_target = ``(\x:int. x + 0i) = (\y. y)``
  val capture_safe = Z3_ProofReplay.monotonicity_prove_for_test
    ([premise], capture_safe_target)
in
  assert (Thm.concl thm ~~ target,
    "ABS congruence replay rung returned the wrong equality");
  assert (Thm.concl capture_safe ~~ capture_safe_target,
    "ABS congruence did not preserve alpha-renamed binders");
  Library.check_oracle_tags "Z3 ABS congruence replay rung" thm;
  Library.check_oracle_tags "Z3 capture-safe ABS congruence" capture_safe
end

fun z3_abs_congruence_replay_rung_shaped_failure () =
let
  val x = ``x:int``
  val captured = Thm.ASSUME ``x + 0i = x``
  val target = ``(\x:int. x + 0i) = (\x. x)``
in
  (ignore (Z3_ProofReplay.monotonicity_prove_for_test ([captured], target));
   die "FAIL: ABS congruence captured a variable from a hypothesis")
  handle Feedback.HOL_ERR _ => ()
end

fun z3_lambda_intro_def_replay_success () =
let
  val thm = replay_z3_proof_string
    "((declare-fun z () (Array Int Int)) \
    \(proof (intro-def (forall ((x Int)) \
    \(= (+ x 1) (select z x))))))"
  val expected = ``!x:int. x + 1 = (z:int->int) x``
  val def = ``(z:int->int) = (\x. x + 1)``
  val left = replay_z3_proof_string
    "((declare-fun zl () (Array Int Int)) \
    \(proof (intro-def (forall ((x Int)) \
    \(= (select zl x) (+ x 1))))))"
  val left_expected = ``!x:int. (zl:int->int) x = x + 1``
  val left_def = ``(zl:int->int) = (\x. x + 1)``
  val binary = replay_z3_proof_string
    "((declare-fun z2 () (Array Int (Array Int Int))) \
    \(proof (intro-def (forall ((x Int) (y Int)) \
    \(= (+ x y) (select (select z2 x) y))))))"
  val binary_expected =
    ``!x y:int. x + y = (z2:int->int->int) x y``
  val binary_def = ``(z2:int->int->int) = (\x y. x + y)``
in
  assert (Thm.concl thm ~~ expected,
    ":lambda-def intro-def replay returned the wrong conclusion");
  assert (HOLset.member (Thm.hypset thm, def),
    ":lambda-def intro-def did not record its function definition");
  assert (Thm.concl left ~~ left_expected,
    "left-oriented :lambda-def returned the wrong conclusion");
  assert (HOLset.member (Thm.hypset left, left_def),
    "left-oriented :lambda-def did not record its function definition");
  assert (Thm.concl binary ~~ binary_expected,
    "two-binder :lambda-def returned the wrong conclusion");
  assert (HOLset.member (Thm.hypset binary, binary_def),
    "two-binder :lambda-def did not record its function definition: " ^
    String.concatWith ", "
      (List.map term_with_types (HOLset.listItems (Thm.hypset binary))));
  Library.check_oracle_tags "Z3 :lambda-def intro-def" thm;
  Library.check_oracle_tags "Z3 left-oriented :lambda-def" left;
  Library.check_oracle_tags "Z3 two-binder :lambda-def" binary
end

fun z3_lambda_intro_def_replay_shaped_failure () =
  expect_hol_error_contains ":lambda-def without a Z3 name"
    "unsupported :lambda-def intro-def shape"
    (fn () => ignore (replay_z3_proof_string
      "((proof (intro-def (forall ((x Int)) (= x x)))))"))

fun z3_proof_bind_consumers_replay_success () =
let
  (* Complete intro-def/nnf-pos/quant-intro chain minimized directly from
     the C1 4.12.4--4.15.3 lambda-equality certificates. *)
  val thm = replay_z3_proof_string
    "((declare-fun z () (Array Int Int)) \
    \(proof (mp \
    \(mp~ \
    \(intro-def (forall ((x Int)) \
    \(= (+ 1 x) (select z x)))) \
    \(nnf-pos \
    \(proof-bind (lambda ((x Int)) \
    \(refl (~ (= (+ 1 x) (select z x)) \
    \(= (+ 1 x) (select z x)))))) \
    \(~ (forall ((x Int)) (= (+ 1 x) (select z x))) \
    \(forall ((x Int)) (= (+ 1 x) (select z x))))) \
    \(forall ((x Int)) (= (+ 1 x) (select z x)))) \
    \(quant-intro \
    \(proof-bind (lambda ((x Int)) \
    \(rewrite (= \
    \(= (+ 1 x) (select z x)) \
    \(= (+ x (* (- 1) (select z x))) (- 1)))))) \
    \(= (forall ((x Int)) (= (+ 1 x) (select z x))) \
    \(forall ((x Int)) \
    \(= (+ x (* (- 1) (select z x))) (- 1))))) \
    \(forall ((x Int)) \
    \(= (+ x (* (- 1) (select z x))) (- 1)))))))"
  val expected = ``!x:int. x + -1 * (z:int->int) x = -1``
  val two_bound = replay_z3_proof_string
    "((proof (quant-intro \
    \(proof-bind (lambda ((x Int) (y Int)) \
    \(refl (= (= (+ x y) (+ y x)) (= (+ x y) (+ y x)))))) \
    \(= (forall ((x Int) (y Int)) (= (+ x y) (+ y x))) \
    \(forall ((x Int) (y Int)) (= (+ x y) (+ y x)))))))"
  val two_bound_nnf = replay_z3_proof_string
    "((proof (nnf-pos \
    \(proof-bind (lambda ((x Int) (y Int)) \
    \(refl (~ (= (+ x y) (+ y x)) (= (+ x y) (+ y x)))))) \
    \(~ (forall ((x Int) (y Int)) (= (+ x y) (+ y x))) \
    \(forall ((x Int) (y Int)) (= (+ x y) (+ y x)))))))"
in
  assert (Thm.concl thm ~~ expected,
    "C1 proof-bind consumer chain returned the wrong conclusion");
  List.app (fn (name, bound_thm) =>
    let
      val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl bound_thm)
      val (vars, _) = boolSyntax.strip_forall lhs
    in
      assert (List.length vars = 2 andalso lhs ~~ rhs,
        "two-binder proof-bind " ^ name ^
        " returned the wrong conclusion: " ^
        term_with_types (Thm.concl bound_thm))
    end)
    [("quant-intro", two_bound), ("nnf-pos", two_bound_nnf)];
  Library.check_oracle_tags "Z3 C1 proof-bind consumer chain" thm;
  Library.check_oracle_tags "Z3 two-binder proof-bind" two_bound;
  Library.check_oracle_tags "Z3 two-binder proof-bind nnf-pos" two_bound_nnf
end

fun z3_proof_bind_quant_intro_binder_annotation_ignored () =
let
  (* The proof-bind wrapper records one bound variable, but quant-intro
     reintroduces two.  The annotation is metadata, not a replay
     precondition: `z3_quant_intro` reconstructs the step from the terms and
     `check_thm` validates it, so replay accepts the certificate rather than
     rejecting it on the binder-count discrepancy. *)
  val thm = replay_z3_proof_string
    "((proof (quant-intro \
    \(proof-bind (lambda ((x Int)) \
    \(refl (= (= x x) (= x x))))) \
    \(= (forall ((x Int) (y Int)) (= x x)) \
    \(forall ((x Int) (y Int)) (= x x))))))"
  val expected = ``(!x:int y:int. x = x) = (!x:int y:int. x = x)``
in
  assert (Thm.concl thm ~~ expected,
    "proof-bind quant-intro binder annotation: wrong conclusion " ^
    term_with_types (Thm.concl thm));
  Library.check_oracle_tags
    "Z3 proof-bind quant-intro binder annotation" thm
end

fun z3_proof_bind_nnf_pos_unliftable_premise_success () =
let
  (* The bound variable occurs free in the premise's hypothesis, so the
     forall congruence is not constructible.  It is an extra rewrite rather
     than a replay precondition, so the step still replays from the
     unlifted premise. *)
  val thm = replay_z3_proof_string
    "((proof (nnf-pos \
    \(proof-bind (lambda ((x Int)) \
    \(hypothesis (= x x)))) \
    \(~ (forall ((x Int)) (= x x)) \
    \(forall ((x Int)) (= x x))))))"
  val expected = ``(!x:int. x = x) = (!x:int. x = x)``
in
  assert (Thm.concl thm ~~ expected,
    "unliftable proof-bind premise: wrong conclusion " ^
    term_with_types (Thm.concl thm));
  Library.check_oracle_tags "Z3 unliftable proof-bind nnf-pos premise" thm
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

fun assert_string_prover name prover tm =
  (let
     val thm = prover tm
   in
     assert (Thm.concl thm ~~ tm,
       name ^ " proved wrong conclusion: " ^ Library.thm_to_string thm);
     Library.check_oracle_tags name thm
   end
   handle Feedback.HOL_ERR holerr =>
     die ("FAIL: " ^ name ^ " did not prove string goal: " ^
       Feedback.message_of holerr)
        | exn =>
      die ("FAIL: " ^ name ^ " raised " ^ General.exnMessage exn))

fun string_prove_ladder_rungs_success () =
  (assert (not (List.null Z3_ProformaThms.string_thm_list),
     "string proforma list was not installed");
   assert_string_prover "string_prove proforma rung"
     SmtStringProve.proforma_prove
     ``smtstr_concat (smtstr_concat s t) u =
       smtstr_concat s (smtstr_concat t u)``;
   assert_string_prover "string_prove ground evaluation rung"
     SmtStringProve.ground_eval_prove
     ``smtstr_lt (SmtStr [97; 98]) (SmtStr [97; 99]) /\
       smtstr_to_int (SmtStr [49; 50]) = 12 /\
       smt_in_re (SmtStr [97; 97])
         (reglan_star (reglan_to_re (SmtStr [97])))``;
   assert_string_prover "string_prove length arithmetic rung"
     (SmtStringProve.length_arith_prove intLib.ARITH_PROVE)
     ``smtstr_len (smtstr_concat s t) >=
       smtstr_len s``)

fun string_prove_symbolic_rung_success () =
  let
    fun direct name tm =
      assert_string_prover name
        SmtStringProve.symbolic_string_prove tm
    (* Character variables carry the SMT-LIB code-point bound: ':smtstr' is
       a bounded carrier, so 'seq_unit c' only denotes a one-character
       string when 'c' is a code point.  On the replay path the bound comes
       from a literal or from 'seq_nth_i_bound'. *)
    val concat_goal =
      ``c <= 196607 /\ d <= 196607 /\
        smtstr_concat p (smtstr_concat (seq_unit c) q) =
          seq_unit d ==> d = c``
  in
    direct "string symbolic concat" concat_goal;
    direct "string symbolic concat singleton-left"
      ``c <= 196607 /\ d <= 196607 /\
        seq_unit d =
          smtstr_concat p (smtstr_concat (seq_unit c) q) ==> d = c``;
    direct "string symbolic concat applied witnesses"
      ``(97:num) <= 196607 /\
        middle_char x (seq_unit 97) <= 196607 /\
        seq_unit 97 =
          smtstr_concat (prefix_part x (seq_unit 97))
            (smtstr_concat
              (seq_unit (middle_char x (seq_unit 97)))
              (suffix_part x (seq_unit 97))) ==>
        97 = middle_char x (seq_unit 97)``;
    direct "string symbolic shared concat prefix"
      ``c <= 196607 /\ d <= 196607 /\ e <= 196607 /\
        seq_eq s
          (smtstr_concat
            (seq_unit (seq_nth_i s 0)) (seq_tail s 0)) /\
        s = smtstr_concat p (smtstr_concat (seq_unit c) q) /\
        smtstr_concat p (smtstr_concat (seq_unit d) r) = seq_unit e ==>
        seq_nth_i s 0 = c``;
    direct "string symbolic prefix"
      ``c <= 196607 /\
        seq_eq s
          (smtstr_concat
            (seq_unit (seq_nth_i s 0)) (seq_tail s 0)) /\
        smtstr_prefixof s (seq_unit c) ==>
        c = seq_nth_i s 0``;
    direct "string symbolic suffix"
      ``smtstr_suffixof s t /\ smtstr_suffixof t u ==>
        smtstr_suffixof s u``;
    direct "string symbolic contains"
      ``smtstr_contains s t /\ smtstr_contains t u ==>
        smtstr_contains s u``;
    Profile.reset_all ();
    assert_string_prover "string symbolic full ladder"
      (SmtStringProve.string_prove intLib.ARITH_PROVE) concat_goal;
    assert (profile_call_count "string(rung:4/symbolic)" > 0,
      "symbolic string goal did not reach rung 4");
    assert (profile_call_count "string(rung:7/unsupported)" = 0,
      "symbolic string goal fell through to the unsupported rung")
  end

fun string_prove_regex_rung_success () =
  let
    fun direct name tm =
      assert_string_prover name SmtStringProve.regex_prove tm
    val range = ``reglan_range (seq_unit 97) (seq_unit 122)``
    val loop13 =
      ``reglan_loop (reglan_to_re (seq_unit 97)) 1 3``
    val comp =
      ``reglan_comp (reglan_to_re (seq_unit 97))``
    val inter =
      ``reglan_inter
          (reglan_range (seq_unit 97) (seq_unit 122))
          (reglan_comp (reglan_to_re (seq_unit 109)))``
    val nullable =
      ``reglan_loop
          (reglan_union
            (reglan_to_re (seq_unit 97)) (reglan_to_re (SmtStr [])))
          1 2``
  in
    direct "regex membership bridge"
      ``~smt_in_re x ^range \/ aut_accept x 0 ^range``;
    direct "regex range length"
      ``aut_accept x 0 ^range ==>
        smtstr_len x >= 1``;
    direct "regex range transition"
      ``~aut_accept x 0 ^range \/
        smtstr_len x <= 0 \/
        (seq_nth_i x 0 <= 122 /\ 97 <= seq_nth_i x 0 /\
         aut_accept x 1 (reglan_to_re (SmtStr [])))``;
    direct "regex bounded-loop transition zero"
      ``~aut_accept x 0 ^loop13 \/
        smtstr_len x <= 0 \/
        (seq_nth_i x 0 = 97 /\
         aut_accept x 1
           (reglan_loop (reglan_to_re (seq_unit 97)) 0 2))``;
    direct "regex bounded-loop length"
      ``aut_accept x 0 ^loop13 ==>
        smtstr_len x >= 1``;
    direct "regex bounded-loop transition one"
      ``~aut_accept x 1
          (reglan_loop (reglan_to_re (seq_unit 97)) 0 2) \/
        smtstr_len x <= 1 \/
        (seq_nth_i x 1 = 97 /\
         aut_accept x 2
           (reglan_loop (reglan_to_re (seq_unit 97)) 0 1))``;
    direct "regex bounded-loop transition two"
      ``~aut_accept x 2
          (reglan_loop (reglan_to_re (seq_unit 97)) 0 1) \/
        smtstr_len x <= 2 \/
        (seq_nth_i x 2 = 97 /\
         aut_accept x 3 (reglan_to_re (SmtStr [])))``;
    direct "regex empty terminal"
      ``~aut_accept x 3 (reglan_to_re (SmtStr [])) \/
        smtstr_len x <= 3 \/ F``;
    direct "regex complement transition"
      ``~aut_accept x 0 ^comp \/
        smtstr_len x <= 0 \/
        (seq_nth_i x 0 <> 97 \/
         aut_accept x 1 (reglan_plus reglan_allchar))``;
    direct "regex complement residual length"
      ``aut_accept x 1 (reglan_plus reglan_allchar) ==>
        smtstr_len x >= 2``;
    direct "regex complement-range transition"
      ``~aut_accept x 0
          (reglan_comp
            (reglan_range (seq_unit 97) (seq_unit 122))) \/
        smtstr_len x <= 0 \/
        (seq_nth_i x 0 < 97 \/ 122 < seq_nth_i x 0 \/
         aut_accept x 1 (reglan_plus reglan_allchar))``;
    direct "regex intersection transition"
      ``~aut_accept x 0 ^inter \/
        smtstr_len x <= 0 \/
        (97 <= seq_nth_i x 0 /\ seq_nth_i x 0 <= 122 /\
         seq_nth_i x 0 <> 109 /\
         aut_accept x 1 (reglan_to_re (SmtStr [])))``;
    direct "regex nullable-loop transition zero"
      ``~aut_accept x 0 ^nullable \/
        smtstr_len x <= 0 \/
        (seq_nth_i x 0 = 97 /\
         aut_accept x 1
           (reglan_loop
             (reglan_union
               (reglan_to_re (seq_unit 97))
               (reglan_to_re (SmtStr [])))
             0 1))``;
    direct "regex nullable-loop transition one"
      ``~aut_accept x 1
          (reglan_loop
            (reglan_union
              (reglan_to_re (seq_unit 97))
              (reglan_to_re (SmtStr [])))
            0 1) \/
        smtstr_len x <= 1 \/
        (seq_nth_i x 1 = 97 /\
         aut_accept x 2 (reglan_to_re (SmtStr [])))``;
    direct "regex nullable-loop terminal"
      ``~aut_accept x 2 (reglan_to_re (SmtStr [])) \/
        smtstr_len x <= 2 \/ F``;
    assert_string_prover "regex ground derivative evaluation"
      (SmtStringProve.string_prove intLib.ARITH_PROVE)
      ``smt_in_re (SmtStr [97]) ^range /\
        smt_in_re (SmtStr [97; 97]) ^nullable /\
        smt_in_re (SmtStr [98]) ^comp``;
    Profile.reset_all ();
    assert_string_prover "regex full ladder"
      (SmtStringProve.string_prove intLib.ARITH_PROVE)
      ``~smt_in_re x ^range \/ aut_accept x 0 ^range``;
    assert (profile_call_count "string(rung:5/regex)" > 0,
      "regex goal did not reach rung 5");
    assert (profile_call_count "string(rung:7/unsupported)" = 0,
      "regex goal fell through to the unsupported rung")
  end

fun string_prove_structured_failures () =
  let
    fun expect_message name expected thunk =
      (ignore (thunk ());
       die ("FAIL: unsupported " ^ name ^ " replayed successfully"))
      handle Feedback.HOL_ERR holerr =>
        let val msg = Feedback.message_of holerr
        in assert (String.isSubstring expected msg,
          name ^ " diagnostic did not include '" ^ expected ^ "': " ^ msg)
        end
  in
    expect_message "string th-lemma" "theory=seq"
      (fn () =>
        SmtStringProve.string_prove intLib.ARITH_PROVE ``F``);
    expect_message "corpus-shaped string th-lemma" "theory=seq"
      (fn () =>
        SmtStringProve.string_prove intLib.ARITH_PROVE
          ``~(smtstr_len x <= 1) \/
            smtstr_to_int x = seq_stoi x 0``);
    expect_message "proof-local prefix witness" "theory=seq"
      (fn () =>
        SmtStringProve.string_prove intLib.ARITH_PROVE
          ``smtstr_prefixof x (seq_unit c) ==>
            seq_unit c =
              smtstr_concat x (suffix_witness x (seq_unit c))``);
    expect_message "char th-lemma" "theory=char"
      (fn () => SmtStringProve.char_prove ``F``);
    expect_message "non-string Seq th-lemma"
      "theory:Z3_Extensions:seq-set-bag:checked-replay"
      (fn () =>
        SmtStringProve.string_prove intLib.ARITH_PROVE
          ``(xs : bool list) = xs``)
  end

fun z3_string_th_lemma_dispatch_success () =
let
  val proforma = replay_z3_proof_string
    "((declare-fun x () String) (declare-fun y () String) \
    \(declare-fun z () String) (proof ((_ th-lemma seq) \
    \(= (str.++ (str.++ x y) z) (str.++ x (str.++ y z))))))"
  val ground = replay_z3_proof_string
    "((proof ((_ th-lemma string) (= (str.to_int \"12\") 12))))"
  val alias = replay_z3_proof_string
    "((proof ((_ th-lemma regexp) true)))"
in
  assert (Thm.concl proforma ~~
      ``smtstr_concat (smtstr_concat x y) z =
        smtstr_concat x (smtstr_concat y z)``,
    "th-lemma-seq did not route through the proforma rung");
  assert (Thm.concl ground ~~
      ``smtstr_to_int (SmtStr [49; 50]) = 12``,
    "th-lemma-string alias did not route through ground evaluation");
  assert (Thm.concl alias ~~ ``T``,
    "th-lemma-regexp alias did not route through the seq handler");
  Library.check_oracle_tags "Z3 seq proforma dispatch" proforma;
  Library.check_oracle_tags "Z3 string ground dispatch" ground;
  Library.check_oracle_tags "Z3 regexp alias dispatch" alias
end

fun z3_char_th_lemma_bit_decomposition_success () =
let
  fun bit_arguments (0, _) = []
    | bit_arguments (remaining, n) =
        (if Int.mod (n, 2) = 1 then "true" else "false") ::
        bit_arguments (remaining - 1, Int.div (n, 2))
  fun reconstruction_proof n =
    "((proof ((_ th-lemma char) \
    \(= (_ Char " ^ Int.toString n ^ ") \
    \((_ bits2char bits2char) " ^
    String.concatWith " " (bit_arguments (18, n)) ^ ")))))"
  fun check_boundary n =
    let val thm = replay_z3_proof_string (reconstruction_proof n)
    in
      Library.check_oracle_tags
        ("Z3 char boundary " ^ Int.toString n) thm
    end
  val digit_proof =
    "((declare-fun ch () Char) \
    \(proof ((_ th-lemma char) \
    \(= (char.is_digit ch) \
    \   (and (char.<= (_ Char 48) ch) \
    \        (char.<= ch (_ Char 57)))))))"
  val () = Profile.reset_all ()
  val () = List.app check_boundary [0, 127, 196607]
  val digit_thm = replay_z3_proof_string digit_proof
in
  assert (profile_call_count "string(rung:6/char-bitblast)" = 4,
    "char decomposition proofs did not use rung 6 exactly four times");
  assert (profile_call_count "string(rung:7/unsupported)" = 0,
    "char decomposition proofs fell through to unsupported");
  Library.check_oracle_tags "Z3 char.is_digit decomposition" digit_thm
end

fun z3_char_th_lemma_shaped_diagnostics () =
let
  fun expect name proof =
    expect_hol_error_contains name
      "unsupported th-lemma shape: theory=char"
      (fn () => ignore (replay_z3_proof_string proof))
  val comparison =
    replay_z3_proof_string
      "((proof ((_ th-lemma char) \
      \(char.<= (_ Char 0) (_ Char 127)))))"
in
  expect "char bit outside 18-bit decomposition"
    "((proof ((_ th-lemma char) \
    \(not ((_ char.bit char.bit 18) (_ Char 0))))))";
  Library.check_oracle_tags "ground char comparison" comparison
end

fun z3_char_th_lemma_false_diagnostic () =
  expect_hol_error_contains "char th-lemma false"
    "unsupported th-lemma shape: theory=char"
    (fn () => ignore (replay_z3_proof_string
      "((proof ((_ th-lemma char) false)))"))

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

fun z3_rewrite_string_rungs_replay_success () =
let
  val literal = replay_z3_proof_string
    ("((proof (rewrite (= (str.++ (str.++ \"a\" \"b\") \"c\") " ^
     "\"abc\"))))")
  val length = replay_z3_proof_string
    "((proof (rewrite (= (str.len \"abc\") 3))))"
  val regex_literal = replay_z3_proof_string
    ("((proof (rewrite (= (str.to_re (str.++ \"a\" \"b\")) " ^
     "(str.to_re \"ab\")))))")
  val re_comp = replay_z3_proof_string
    ("((proof (rewrite (= (re.diff re.all (str.to_re \"a\")) " ^
     "(re.comp (str.to_re \"a\"))))))")
  (* A general re.diff must keep both operands: only 're.diff re.all r'
     abbreviates to a complement. *)
  val re_diff = replay_z3_proof_string
    ("((proof (rewrite (= (re.diff (str.to_re \"a\") (str.to_re \"b\")) " ^
     "(re.diff (str.to_re \"a\") (str.to_re \"b\"))))))")
  val direct_ground = SmtStringProve.string_rewrite_prove
    ``smtstr_len (SmtStr [97; 98; 99]) = 3``
in
  assert (Thm.concl literal ~~
      ``smtstr_concat
          (smtstr_concat (SmtStr [97]) (SmtStr [98]))
          (SmtStr [99]) = SmtStr [97; 98; 99]``,
    "string literal rewrite returned the wrong equality");
  assert (Thm.concl length ~~
      ``smtstr_len (SmtStr [97; 98; 99]) = 3``,
    "string ground rewrite returned the wrong equality: " ^
    Library.thm_to_string length);
  assert (profile_call_count "rewrite(03.1)(string-ground-eval)" > 0,
    "string rewrite ladder did not use ground evaluation");
  assert (Thm.concl regex_literal ~~
      ``reglan_to_re
          (smtstr_concat (SmtStr [97]) (SmtStr [98])) =
        reglan_to_re (SmtStr [97; 98])``,
    "regex literal rewrite returned the wrong equality: " ^
    Library.thm_to_string regex_literal);
  assert (Thm.concl re_comp ~~
      ``reglan_comp (reglan_to_re (SmtStr [97])) =
        reglan_comp (reglan_to_re (SmtStr [97]))``,
    "re.comp rewrite returned the wrong equality: " ^
    Library.thm_to_string re_comp);
  assert (Thm.concl re_diff ~~
      ``reglan_diff (reglan_to_re (SmtStr [97]))
          (reglan_to_re (SmtStr [98])) =
        reglan_diff (reglan_to_re (SmtStr [97]))
          (reglan_to_re (SmtStr [98]))``,
    "re.diff rewrite dropped its first regex argument: " ^
    Library.thm_to_string re_diff);
  assert (Thm.concl direct_ground ~~
      ``smtstr_len (SmtStr [97; 98; 99]) = 3``,
    "direct string ground rewrite returned the wrong equality");
  Library.check_oracle_tags "Z3 string literal rewrite" literal;
  Library.check_oracle_tags "Z3 string length rewrite" length;
  ()
end

fun z3_rewrite_string_rung_shaped_failure () =
  expect_hol_error_contains "string rewrite shaped failure"
    "string rewrite normalization did not close"
    (fn () => ignore (SmtStringProve.string_rewrite_prove
      ``smtstr_concat x (SmtStr [97]) =
        smtstr_concat x (SmtStr [98])``))

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
  val string_cases = [
    ("sequence",
      "((proof ((_ th-lemma seq eq-propagate 2) false)))",
      "sequence"),
    ("string",
      "((proof ((_ th-lemma string eq-propagate 3) false)))",
      "string"),
    ("regexp",
      "((proof ((_ th-lemma regexp eq-propagate 4) false)))",
      "regexp")
  ]
  fun expect_string_diagnostic (name, proof_text, _) =
    expect_hol_error_contains ("unsupported " ^ name ^ " th-lemma")
      "unsupported th-lemma shape: theory=seq"
      (fn () => ignore (replay_z3_proof_string proof_text))
in
  expect_advanced_th_lemma_diagnostic
    ("floating-point",
      "((proof ((_ th-lemma fp eq-propagate 1) false)))",
      "theory=fp",
      "proof-rule:th-lemma-fp");
  List.app expect_string_diagnostic string_cases
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

fun smt_resource_diagnostic_contract () =
let
  val proof_diagnostic =
    "resource-gated: fp-bitblast; limit=proof-size; " ^
    "observed=16777217 bytes; maximum=16777216 bytes; " ^
    "feature=resource-gate:FloatingPoint:z3-proof-text"
  val time_diagnostic =
    "resource-gated: fp-bitblast; limit=step-time; maximum=10 s; " ^
    "feature=resource-gate:FloatingPoint:comparison-step"
  val term_diagnostic =
    "resource-gated: fp-bitblast; limit=term-size; " ^
    "observed=200001 nodes; maximum=200000 nodes; " ^
    "feature=resource-gate:FloatingPoint:comparison-goal"
  fun expect_gate label expected thunk =
    (thunk ();
     die ("FAIL: " ^ label ^ " did not resource-gate"))
    handle Feedback.HOL_ERR holerr =>
      let val observed = Feedback.message_of holerr
      in
        assert (SmtResource.is_resource_gate holerr,
          label ^ " did not raise the reserved resource diagnostic");
        assert (observed = expected,
          label ^ " diagnostic mismatch\nexpected: " ^ expected ^
          "\nobserved: " ^ observed)
      end
in
  assert (SmtResource.max_z3_proof_bytes = 16777216,
    "Z3 proof-size budget is not 16 MB");
  assert (Time.toSeconds SmtResource.max_bitblast_step_time = 10,
    "bit-blast step-time budget is not 10 seconds");
  assert (SmtResource.max_bitblast_term_nodes = 200000,
    "bit-blast term-size budget is not 200k nodes");
  SmtResource.check_proof_size "z3-proof-text" 16777216;
  SmtResource.check_term_size "comparison-goal" 200000;
  SmtResource.check_bitblast_goal "small-goal" boolSyntax.T;
  expect_gate "proof-size cap" proof_diagnostic (fn () =>
    SmtResource.check_proof_size "z3-proof-text" 16777217);
  expect_gate "term-size cap" term_diagnostic (fn () =>
    SmtResource.check_term_size "comparison-goal" 200001);
  expect_gate "step-time cap" time_diagnostic (fn () =>
    SmtResource.with_bitblast_step_time "comparison-step"
      (fn () => raise Timeout.TIMEOUT Time.zeroTime) ())
end

fun smt_resource_proof_pre_gate_precedes_parser () =
let
  val path = OS.FileSys.tmpName ()
  val block = String.implode (List.tabulate (4096, fn _ => #"("))
  val parser_invoked = ref false
  val expected =
    "resource-gated: fp-bitblast; limit=proof-size; " ^
    "observed=16777217 bytes; maximum=16777216 bytes; " ^
    "feature=resource-gate:FloatingPoint:z3-proof-text"
  fun remove () = OS.FileSys.remove path handle _ => ()
  fun write_oversized_proof () =
    let
      val outstream = TextIO.openOut path
      fun blocks 0 = ()
        | blocks n = (TextIO.output (outstream, block); blocks (n - 1))
    in
      TextIO.output (outstream, "unsat\n");
      blocks 4096;
      TextIO.output (outstream, "x");
      TextIO.closeOut outstream
    end
  fun check_file () =
    let
      val instream = TextIO.openIn path
      fun close () = TextIO.closeIn instream handle _ => ()
      fun check () =
        let
          val (result, proof_start) =
            Z3.is_sat_stream_with_consumed instream
          val () =
            case result of
              SolverSpec.UNSAT NONE => ()
            | _ => die
                "FAIL: synthetic oversized Z3 output did not start with unsat"
        in
          ignore (SmtResource.with_z3_proof_size_gate "z3-proof-text"
            path proof_start instream
            (fn _ => (parser_invoked := true; ())))
        end
    in
      Portable.finally close check ()
    end
  fun run () =
    (write_oversized_proof ();
     check_file ();
     die "FAIL: oversized synthetic proof text passed its pre-gate")
    handle Feedback.HOL_ERR holerr =>
      let val observed = Feedback.message_of holerr
      in
        assert (SmtResource.is_resource_gate holerr,
          "oversized proof raised a non-resource diagnostic: " ^ observed);
        assert (observed = expected,
          "proof pre-gate diagnostic mismatch\nexpected: " ^ expected ^
          "\nobserved: " ^ observed);
        assert (not (!parser_invoked),
          "Z3 proof parser callback ran before the proof-size gate")
      end
in
  Portable.finally remove run ()
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

fun z3_direct_higher_order_replay_success () =
  z3_direct_if_configured (fn () =>
  let
    val goals = [
      ("first-class lambda argument",
        ``(H:(int -> int) -> bool) (\x. x + 1) /\ p ==>
          H (\y. y + 1)``),
      ("lambda equality",
        ``(\x:int. f (g x)) = (\y. f (g y))``),
      ("eta instance", ``(\x:int. f x) = f``),
      ("partial application",
        ``(H:(bool -> int) -> bool) (smtlib_ho_rank2 x) ==>
          H (\p. smtlib_ho_rank2 x p)``)
    ]
    fun check (label, goal) =
      let
        val thm =
          case Z3.Z3_SMT_Prover ([], goal) of
            SolverSpec.UNSAT (SOME thm) => thm
          | SolverSpec.UNSAT NONE =>
              die ("FAIL: " ^ label ^ " returned UNSAT without a theorem")
          | SolverSpec.SAT _ =>
              die ("FAIL: " ^ label ^ " was wrongly reported SAT")
          | SolverSpec.UNKNOWN _ =>
              die ("FAIL: " ^ label ^ " was not proved")
      in
        assert (List.null (Thm.hyp thm),
          label ^ " theorem has unexpected hypotheses");
        assert (Term.aconv (Thm.concl thm) goal,
          label ^ " theorem conclusion does not match its goal");
        Library.check_oracle_tags ("Z3 " ^ label) thm
      end
  in
    List.app check goals
  end)

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
    ("smtlib_string_literal_codec_success",
      smtlib_string_literal_codec_success),
    ("smtlib_string_literal_typecheck_success",
      smtlib_string_literal_typecheck_success),
    ("smtlib_string_literal_out_of_range_diagnostic",
      smtlib_string_literal_out_of_range_diagnostic),
    ("smtlib_indexed_char_out_of_range_diagnostic",
      smtlib_indexed_char_out_of_range_diagnostic),
    ("smtlib_indexed_char_hex_index_success",
      smtlib_indexed_char_hex_index_success),
    ("smtlib_indexed_char_outbound_range_diagnostic",
      smtlib_indexed_char_outbound_range_diagnostic),
    ("smtlib_proof_stream_tokenizer_success",
      smtlib_proof_stream_tokenizer_success),
    ("smtlib_proof_stream_tokenizer_marker_collision",
      smtlib_proof_stream_tokenizer_marker_collision),
    ("smtlib_string_typed_declaration_success",
      smtlib_string_typed_declaration_success),
    ("smtlib_string_typed_binder_success",
      smtlib_string_typed_binder_success),
    ("smtlib_string_typed_reset_assertions_success",
      smtlib_string_typed_reset_assertions_success),
    ("smtlib_string_typed_definitions_success",
      smtlib_string_typed_definitions_success),
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
    ("num_to_int_under_abstraction_success",
      num_to_int_under_abstraction_success),
    ("hol_string_to_smt_conversion_success",
      hol_string_to_smt_conversion_success),
    ("smtfp_carrier_universe_direction_success",
      smtfp_carrier_universe_direction_success),
    ("smtfloat_rounding_conversions_success",
      smtfloat_rounding_conversions_success),
    ("smtfloat_ground_evaluation_success",
      smtfloat_ground_evaluation_success),
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
    ("parse_file_match_binder_surface_sort_success",
      parse_file_match_binder_surface_sort_success),
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
    ("parse_file_define_fun_body_fragment_violation_success",
      parse_file_define_fun_body_fragment_violation_success),
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
    ("smtlib_lambda_abstraction_alpha_success",
      smtlib_lambda_abstraction_alpha_success),
    ("smtlib_lambda_nesting_equivalence_success",
      smtlib_lambda_nesting_equivalence_success),
    ("smtlib_lambda_under_quantifier_success",
      smtlib_lambda_under_quantifier_success),
    ("smtlib_lambda_body_sort_diagnostic",
      smtlib_lambda_body_sort_diagnostic),
    ("smtlib_lambda_surface_syntax_hygiene",
      smtlib_lambda_surface_syntax_hygiene),
    ("smtlib_apply_operators_success",
      smtlib_apply_operators_success),
    ("smtlib_apply_indexed_ambiguity_success",
      smtlib_apply_indexed_ambiguity_success),
    ("smtlib_apply_operator_diagnostics",
      smtlib_apply_operator_diagnostics),
    ("smtlib_apply_operator_metadata_success",
      smtlib_apply_operator_metadata_success),
    ("smtlib_partial_application_success",
      smtlib_partial_application_success),
    ("smtlib_ranked_partial_application_diagnostic",
      smtlib_ranked_partial_application_diagnostic),
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
    ("smtlib_ho_logic_packets_success",
      smtlib_ho_logic_packets_success),
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
    ("smtlib_distinct_translation_success",
      smtlib_distinct_translation_success),
    ("smtlib_datatype_type_translation_success",
      smtlib_datatype_type_translation_success),
    ("smtlib_extended_hol_encoding_records_success",
      smtlib_extended_hol_encoding_records_success),
    ("smtlib_hol_string_injection_translation_success",
      smtlib_hol_string_injection_translation_success),
    ("smtlib_native_string_translation_success",
      smtlib_native_string_translation_success),
    ("smtlib_native_string_sort_propagation_success",
      smtlib_native_string_sort_propagation_success),
    ("smtlib_native_string_carrier_success",
      smtlib_native_string_carrier_success),
    ("smtlib_higher_order_translation_abstraction_success",
      smtlib_higher_order_translation_abstraction_success),
    ("smtlib_ho_parser_dict_currying_success",
      smtlib_ho_parser_dict_currying_success),
    ("smtlib_regime_trigger_success",
      smtlib_regime_trigger_success),
    ("smtlib_driver_regime_selection_success",
      smtlib_driver_regime_selection_success),
    ("smtlib_standard27_translation_success",
      smtlib_standard27_translation_success),
    ("smtlib_z3_lambda_array_translation_success",
      smtlib_z3_lambda_array_translation_success),
    ("smtlib_fo_emission_golden_success",
      smtlib_fo_emission_golden_success),
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
    ("cpc_string_registry_and_literal_parser_success",
      cpc_string_registry_and_literal_parser_success),
    ("cpc_proof_replay_string_rules_success",
      cpc_proof_replay_string_rules_success),
    ("cpc_proof_replay_string_obligation_diagnostic",
      cpc_proof_replay_string_obligation_diagnostic),
    ("cpc_proof_replay_string_premise_hypotheses",
      cpc_proof_replay_string_premise_hypotheses),
    ("cpc_proof_parser_lambda_inline_var_apply_success",
      cpc_proof_parser_lambda_inline_var_apply_success),
    ("cpc_proof_replay_ho_conversion_rules_success",
      cpc_proof_replay_ho_conversion_rules_success),
    ("cpc_proof_replay_ho_cong_and_ite_success",
      cpc_proof_replay_ho_cong_and_ite_success),
    ("cpc_proof_replay_ho_cong_nary_success",
      cpc_proof_replay_ho_cong_nary_success),
    ("cpc_proof_replay_ho_rare_rewrites_success",
      cpc_proof_replay_ho_rare_rewrites_success),
    ("cpc_proof_parser_declarations_success",
      cpc_proof_parser_declarations_success),
    ("cpc_proof_parser_totalized_arithmetic_success",
      cpc_proof_parser_totalized_arithmetic_success),
    ("cpc_proof_parser_totalized_arithmetic_diagnostic",
      cpc_proof_parser_totalized_arithmetic_diagnostic),
    ("cpc_totalized_outbound_exclusions_success",
      cpc_totalized_outbound_exclusions_success),
    ("cpc_totalized_replay_success", cpc_totalized_replay_success),
    ("cpc_proof_parser_singleton_premise_success",
      cpc_proof_parser_singleton_premise_success),
    ("cpc_proof_parser_version_resolution_success",
      cpc_proof_parser_version_resolution_success),
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
    ("cpc_cache_repeated_conclusion_bypasses_handler_success",
      cpc_cache_repeated_conclusion_bypasses_handler_success),
    ("cpc_cache_popped_scope_is_rejected_success",
      cpc_cache_popped_scope_is_rejected_success),
    ("cpc_cache_prefers_derived_over_assumption_success",
      cpc_cache_prefers_derived_over_assumption_success),
    ("cpc_cache_omitted_conclusion_bypasses_success",
      cpc_cache_omitted_conclusion_bypasses_success),
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
    ("z3_proof_parser_verbatim_lambda_binding_success",
      z3_proof_parser_verbatim_lambda_binding_success),
    ("z3_proof_parser_structures_proof_bind_success",
      z3_proof_parser_structures_proof_bind_success),
    ("z3_proof_parser_erases_inert_proof_bind_success",
      z3_proof_parser_erases_inert_proof_bind_success),
    ("z3_proof_bind_replay_success",
      z3_proof_bind_replay_success),
    ("z3_proof_bind_empty_annotation_replay_success",
      z3_proof_bind_empty_annotation_replay_success),
    ("z3_proof_parser_th_lemma_metadata_success",
      z3_proof_parser_th_lemma_metadata_success),
    ("z3_proof_parser_advanced_th_lemma_metadata_success",
      z3_proof_parser_advanced_th_lemma_metadata_success),
    ("z3_proof_parser_datatype_th_lemma_metadata_success",
      z3_proof_parser_datatype_th_lemma_metadata_success),
    ("z3_proof_parser_unknown_rule_diagnostic",
      z3_proof_parser_unknown_rule_diagnostic),
    ("z3_proof_parser_version_resolution_success",
      z3_proof_parser_version_resolution_success),
    ("z3_proof_parser_rule_name_term_boundary",
      z3_proof_parser_rule_name_term_boundary),
    ("z3_proof_parser_is_int_translation_collision_success",
      z3_proof_parser_is_int_translation_collision_success),
    ("z3_proof_parser_string_internal_symbols_success",
      z3_proof_parser_string_internal_symbols_success),
    ("z3_proof_parser_char_th_lemma_index_success",
      z3_proof_parser_char_th_lemma_index_success),
    ("benchmark_rejects_z3_string_internal_symbols",
      benchmark_rejects_z3_string_internal_symbols),
    ("z3_beta_eta_replay_rungs_success",
      z3_beta_eta_replay_rungs_success),
    ("z3_beta_eta_replay_rungs_shaped_failure",
      z3_beta_eta_replay_rungs_shaped_failure),
    ("z3_rewrite_beta_eta_abs_rungs_success",
      z3_rewrite_beta_eta_abs_rungs_success),
    ("z3_rewrite_abs_rung_shaped_failure",
      z3_rewrite_abs_rung_shaped_failure),
    ("z3_abs_congruence_replay_rung_success",
      z3_abs_congruence_replay_rung_success),
    ("z3_abs_congruence_replay_rung_shaped_failure",
      z3_abs_congruence_replay_rung_shaped_failure),
    ("z3_lambda_intro_def_replay_success",
      z3_lambda_intro_def_replay_success),
    ("z3_lambda_intro_def_replay_shaped_failure",
      z3_lambda_intro_def_replay_shaped_failure),
    ("z3_proof_bind_consumers_replay_success",
      z3_proof_bind_consumers_replay_success),
    ("z3_proof_bind_quant_intro_binder_annotation_ignored",
      z3_proof_bind_quant_intro_binder_annotation_ignored),
    ("z3_proof_bind_nnf_pos_unliftable_premise_success",
      z3_proof_bind_nnf_pos_unliftable_premise_success),
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
    ("string_prove_ladder_rungs_success",
      string_prove_ladder_rungs_success),
    ("string_prove_symbolic_rung_success",
      string_prove_symbolic_rung_success),
    ("string_prove_regex_rung_success",
      string_prove_regex_rung_success),
    ("string_prove_structured_failures",
      string_prove_structured_failures),
    ("z3_string_th_lemma_dispatch_success",
      z3_string_th_lemma_dispatch_success),
    ("z3_char_th_lemma_bit_decomposition_success",
      z3_char_th_lemma_bit_decomposition_success),
    ("z3_char_th_lemma_shaped_diagnostics",
      z3_char_th_lemma_shaped_diagnostics),
    ("z3_char_th_lemma_false_diagnostic",
      z3_char_th_lemma_false_diagnostic),
    ("z3_rewrite_datatype_rung_replay_success",
      z3_rewrite_datatype_rung_replay_success),
    ("z3_rewrite_string_rungs_replay_success",
      z3_rewrite_string_rungs_replay_success),
    ("z3_rewrite_string_rung_shaped_failure",
      z3_rewrite_string_rung_shaped_failure),
    ("z3_th_lemma_advanced_unsupported_diagnostic",
      z3_th_lemma_advanced_unsupported_diagnostic),
    ("z3_proof_replay_failure_diagnostic",
      z3_proof_replay_failure_diagnostic),
    ("z3_proof_replay_malformed_premise_diagnostics",
      z3_proof_replay_malformed_premise_diagnostics),
    ("z3_tac_oracle_tag_gate_rejects_oracle_thm",
      z3_tac_oracle_tag_gate_rejects_oracle_thm),
    ("smt_resource_diagnostic_contract",
      smt_resource_diagnostic_contract),
    ("smt_resource_proof_pre_gate_precedes_parser",
      smt_resource_proof_pre_gate_precedes_parser),
    ("z3_reconstructed_theorem_contract_success",
      z3_reconstructed_theorem_contract_success),
    ("z3_reconstructed_theorem_contract_rejects_bad_shape",
      z3_reconstructed_theorem_contract_rejects_bad_shape),
    ("z3_direct_higher_order_replay_success",
      z3_direct_higher_order_replay_success),
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
