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

fun parse_file_datatype_unsupported_diagnostic () =
  let
    val _ =
      parse_smtlib_assertions
        ("(set-logic QF_UF)\n" ^
         "(declare-datatypes ((Tree 1) (Forest 1)) " ^
         "((par (T) ((leaf (value T)))) (par (T) ((empty)))))\n" ^
         "(exit)\n")
  in
    die "legacy benchmark parser accepted mutual datatype declarations"
  end
  handle Feedback.HOL_ERR holerr =>
    let val msg = Feedback.message_of holerr
    in
      assert (contains "unsupported command 'declare-datatypes'" msg,
        "datatype diagnostic was not explicit: " ^ msg)
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
        SmtLib_Parser.QueryCheckSat assumptions =>
          List.length assumptions = 1 andalso
          List.exists (term_is_var_named "a") assumptions
      | _ => false) queries,
    "check-sat-assuming assumptions were not preserved")
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
  fun require_logic logic =
    let
      val _ = SmtLib_Logics.parsedicts_of_logic logic
      val metadata = SmtLib_Logics.metadata_of_logic logic
    in
      assert (not (List.null metadata),
        "logic metadata was empty for " ^ logic)
    end
in
  List.app require_logic logics
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
    ("parse_file_datatype_unsupported_diagnostic",
      parse_file_datatype_unsupported_diagnostic),
    ("parse_file_datatype_dictionary_success",
      parse_file_datatype_dictionary_success),
    ("parse_file_echo_success", parse_file_echo_success),
    ("parse_file_push_pop_assertion_scoping",
      parse_file_push_pop_assertion_scoping),
    ("parse_file_push_pop_declaration_scoping",
      parse_file_push_pop_declaration_scoping),
    ("parse_file_reset_assertions_state", parse_file_reset_assertions_state),
    ("parse_file_reset_state", parse_file_reset_state),
    ("parse_file_query_commands_success", parse_file_query_commands_success),
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
      smtlib_scoped_logic_dictionary_success)
  ]
  val () = List.app run_test tests
  val () = print "\ndone, all unit tests successful.\n"
in
  ()
end

end (* struct *)
