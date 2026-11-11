(* Parsing cvc5's native CPC proof scripts. *)

structure CPC_ProofParser =
struct

local
  open CPC_Proof smtfloatReplayWordTheory SmtLib_GraphTranslation

  val ERR = Feedback.mk_HOL_ERR "CPC_ProofParser"

  structure F = SmtLib_GraphFrontend
  structure P = SmtLib_Parser
  structure G = SmtReplayGraph
  structure B = SmtLib_GraphBackend
  structure C = SmtLib_ConstructorSyntax
  type dicts = SmtLib_Parser.dicts

  val term_intern_bucket_count = 4093
  val cpc_term_intern = ref
    (Array.array (term_intern_bucket_count, [] : Term.term list))

  fun term_intern_hash term =
    let
      fun string_hash string =
        let
          fun loop index hash =
            if index = String.size string then hash
            else loop (index + 1)
              ((hash * 33 + Char.ord (String.sub (string, index))) mod
               term_intern_bucket_count)
        in loop 0 5381 end
      fun head_hash tm =
        if Term.is_var tm then string_hash (#1 (Term.dest_var tm))
        else if Term.is_const tm then
          string_hash (#Name (Term.dest_thy_const tm))
        else if Term.is_comb tm then 17
        else if Term.is_abs tm then 19
        else 23
      fun bounded 0 tm = head_hash tm
        | bounded depth tm =
            if Term.is_comb tm then
              let val (operator, operand) = Term.dest_comb tm in
                (bounded (depth - 1) operator * 37 +
                 bounded (depth - 1) operand * 17 + 3) mod
                  term_intern_bucket_count
              end
            (* A bucket hash is not an abstraction observation. Opening
               here can traverse/rebuild a shared body on stock kernels. *)
            else head_hash tm
    in bounded 6 term end

  fun intern_cpc_term term =
    let
      (* Applications are interned bottom-up by their canonical children.
         Abstractions remain opaque: CPC alpha_equiv mappings name their
         source binders, so alpha-equivalent abstractions are not
         interchangeable parser occurrences.  Do not open them merely to
         recover sharing, or collect them in one quadratic-search bucket. *)
      fun same_candidate saved candidate =
        Portable.pointer_eq (saved, candidate) orelse
        if Term.is_comb saved andalso Term.is_comb candidate then
          let
            val (saved_operator, saved_operand) = Term.dest_comb saved
            val (operator, operand) = Term.dest_comb candidate
          in
            Portable.pointer_eq (saved_operator, operator) andalso
            Portable.pointer_eq (saved_operand, operand)
          end
        else if Term.is_var saved andalso Term.is_var candidate then
          let
            val (saved_name, saved_type) = Term.dest_var saved
            val (name, ty) = Term.dest_var candidate
          in
            saved_name = name andalso Type.compare (saved_type, ty) = EQUAL
          end
        else if Term.is_const saved andalso Term.is_const candidate then
          Term.same_const saved candidate andalso
          Type.compare (Term.type_of saved, Term.type_of candidate) = EQUAL
        else false
      fun lookup bucket candidate = List.find
        (fn saved => same_candidate saved candidate)
        (Array.sub (!cpc_term_intern, bucket))
      fun insert bucket candidate =
        let
          val entries = Array.sub (!cpc_term_intern, bucket)
        in
          Array.update (!cpc_term_intern, bucket, candidate :: entries);
          candidate
        end
      fun intern candidate =
        if Term.is_abs candidate then candidate
        else let val bucket = term_intern_hash candidate in
          case List.find (fn saved => Portable.pointer_eq (saved, candidate))
              (Array.sub (!cpc_term_intern, bucket)) of
            SOME saved => saved
          | NONE =>
            if Term.is_comb candidate then
              let
                val (operator, operand) = Term.dest_comb candidate
                val operator' = intern operator
                val operand' = intern operand
                val rebuilt =
                  if Portable.pointer_eq (operator, operator') andalso
                     Portable.pointer_eq (operand, operand') then candidate
                  else Term.mk_comb (operator', operand')
                (* Compute a candidate's hash once for both lookup and
                   insertion; child canonicalization needs a new hash only
                   when it actually rebuilt the candidate. *)
                val rebuilt_bucket =
                  if Portable.pointer_eq (candidate, rebuilt) then bucket
                  else term_intern_hash rebuilt
              in
                case lookup rebuilt_bucket rebuilt of
                  SOME saved => saved
                | NONE => insert rebuilt_bucket rebuilt
              end
            else
              case lookup bucket candidate of
                SOME saved => saved
              | NONE => insert bucket candidate
        end
    in intern term end

  (* Intern only this shell, never canonicalizing or rebuilding children.
     The caller must admit leaf types before lookup: exact type comparison
     below is not itself resource-bounded.  The existing bounded bucket hash
     is shared with intern_cpc_term; abstractions remain entirely opaque. *)
  fun intern_cpc_shell candidate =
    if Term.is_abs candidate then candidate
    else
      let
        fun same_candidate saved =
          Portable.pointer_eq (saved, candidate) orelse
          if Term.is_comb saved andalso Term.is_comb candidate then
            let
              val (saved_operator, saved_operand) = Term.dest_comb saved
              val (operator, operand) = Term.dest_comb candidate
            in
              Portable.pointer_eq (saved_operator, operator) andalso
              Portable.pointer_eq (saved_operand, operand)
            end
          else if Term.is_var saved andalso Term.is_var candidate then
            let
              val (saved_name, saved_type) = Term.dest_var saved
              val (name, ty) = Term.dest_var candidate
            in
              saved_name = name andalso Type.compare (saved_type, ty) = EQUAL
            end
          else if Term.is_const saved andalso Term.is_const candidate then
            Term.same_const saved candidate andalso
            Type.compare (Term.type_of saved, Term.type_of candidate) = EQUAL
          else false
        val bucket = term_intern_hash candidate
        val entries = Array.sub (!cpc_term_intern, bucket)
      in
        case List.find same_candidate entries of
          SOME saved => saved
        | NONE =>
            (Array.update (!cpc_term_intern, bucket, candidate :: entries);
             candidate)
      end

  fun intern_located ({term, provenance} : located_term) =
    {term = intern_cpc_term term, provenance = provenance}

  (* @list is CPC's compact representation for a list of binders or
     resolution annotations.  It is not an SMT-LIB term, so retain only the
     binder-list payload needed when it is referenced by a later quantifier. *)
  val cpc_list_definitions = ref (Redblackmap.mkDict String.compare)
  val cpc_list_names = ref ([] : string list)

  (* Definitions are syntax aliases.  Keep their exact occurrence tree so an
     alias use retains CPC's operand boundaries without consulting HOL-term
     identity.  This dictionary is used only while parsing the current proof;
     every command receives its own copied provenance value. *)
  val cpc_term_provenances = ref
    (Redblackmap.mkDict String.compare :
      (string, term_provenance) Redblackmap.dict)

  (* HOL represents a flat source forall block and the corresponding nested
     source foralls by the same term.  Record every parsed source occurrence
     by alpha-equivalent semantic term, retaining every distinct immediate
     block size.  A term with more than one size is deliberately ambiguous:
     the term-only parameterized-skolem callback must then fail closed. *)
  val cpc_forall_blocks = ref
    ([] : (Term.term * int list) list)

  fun add_distinct_int value values =
    if List.exists (Lib.equal value) values then values else value :: values

  fun record_forall_block (term, size) =
    let
      fun record [] = [(term, [size])]
        | record ((candidate, sizes) :: rest) =
            if Term.aconv candidate term then
              (candidate, add_distinct_int size sizes) :: rest
            else (candidate, sizes) :: record rest
    in
      cpc_forall_blocks := record (!cpc_forall_blocks)
    end

  fun record_cpc_binder_block (name, size, term) =
    if name = "forall" then record_forall_block (term, size) else ()

  (* Quoting is lexical for ordinary user symbols, but quoted spellings of
     syntax and baseline theory names denote separate user symbols.  Keep the
     baseline, source/query, and proof-declaration provenances separate.
     Thus a proof cannot shadow a builtin or duplicate its own declaration. *)
  val cpc_reserved_symbols = ref (HOLset.empty String.compare)
  val cpc_source_term_symbols = ref (HOLset.empty String.compare)
  val cpc_source_sort_symbols = ref (HOLset.empty String.compare)
  val cpc_proof_term_symbols = ref (HOLset.empty String.compare)
  val cpc_proof_sort_symbols = ref (HOLset.empty String.compare)

  fun set_member set item = HOLset.member (set, item)

  fun quoted_symbol_key token =
    case SmtLib_Parser.proof_quoted_symbol_token token of
      SOME name =>
        if set_member (!cpc_reserved_symbols) name then token else name
    | NONE => token

  (* Provenance follows the same semantic key as term elaboration.  In
     particular, an ordinary user symbol has one entry whether cvc5 prints
     it as [foo] or [|foo|]. *)
  fun provenance_key name = quoted_symbol_key name

  fun add_term_provenance name provenance =
    cpc_term_provenances := Redblackmap.insert
      (!cpc_term_provenances, provenance_key name, provenance)

  fun lookup_term_provenance name =
    SOME (Redblackmap.find (!cpc_term_provenances, provenance_key name))
    handle Redblackmap.NotFound => NONE

  fun add_cpc_list name terms =
    let val key = provenance_key name in
      cpc_list_definitions := Redblackmap.insert
        (!cpc_list_definitions, key, terms);
      cpc_list_names := key :: !cpc_list_names
    end

  fun lookup_cpc_list name =
    SOME (Redblackmap.find
      (!cpc_list_definitions, provenance_key name))
    handle Redblackmap.NotFound => NONE

  val cpc_fp_private_parse_avoid = ref ([] : Term.term list)
  val cpc_fp_private_allocated = ref Term.empty_varset
  val cpc_source_variables = ref (Redblackmap.mkDict Term.var_compare)
  val cpc_source_images = ref Term.empty_varset
  val cpc_reserved_source_scope = ref ([] : Term.term list)

  (* A proof-local @var/declaration/binder can be printed AFTER a private
     allocation with that allocation's exact HOL descriptor. Preserve the
     ordinary descriptor's identity in a separate namespace in either
     declaration order. Original query variables are already reserved by
     the Source scope and therefore never require renaming here. Store all
     ordinary identities (not just collisions), so a later descriptor also
     cannot alias an earlier collision's renamed image. *)
  fun cpc_source_variable specification =
    let val original = Term.mk_var specification in
      case Redblackmap.peek (!cpc_source_variables, original) of
        SOME variable => variable
      | NONE =>
          let
            val occupied = !cpc_fp_private_parse_avoid
            val variable =
              if HOLset.member (!cpc_fp_private_allocated, original) orelse
                 HOLset.member (!cpc_source_images, original)
              then Term.variant occupied original
              else original
            val _ = cpc_source_variables := Redblackmap.insert
              (!cpc_source_variables, original, variable)
            val _ = cpc_source_images :=
              HOLset.add (!cpc_source_images, variable)
            val _ = cpc_fp_private_parse_avoid := variable :: occupied
          in variable end
    end

  val cpc_cfg : SmtLib_Parser.parser_cfg = {
    mk_let_bindings = SmtLib_Parser.smtlib_mk_let_bindings,
    mk_let = SmtLib_Parser.smtlib_mk_let,
    mk_bound_var = cpc_source_variable,
    lookup_binder_list = lookup_cpc_list,
    record_binder_block = record_cpc_binder_block,
    symbol_key = quoted_symbol_key,
    type_symbol_key = quoted_symbol_key,
    parse_choice = false,
    parse_lambda = true
  }

  fun cpc_symbol_key where_ token =
    case SmtLib_Parser.proof_string_token token of
      SOME _ => raise ERR where_ "string literal used as a symbol"
    | NONE => quoted_symbol_key token

  fun cpc_semantic_token token =
    case SmtLib_Parser.proof_string_token token of
      SOME _ => token
    | NONE => quoted_symbol_key token

  fun cpc_get_token get_token () = cpc_semantic_token (get_token ())

  fun parse_cpc_type get_token tydict =
    SmtLib_Parser.parse_type (cpc_get_token get_token) tydict

  fun parse_cpc_type_list get_token tydict =
    SmtLib_Parser.parse_type_list (cpc_get_token get_token) tydict

  fun cpc_symbol_name where_ token =
    SmtLib_Parser.proof_symbol_text (cpc_symbol_key where_ token)

  fun cpc_id_initial c =
    ((#"a" <= c andalso c <= #"z") orelse
     (#"A" <= c andalso c <= #"Z")) orelse
    List.exists (Lib.equal c)
      [#"~", #"!", #"@", #"$", #"%", #"^", #"&", #"*", #"_",
       #"-", #"+", #"=", #"<", #">", #".", #"?", #"/"]

  fun cpc_simple_symbol text =
    String.size text > 0 andalso
    cpc_id_initial (String.sub (text, 0)) andalso
    List.all (fn c => cpc_id_initial c orelse Char.isDigit c)
      (String.explode text)

  (* CPC command and premise IDs use the @-prefixed identifier production,
     not the wider atom production and never the String-token production.
     Apply the ordinary symbol key only after checking the original token
     kind and spelling.  Thus [@p] and [|@p|] share a key unless [@p] is a
     reserved symbol, whose quoted spelling remains a distinct symbol. *)
  fun cpc_id_key where_ description token =
    case SmtLib_Parser.proof_string_token token of
      SOME _ => raise ERR where_
        ("string literal is not a valid CPC " ^ description)
    | NONE =>
        let val text = SmtLib_Parser.proof_symbol_text token in
          if cpc_simple_symbol text andalso String.size text > 1 andalso
             String.sub (text, 0) = #"@"
          then quoted_symbol_key token
          else raise ERR where_
            ("invalid CPC " ^ description ^ " '" ^ text ^ "'")
        end

  (* cvc5's @var production is the one CPC context whose name is serialized
     as an SMT-LIB String token.  Decode it to the corresponding HOL name;
     no ordinary identifier position receives this exception. *)
  fun cpc_var_name token =
    case SmtLib_Parser.proof_string_token token of
      SOME name => name
    | NONE => SmtLib_Parser.proof_symbol_text token

  (* Source terms are supplied by the caller, not recovered by probing
     dictionary callbacks. Keep this scope separate from per-parse avoids.
     Ordinary non-FP parsing does no source traversal: each scope collects
     and memoizes its variables only when a private marker is requested. *)
  val cpc_fp_private_source_avoid =
    ref ((fn () => []) : unit -> Term.term list)

  fun cpc_fp_private_source_vars terms =
    let
      val variables = ref Term.empty_varset
      fun inspect term =
        if Term.is_var term then
          variables := HOLset.add (!variables, term)
        else ()
      (* These are exactly the permitted legacy proof Sources, already
         subject to this same binder-opening policy during final marker
         exclusion. Reuse its prospective raw admission, never open a large
         opaque binder to obtain freshness metadata. Bound names need not
         be reserved: kernel instantiation is capture-avoiding. *)
      (* Same DAG metric/limit and diagnostic as legacy final Source marker
         exclusion; do not introduce a new freshness admission policy. *)
      fun collect term =
        if Term.is_var term then inspect term
        else
          let val scan = SmtResource.bounded_structure_with_inspector
                inspect SmtResource.max_bitblast_term_nodes term
          in if #complete scan then () else
            raise Feedback.mk_HOL_ERR "CPC_ProofReplay"
              "instantiate_cpc_fp_unbound_markers"
              "private FP marker scan exceeded the DAG resource limit"
          end
      val _ = List.app collect terms
    in HOLset.listItems (!variables) end

  fun with_cpc_fp_private_source_terms terms action input =
    let
      val saved = !cpc_fp_private_source_avoid
      val cached = ref NONE
      fun avoid () =
        case !cached of
          SOME variables => variables
        | NONE =>
            let
              val variables = cpc_fp_private_source_vars terms @ saved ()
              val _ = cached := SOME variables
            in variables end
      val _ = cpc_fp_private_source_avoid := avoid
    in
      Portable.finally
        (fn () => cpc_fp_private_source_avoid := saved) action input
    end

  (* Declaration callers supply variables, not compound source terms. *)
  fun cpc_fp_private_avoid_terms terms =
    cpc_fp_private_parse_avoid :=
      terms @ !cpc_fp_private_parse_avoid

  fun fresh_cpc_fp_private_marker ty _ =
    let
      (* Original variables come from the permitted Source scope; parsed
         declarations and earlier private allocations are reserved directly.
         Do not rescan a constructed witness operand (possibly an opaque
         binder) just to rediscover those names. *)
      val sources = (!cpc_fp_private_source_avoid) ()
      (* Source scopes memoize this exact variable list. Retain it once,
         not once per marker (which would grow avoids quadratically). *)
      val avoided =
        if Portable.pointer_eq (sources,!cpc_reserved_source_scope) then
          !cpc_fp_private_parse_avoid
        else sources @ !cpc_fp_private_parse_avoid
      val _ = cpc_reserved_source_scope := sources
      val marker = Term.variant avoided (Term.genvar ty)
      val _ = cpc_fp_private_parse_avoid := marker :: avoided
      val _ = cpc_fp_private_allocated :=
        HOLset.add (!cpc_fp_private_allocated, marker)
    in marker end

  fun add_term (dicts_ref : dicts ref) name tm =
    let
      val (tydict, tmdict) = !dicts_ref
      val tmdict = Library.extend_dict ((name,
        SmtLib_Theories.K_zero_zero tm), tmdict)
    in
      dicts_ref := (tydict, tmdict);
      if Term.is_var tm then cpc_fp_private_avoid_terms [tm] else ()
    end

  (* CPC prints rational literals as atoms (for example `-1` and `4/3`),
     while SMT-LIB normally uses constructor syntax.  These occur in proof
     arguments and definitions even when the source query contained no
     rational atom.  Keep the compatibility layer narrow: standard literals
     remain delegated to the ordinary dictionaries and unknown proof tokens
     still fail loudly. *)
  fun cpc_literal_parsefn token indices args =
    if not (List.null indices) orelse not (List.null args) then
      SmtLib_Theories.decline "<cpc_literal_parsefn>"
        "not a nullary CPC literal"
    else case SmtLib_Parser.proof_string_token token of
      SOME value =>
        (SmtLib_String_Literal.mk_string_term value
         handle SmtLib_String_Literal.InvalidStringLiteral detail =>
           raise ERR "cpc_literal_parsefn" detail)
    | NONE =>
    if String.isPrefix "-" token orelse String.isSubstring "/" token then
      let
        val is_fraction = String.isSubstring "/" token
        val fields = String.fields (fn c => c = #"/") token
        val (numerator_text, denominator_text) =
          case fields of
            [numerator, denominator] => (numerator, denominator)
          | [numerator] => (numerator, "1")
          | _ => raise ERR "cpc_literal_parsefn" "malformed CPC rational literal"
        val numerator = Arbint.fromString numerator_text
        val denominator = Arbint.fromString denominator_text
      in
        if not is_fraction then intSyntax.term_of_int numerator
        else if denominator = Arbint.one then realSyntax.term_of_int numerator
        else realSyntax.mk_div (realSyntax.term_of_int numerator,
          realSyntax.term_of_int denominator)
      end
    else SmtLib_Theories.decline "<cpc_literal_parsefn>"
      "not a CPC rational literal"

  fun numeral_of_term where_ tm =
    numSyntax.dest_numeral tm
    handle Feedback.HOL_ERR _ =>
      Arbint.toNat (intSyntax.int_of_term tm)
      handle Feedback.HOL_ERR _ =>
        raise ERR where_ "expected a CPC natural-number argument"

  (* These compact constructors are emitted by cvc5's CPC printer, not by
     SMT-LIB source files.  They are definitional presentations of ordinary
     HOL bit-vector terms. *)
  fun cpc_bv_parsefn token indices args =
    if not (List.null indices) then
      SmtLib_Theories.decline "<cpc_bv_parsefn>"
        "unexpected indexed CPC bit-vector term"
    else
      case (token, args) of
        ("@bv", [value, width]) =>
          wordsSyntax.mk_word (numeral_of_term "@bv value" value,
            numeral_of_term "@bv width" width)
      | ("@bvsize", [word]) =>
          intSyntax.mk_injected
            (numSyntax.mk_numeral
              (fcpLib.index_to_num (wordsSyntax.dim_of word)))
      | ("@bit", [index, word]) =>
          wordsSyntax.mk_word_bit
            (numSyntax.mk_numeral (numeral_of_term "@bit index" index), word)
      | ("@from_bools", bits) => SmtLib_Theories.mk_bbterm bits
      | ("bvsltbv", [left, right]) =>
          boolSyntax.mk_cond
            (wordsSyntax.mk_word_lt (left, right),
             wordsSyntax.mk_word (Arbnum.one, Arbnum.one),
             wordsSyntax.mk_word (Arbnum.zero, Arbnum.one))
      | ("bvultbv", [left, right]) =>
          boolSyntax.mk_cond
            (wordsSyntax.mk_word_lo (left, right),
             wordsSyntax.mk_word (Arbnum.one, Arbnum.one),
             wordsSyntax.mk_word (Arbnum.zero, Arbnum.one))
      | ("concat", first :: rest) =>
          if List.null rest then
            SmtLib_Theories.decline "<cpc_bv_parsefn>"
              "concat expects at least two words"
          else List.foldl
            (fn (right, left) => wordsSyntax.mk_word_concat (left, right))
            first rest
      | _ => SmtLib_Theories.decline "<cpc_bv_parsefn>"
          "malformed CPC bit-vector term"

  (* A linear-integer source proof can introduce real-valued rational
     coefficients.  cvc5 writes the corresponding floor/coercion operators
     even though the input logic did not need the mixed Int/Real dictionary. *)
  fun cpc_intreal_parsefn token indices args =
    if not (List.null indices) then
      SmtLib_Theories.decline "<cpc_intreal_parsefn>"
        "unexpected indexed CPC arithmetic term"
    else
      case (token, args) of
        ("to_int", [real]) => intrealSyntax.mk_INT_FLOOR real
      | ("to_real", [integer]) => intrealSyntax.mk_real_of_int integer
      | ("int.pow2", [exponent]) =>
          intSyntax.mk_exp
            (intSyntax.term_of_int (Arbint.fromInt 2),
             intSyntax.mk_Num exponent)
      | _ => SmtLib_Theories.decline "<cpc_intreal_parsefn>"
          "malformed CPC arithmetic term"

  (* CPC prints every indexed SMT-LIB term identifier as an ordinary
     application whose leading arguments are the indices.  Derive the
     adapter from the authoritative ALL-logic registry, retaining the
     official SMT-LIB entries and cvc5's proof-term extensions (but not
     another solver's dialect).  This covers the current 23 entries,
     including duplicate overloaded entries, and makes a future applicable
     registry addition available without another CPC list. *)
  fun same_metadata
      ({theory = theory1, kind = kind1, name = name1, source = source1,
        attributes = attributes1, declarations = declarations1}
        : SmtLib_Theories.symbol_metadata)
      ({theory = theory2, kind = kind2, name = name2, source = source2,
        attributes = attributes2, declarations = declarations2}
        : SmtLib_Theories.symbol_metadata) =
    theory1 = theory2 andalso kind1 = kind2 andalso name1 = name2 andalso
    source1 = source2 andalso attributes1 = attributes2 andalso
    declarations1 = declarations2

  fun distinct_metadata metadata = List.foldl
    (fn (entry, result) =>
      if List.exists (same_metadata entry) result then result
      else result @ [entry]) [] metadata

  val cpc_indexed_term_registry = distinct_metadata (List.filter
    (fn ({kind, source, attributes, ...}
          : SmtLib_Theories.symbol_metadata) =>
      kind = "term" andalso #indexed attributes andalso
      (case source of
         SmtLib_Theories.Official => true
       | SmtLib_Theories.Extension "cvc5" => true
       | SmtLib_Theories.Extension _ => false))
    (SmtLib_Logics.metadata_of_logic "ALL"))

  fun indexed_family_arities metadata =
    let
      fun add ({name, attributes, ...}: SmtLib_Theories.symbol_metadata,
          families) =
        let
          val arity = List.length (#parametric_sorts attributes)
        in
          case Redblackmap.peek (families, name) of
            NONE => Redblackmap.insert (families, name, arity)
          | SOME old_arity =>
              if old_arity = arity then families
              else raise ERR "indexed_family_arities"
                ("inconsistent indexed arities for registry symbol " ^ name)
        end
    in
      Redblackmap.listItems (List.foldl add
        (Redblackmap.mkDict String.compare) metadata)
    end

  val cpc_indexed_term_families =
    indexed_family_arities cpc_indexed_term_registry

  fun cpc_deindexed_parsefn source_dict source_name index_arity token
      indices args =
    if source_name = "_" andalso token <> "_" then
      SmtLib_Theories.decline "<cpc_deindexed_parsefn>"
        "generic indexed adapter does not match this token"
    else if not (List.null indices) then
      SmtLib_Parser.apply_term source_dict source_name indices args
    else if List.length args < index_arity then
      SmtLib_Theories.decline "<cpc_deindexed_parsefn>"
        (token ^ " expects " ^ Int.toString index_arity ^
         " flattened index argument(s)")
    else
      SmtLib_Parser.apply_term source_dict source_name
        (List.take (args, index_arity)) (List.drop (args, index_arity))

  fun with_cpc_deindexed_entries tmdict =
    List.foldl
      (fn ((name, arity), dict) =>
        if Option.isSome (Redblackmap.peek (tmdict, name)) then
          let
            val adapter = cpc_deindexed_parsefn tmdict name arity
            (* [_] is also the parser's generic literal pseudo-entry.  Its
               non-indexed alternatives must remain available for atoms such
               as [#b0]; every real indexed family is replaced outright so
               malformed flattened applications cannot fall through. *)
            val entries = if name = "_" then
                adapter :: Redblackmap.find (tmdict, name)
              else [adapter]
          in
            Redblackmap.insert (dict, name, entries)
          end
        else dict)
      tmdict cpc_indexed_term_families

  (* [to_fp_bv] is a genuinely CPC-specific alias, rather than an indexed
     SMT-LIB registry name. *)
  fun cpc_to_fp_bv_parsefn token indices args =
    case (token, indices, args) of
      ("to_fp_bv", [_, _], _) =>
        SmtLib_Theories.FloatingPoint.to_fp indices args
    | ("to_fp_bv", [], eb :: sb :: rest) =>
        SmtLib_Theories.FloatingPoint.to_fp [eb, sb] rest
    | _ => raise ERR "cpc_to_fp_bv_parsefn"
        "to_fp_bv expects two FP format indices"

  (* cvc5's FP bit-blaster uses sort expressions as proof-term metadata,
     for example `(@fp.SIGN (_ BitVec 1))`.  HOL has no terms denoting
     types, so retain only the marker's HOL type.  The internal @fp names
     then become ordinary free HOL variables of that type; a later `trust`
     step must still prove every relationship between them and the source FP
     term.  This interpretation therefore grants no theorem. *)
  fun cpc_sort_marker_parsefn token indices args =
    let
      fun marker name ty = Term.mk_var (name, ty)
      fun width index = fcpLib.index_type (numeral_of_term token index)
    in
      case (token, indices, args) of
        ("Int", [], []) => marker "@cpc.Int" intSyntax.int_ty
      | ("BitVec", [bits], []) =>
          marker "@cpc.BitVec" (wordsSyntax.mk_word_type (width bits))
      | ("FloatingPoint", [eb, sb], []) =>
          marker "@cpc.FloatingPoint"
            (SmtLib_Theories.smtfp_type
              (numeral_of_term token eb, numeral_of_term token sb))
      | ("->", [], domain :: rest) =>
          if List.null rest then
            raise ERR "cpc_sort_marker_parsefn"
              "CPC function-sort marker needs a range"
          else
            let
              val (domains, range) = Lib.front_last (domain :: rest)
            in
              marker "@cpc.function"
                (boolSyntax.list_mk_fun
                  (List.map Term.type_of domains, Term.type_of range))
            end
      | _ => raise ERR "cpc_sort_marker_parsefn"
          ("malformed CPC sort marker " ^ token)
    end

  type cpc_fp_private_binding = {
    marker : Term.term,
    kind : string,
    source : Term.term
  }

  val cpc_fp_private_bindings_ref =
    ref ([] : cpc_fp_private_binding list)

  val cpc_fp_private_unbound_markers_ref =
    ref ([] : (Term.term * string) list)

  (* Keys retain only the no-op observer; queries supply their own work
     gate. Preserve typed variable identity, including separately allocated
     copies. Pointer hits open nothing, and different names open no Types.
     All string bytes, Type edges and memo probes are paid BEFORE inspection.
     The local pair memo prevents expansion of shared annotations and never
     retains a caller or query Type in the proof-local index. *)
  fun private_identity_compare ((left,observe_left),(right,observe_right)) =
    let
      fun observe () = (observe_left (); observe_right ())
      fun names (a,b) =
        (observe ();
         if Portable.pointer_eq (a,b) then EQUAL else
         let
           val na = String.size a
           val nb = String.size b
           fun next i =
             (observe ();
              if i = na then (if i = nb then EQUAL else LESS)
              else if i = nb then GREATER
              else case Char.compare (String.sub (a,i),String.sub (b,i)) of
                EQUAL => next (i+1)
              | order => order)
         in next 0 end)
      fun types pair =
        let
          val saved = ref
            ([] : (Type.hol_type * Type.hol_type * order) list)
          fun lookup _ [] = NONE
            | lookup (a,b) ((l,r,result)::rest) =
                (observe ();
                 if Portable.pointer_eq (a,l) andalso
                    Portable.pointer_eq (b,r) then SOME result
                 else lookup (a,b) rest)
          fun operators (a,b) =
            (observe ();
             if Portable.pointer_eq (a,b) then EQUAL else
             let
               val {Name=an,Thy=at} = KernelSig.name_of_id a
               val {Name=bn,Thy=bt} = KernelSig.name_of_id b
             in case names (an,bn) of
                 EQUAL => (case names (at,bt) of
                     EQUAL => Int.compare
                       (KernelSig.epoch_of a,KernelSig.epoch_of b)
                   | order => order)
               | order => order
             end)
          fun arguments (xs,ys) =
            (observe ();
             case (xs,ys) of
               ([],[]) => EQUAL
             | ([],_) => LESS
             | (_,[]) => GREATER
             | (a::rest,b::tail) =>
                 (case compare (a,b) of EQUAL => arguments (rest,tail)
                  | order => order))
          and compare (a,b) =
            (observe ();
             if Portable.pointer_eq (a,b) then EQUAL else
             case lookup (a,b) (!saved) of SOME order => order
             | NONE =>
                 let
                   val order = if Type.is_vartype a then
                       if Type.is_vartype b then names
                         (Type.dest_vartype a,Type.dest_vartype b)
                       else LESS
                     else if Type.is_vartype b then GREATER
                     else
                       let val {Tyop=ao,Args=ax,...} =
                             Type.dest_thy_typeid a
                           val {Tyop=bo,Args=bx,...} =
                             Type.dest_thy_typeid b
                       in case operators (ao,bo) of
                           EQUAL => arguments (ax,bx)
                         | order => order
                       end
                   val _ = saved := (a,b,order) :: !saved
                 in order end)
        in compare pair end
    in
      observe ();
      if Portable.pointer_eq (left,right) then EQUAL else
      let val (ln,lt) = Term.dest_var left
          val (rn,rt) = Term.dest_var right
      in case names (ln,rn) of EQUAL => types (lt,rt)
         | order => order
      end
    end
  fun no_private_identity_observation () = ()
  fun empty_private_identity_index () =
    HOLset.empty private_identity_compare
  val cpc_fp_private_identity_index = ref (empty_private_identity_index ())
  fun register_cpc_fp_private_identity marker =
    cpc_fp_private_identity_index := HOLset.add
      (!cpc_fp_private_identity_index,
       (marker,no_private_identity_observation))
  fun is_cpc_fp_private_marker_observed observe term =
    (observe ();
     Term.is_var term andalso HOLset.member
       (!cpc_fp_private_identity_index,(term,observe)))
  fun is_cpc_fp_private_marker term =
    is_cpc_fp_private_marker_observed no_private_identity_observation term

  fun cpc_fp_private_bindings () = !cpc_fp_private_bindings_ref
  fun cpc_fp_private_unbound_markers () =
    !cpc_fp_private_unbound_markers_ref

  (* Only syntactic FP metadata is retained here, never replay results or
     theorem authority. The weak key must be the command spine itself, not
     a fresh ref wrapping it: the latter could die while the proof is live.
     Poly/ML's Weak API types weak targets as refs. At this boundary only,
     view the heap object as an opaque ref; never dereference or assign it.
     No registry value or closure keeps a strong pointer to the commands.
     Empty spines are shared immediates, so use the proof record for those.
     Like the replay's existing Poly/ML sharing operations, this needs a
     runtime adapter on other ML systems; there is no portable Weak API. *)
  type cpc_fp_private_proof_entry = {
    key : unit ref option ref,
    bindings : cpc_fp_private_binding list,
    unbound : (Term.term * string) list,
    identities : (Term.term * (unit -> unit)) HOLset.set
  }

  val cpc_fp_private_proofs =
    ref ([] : cpc_fp_private_proof_entry list)

  fun cpc_fp_private_proof_key (proof : proof) : unit ref =
    if List.null (#commands proof) then RunCall.unsafeCast proof
    else RunCall.unsafeCast (#commands proof)

  fun prune_cpc_fp_private_proofs () =
    cpc_fp_private_proofs := List.filter
      (fn {key, ...} : cpc_fp_private_proof_entry => Option.isSome (!key))
      (!cpc_fp_private_proofs)

  fun retain_cpc_fp_private_proof proof =
    let
      val _ = prune_cpc_fp_private_proofs ()
    in
      if List.null (!cpc_fp_private_bindings_ref) andalso
         List.null (!cpc_fp_private_unbound_markers_ref) then ()
      else cpc_fp_private_proofs := {
        key = Weak.weak (SOME (cpc_fp_private_proof_key proof)),
        bindings = !cpc_fp_private_bindings_ref,
        unbound = !cpc_fp_private_unbound_markers_ref,
        identities = !cpc_fp_private_identity_index
      } :: !cpc_fp_private_proofs
    end

  fun with_cpc_fp_private_proof proof action input =
    let
      val _ = prune_cpc_fp_private_proofs ()
      val key = cpc_fp_private_proof_key proof
      fun matches ({key = weak, ...} : cpc_fp_private_proof_entry) =
        case !weak of
          SOME saved => Portable.pointer_eq (saved, key)
        | NONE => false
      val saved_bindings = !cpc_fp_private_bindings_ref
      val saved_unbound = !cpc_fp_private_unbound_markers_ref
      val saved_identities = !cpc_fp_private_identity_index
      val (bindings, unbound, identities) =
        case List.find matches (!cpc_fp_private_proofs) of
          SOME {bindings, unbound, identities, ...} =>
            (bindings, unbound, identities)
        | NONE => ([], [], empty_private_identity_index ())
      val _ = cpc_fp_private_bindings_ref := bindings
      val _ = cpc_fp_private_unbound_markers_ref := unbound
      val _ = cpc_fp_private_identity_index := identities
      fun restore () =
        (cpc_fp_private_bindings_ref := saved_bindings;
         cpc_fp_private_unbound_markers_ref := saved_unbound;
         cpc_fp_private_identity_index := saved_identities)
    in Portable.finally restore action input end

  fun cpc_fp_private_abbreviation token sort_marker source =
    let
      fun same ({marker, kind, source = saved} : cpc_fp_private_binding) =
        kind = token andalso
        Type.compare (Term.type_of marker, Term.type_of sort_marker) = EQUAL
        andalso (Portable.pointer_eq (saved, source) orelse
                 Term.aconv saved source)
    in
      case List.find same (!cpc_fp_private_bindings_ref) of
        SOME {marker, ...} => marker
      | NONE =>
          let
            val marker = fresh_cpc_fp_private_marker
              (Term.type_of sort_marker) [source]
            val binding = {marker = marker, kind = token, source = source}
          in
            cpc_fp_private_bindings_ref :=
              binding :: !cpc_fp_private_bindings_ref;
            register_cpc_fp_private_identity marker;
            marker
          end
    end

  fun cpc_fp_private_parsefn token indices args =
    if not (List.null indices) then
      raise ERR "cpc_fp_private_parsefn" "unexpected indices"
    else
      case args of
        [sort_marker] =>
          let
            val marker = fresh_cpc_fp_private_marker
              (Term.type_of sort_marker) []
          in
            cpc_fp_private_unbound_markers_ref :=
              (marker, token) :: !cpc_fp_private_unbound_markers_ref;
            register_cpc_fp_private_identity marker;
            marker
          end
      | [sort_marker, source] =>
          cpc_fp_private_abbreviation token sort_marker source
      | _ => raise ERR "cpc_fp_private_parsefn"
          (token ^ " expects a sort marker and at most one " ^
           "floating-point operand")

  fun cpc_fp_rounding_parsefn token indices args =
    if token <> "@fp.RMBITBLAST" orelse not (List.null indices) then
      raise ERR "cpc_fp_rounding_parsefn"
        "malformed private rounding-mode bit-blast"
    else
      case args of
        [source] =>
          let
            val constant = Term.prim_mk_const
              {Thy = "smtfloatReplayWord",
               Name = "smtfp_cvc_rounding_bits"}
            val (domain, _) = Type.dom_rng (Term.type_of constant)
            val instantiation =
              Type.match_type domain (Term.type_of source)
          in Term.mk_comb (Term.inst instantiation constant, source) end
      | _ => raise ERR "cpc_fp_rounding_parsefn"
          "private rounding-mode bit-blast expects one operand"

  fun cpc_private_const_parsefn token indices args =
    if token <> "@const" orelse not (List.null indices) then
      raise ERR "cpc_private_const_parsefn" "malformed private constant"
    else
      case args of
        [index, sort_marker] =>
          let
            val _ =
              Type.compare (Term.type_of index, intSyntax.int_ty) = EQUAL
              orelse raise ERR "cpc_private_const_parsefn"
                "@const index must have HOL int type"
          in
            Term.mk_var
              ("@cpc.const." ^
               Arbnum.toString (numeral_of_term token index),
               Term.type_of sort_marker)
          end
      | _ => raise ERR "cpc_private_const_parsefn"
          "@const expects an index and a sort marker"

  fun cpc_bvite_parsefn token indices args =
    if token <> "bvite" orelse not (List.null indices) then
      raise ERR "cpc_bvite_parsefn" "malformed bvite"
    else
      case args of
        [condition, then_branch, else_branch] =>
          boolSyntax.mk_cond
            (wordsSyntax.mk_word_bit (numSyntax.zero_tm, condition),
             then_branch, else_branch)
      | _ => raise ERR "cpc_bvite_parsefn" "bvite expects three arguments"

  (* Totalized FP operators are private bit-blaster vocabulary.  Keep each
     application as an uninterpreted HOL function: its defining `trust` step
     is accepted only if the FP re-prover can establish the relationship to
     the public SMT-LIB operator. *)
  fun cpc_fp_total_parsefn token indices args =
    if not (List.null indices) orelse List.null args then
      raise ERR "cpc_fp_total_parsefn" "malformed private FP operator"
    else
      let
        val result_type = Term.type_of (List.hd args)
        val function_type = boolSyntax.list_mk_fun
          (List.map Term.type_of args, result_type)
      in
        Term.list_mk_comb (Term.mk_var (token, function_type), args)
      end

  (* cvc5's CPC signature contains totalized arithmetic operators that are
     not SMT-LIB symbols.  Integer totals have specified zero branches;
     integer by-zero skolems remain HOL's underspecified ediv/emod at zero.
     Real by-zero uses smt_rdiv, since HOL real division is specified there. *)
  val smt_ediv_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_ediv_total"}
  val smt_emod_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_emod_total"}
  val smt_rdiv_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_rdiv"}

  fun cpc_arith_total_error message =
    raise ERR "cpc_arith_total_parsefn" message

  fun cpc_left_assoc name constructor args =
    case args of
      first :: rest =>
        if List.null rest then
          cpc_arith_total_error (name ^ " expects at least two arguments")
        else List.foldl (fn (right, left) => constructor (left, right))
          first rest
    | [] => cpc_arith_total_error (name ^ " expects arguments")

  fun cpc_real_arg arg =
    if Type.compare (Term.type_of arg, intSyntax.int_ty) = EQUAL then
      intrealSyntax.mk_real_of_int arg
    else arg

  fun cpc_arith_total_parsefn token indices args =
    if not (List.null indices) then
      cpc_arith_total_error (token ^ " does not accept indices")
    else
      case token of
        "div_total" => cpc_left_assoc token
          (fn (left, right) => Term.list_mk_comb
            (smt_ediv_total_tm, [left, right])) args
      | "mod_total" =>
          (case args of
             [left, right] => Term.list_mk_comb
               (smt_emod_total_tm, [left, right])
           | _ => cpc_arith_total_error "mod_total expects two arguments")
      | "/_total" => cpc_left_assoc token
          (fn (left, right) => realSyntax.mk_div (left, right))
          (List.map cpc_real_arg args)
      | "@int_div_by_zero" =>
          (case args of
             [arg] => SmtLib_Theories.mk_int_ediv
               (arg, intSyntax.zero_tm)
           | [] => Term.mk_var (token, intSyntax.int_ty)
           | _ => cpc_arith_total_error
               "@int_div_by_zero expects one argument")
      | "@mod_by_zero" =>
          (case args of
             [arg] => SmtLib_Theories.mk_int_emod
               (arg, intSyntax.zero_tm)
           | [] => Term.mk_var (token, intSyntax.int_ty)
           | _ => cpc_arith_total_error
               "@mod_by_zero expects one argument")
      | "@div_by_zero" =>
          (case args of
             [arg] => Term.list_mk_comb
               (smt_rdiv_tm, [arg, realSyntax.zero_tm])
           | [] => Term.mk_var (token, realSyntax.real_ty)
           | _ => cpc_arith_total_error
               "@div_by_zero expects one argument")
      | _ => cpc_arith_total_error
        ("unsupported totalized arithmetic symbol " ^ token)

  (* cvc5 uses unary variadic aggregates as compact list substitutions in
     RARE annotations.  They are proof metadata, not accepted benchmark
     syntax; interpret a singleton as itself and retain the standard
     left-associative meaning for longer lists. *)
  fun cpc_concat_parsefn theory_name token indices args =
    if not (List.null indices) then
      raise ERR "cpc_concat_parsefn" "unexpected concat indices"
    else
      let
        val constant =
          Term.prim_mk_const {Thy = "smtstring", Name = theory_name}
        fun concat (right, left) =
          Term.list_mk_comb (constant, [left, right])
      in
        case args of
          first :: rest => List.foldl concat first rest
        | [] => raise ERR "cpc_concat_parsefn"
            (token ^ " expects at least one CPC argument")
      end

  fun with_cpc_fp_entries tmdict =
    let
      val tmdict = List.foldl
        (fn (name, dict) => Library.extend_dict
          ((name, cpc_sort_marker_parsefn), dict))
        tmdict ["Int", "BitVec", "FloatingPoint", "->"]
      val tmdict = List.foldl
        (fn (name, dict) => Library.extend_dict
          ((name, cpc_fp_private_parsefn), dict))
        tmdict
        ["@fp.SIGN", "@fp.EXPONENT", "@fp.SIGNIFICAND", "@fp.ZERO",
         "@fp.NAN", "@fp.INF"]
      val tmdict = Library.extend_dict
        (("@fp.RMBITBLAST", cpc_fp_rounding_parsefn), tmdict)
      val tmdict = Library.extend_dict
        (("bvite", cpc_bvite_parsefn), tmdict)
      val tmdict = List.foldl
        (fn (name, dict) => Library.extend_dict
          ((name, cpc_fp_total_parsefn), dict))
        tmdict ["fp.max_total", "fp.min_total"]
    in
      Library.extend_dict
        (("to_fp_bv", cpc_to_fp_bv_parsefn), tmdict)
    end

  val cpc_smtstr_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "smtstr", Args = []}

  fun cpc_skolem_error where_ message = raise ERR where_ message

  fun cpc_exact_args where_ arity args =
    if List.length args = arity then args
    else cpc_skolem_error where_
      ("expected " ^ Int.toString arity ^ " explicit argument(s)")

  (* Parameterized CPC skolems are authoritative typed symbols, not an
     invitation to synthesize a fresh UF at whatever types happen to parse.
     Keep all sort/coherence checks in this fail-closed boundary. *)
  val cpc_reglan_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "reglan", Args = []}

  fun cpc_type_eq (left, right) = Type.compare (left, right) = EQUAL

  fun cpc_expect_type where_ expected term =
    if cpc_type_eq (Term.type_of term, expected) then ()
    else cpc_skolem_error where_ "parameterized-skolem sort mismatch"

  fun cpc_expect_same where_ left right =
    if cpc_type_eq (Term.type_of left, Term.type_of right) then ()
    else cpc_skolem_error where_
      "parameterized-skolem arguments have different sorts"

  fun cpc_expect_smtstr where_ term =
    cpc_expect_type where_ cpc_smtstr_ty term

  fun cpc_expect_reglan where_ term =
    cpc_expect_type where_ cpc_reglan_ty term

  fun cpc_reglan_equiv left right =
    SmtRegLanProve.mk_equiv (left, right)

  (* RegLan is an extensional sort in SMT-LIB and cvc5's CPC calculus.  This
     dictionary is proof-local: source HOL equality remains constructor
     equality and is rejected by translation below. *)
  fun cpc_equality_parsefn token indices args =
    let
      val _ = List.null indices orelse cpc_skolem_error
        "cpc_equality_parsefn" "equality does not accept indices"
      val _ = List.length args >= 2 orelse cpc_skolem_error
        "cpc_equality_parsefn" "equality expects at least two arguments"
      val ty = Term.type_of (List.hd args)
      val _ = List.all (fn arg => cpc_type_eq (Term.type_of arg, ty)) args
        orelse cpc_skolem_error "cpc_equality_parsefn"
          "equality arguments have different sorts"
      fun adjacent relation (left :: right :: rest) =
            relation left right :: adjacent relation (right :: rest)
        | adjacent _ _ = []
      val relation =
        if cpc_type_eq (ty, cpc_reglan_ty) then cpc_reglan_equiv
        else fn left => fn right => boolSyntax.mk_eq (left, right)
    in
      boolSyntax.list_mk_conj (adjacent relation args)
    end

  fun cpc_distinct_parsefn token indices args =
    let
      val _ = List.null indices orelse cpc_skolem_error
        "cpc_distinct_parsefn" "distinct does not accept indices"
      val _ = List.length args >= 2 orelse cpc_skolem_error
        "cpc_distinct_parsefn" "distinct expects at least two arguments"
      val ty = Term.type_of (List.hd args)
      val _ = List.all (fn arg => cpc_type_eq (Term.type_of arg, ty)) args
        orelse cpc_skolem_error "cpc_distinct_parsefn"
          "distinct arguments have different sorts"
      fun pairs _ [] = []
        | pairs relation (left :: rest) =
            List.map (fn right => boolSyntax.mk_neg (relation left right))
              rest @ pairs relation rest
    in
      if cpc_type_eq (ty, cpc_reglan_ty) then
        boolSyntax.list_mk_conj (pairs cpc_reglan_equiv args)
      else
        listSyntax.mk_all_distinct (listSyntax.mk_list (args, ty))
    end

  fun cpc_expect_int where_ term =
    cpc_expect_type where_ intSyntax.int_ty term

  fun cpc_sequence_element where_ term =
    if cpc_type_eq (Term.type_of term, cpc_smtstr_ty) then numSyntax.num
    else
      (listSyntax.dest_list_type (Term.type_of term)
       handle Feedback.HOL_ERR _ => cpc_skolem_error where_
         "expected a String or Seq argument")

  fun cpc_expect_same_sequence where_ left right =
    let
      val left_element = cpc_sequence_element where_ left
      val right_element = cpc_sequence_element where_ right
    in
      if cpc_type_eq (left_element, right_element) andalso
         cpc_type_eq (Term.type_of left, Term.type_of right) then ()
      else cpc_skolem_error where_
        "parameterized-skolem expected same-element Seq arguments"
    end

  fun cpc_function_types where_ function =
    Type.dom_rng (Term.type_of function)
    handle Feedback.HOL_ERR _ => cpc_skolem_error where_
      "expected a function argument"

  fun cpc_expect_function where_ domain range function =
    let val (actual_domain, actual_range) =
      cpc_function_types where_ function
    in
      if cpc_type_eq (domain, actual_domain) andalso
         cpc_type_eq (range, actual_range) then ()
      else cpc_skolem_error where_
        "parameterized-skolem function domain/range mismatch"
    end

  fun cpc_opaque_skolem token result_ty args =
    Term.list_mk_comb
      (Term.mk_var (token,
        boolSyntax.list_mk_fun (List.map Term.type_of args, result_ty)), args)

  fun cpc_purify_parsefn token indices args =
    case (token, indices, cpc_exact_args "cpc_purify_parsefn" 1 args) of
      ("@purify", [], [term]) => term
    | _ => cpc_skolem_error "cpc_purify_parsefn"
        "malformed @purify application"

  fun cpc_array_deq_diff_parsefn token indices args =
    case (token, indices,
        cpc_exact_args "cpc_array_deq_diff_parsefn" 2 args) of
      ("@array_deq_diff", [], [left, right]) =>
        let
          val (index, _) = cpc_function_types token left
          val _ = cpc_expect_same token left right
          val variable = Term.variant (Term.all_varsl [left, right])
            (Term.mk_var ("array_deq_diff_x", index))
        in
          boolSyntax.mk_select (variable, boolSyntax.mk_neg
            (boolSyntax.mk_eq (Term.mk_comb (left, variable),
              Term.mk_comb (right, variable))))
        end
    | _ => cpc_skolem_error "cpc_array_deq_diff_parsefn"
        "malformed @array_deq_diff application"

  fun immediate_forall_block where_ quantified =
    let
      fun lookup [] = cpc_skolem_error where_
            "source FORALL binder-block metadata is unavailable"
        | lookup ((candidate, sizes) :: rest) =
            if Term.aconv candidate quantified then
              (case sizes of
                 [size] => (candidate, size)
               | _ => cpc_skolem_error where_
                   "source FORALL binder-block metadata is ambiguous")
            else lookup rest
    in
      lookup (!cpc_forall_blocks)
    end

  fun cpc_quantifiers_skolemize_parsefn token indices args =
    case (token, indices,
        cpc_exact_args "cpc_quantifiers_skolemize_parsefn" 2 args) of
      ("@quantifiers_skolemize", [], [quantified, index_term]) =>
        let
          val where_ = "cpc_quantifiers_skolemize_parsefn"
          val _ = cpc_expect_int token index_term
          val index =
            (intSyntax.int_of_term index_term
             handle Feedback.HOL_ERR _ => cpc_skolem_error where_
               "expected a concrete integer binder index")
          val _ = if Arbint.< (index, Arbint.zero) then
              cpc_skolem_error where_ "binder index is negative"
            else ()
          val _ = if boolSyntax.is_forall quantified then ()
            else cpc_skolem_error where_
              "expected a FORALL Boolean formula"
          val (canonical_quantified, immediate_count) =
            immediate_forall_block where_ quantified
          val {witnesses, ...} = CPC_Proof.cpc_skolem_witnesses
            immediate_count
            (Thm.ASSUME (boolSyntax.mk_neg canonical_quantified))
          fun witness_at _ [] = cpc_skolem_error where_
                "binder index is outside the quantified formula"
            | witness_at current (witness :: rest) =
                (case Arbint.compare (index, current) of
                   EQUAL => witness
                 | GREATER =>
                     witness_at (Arbint.+ (current, Arbint.one)) rest
                 | LESS => cpc_skolem_error where_
                     "binder index is outside the quantified formula")
        in
          witness_at Arbint.zero witnesses
        end
    | _ => cpc_skolem_error "cpc_quantifiers_skolemize_parsefn"
        "malformed @quantifiers_skolemize application"

  fun cpc_sets_deq_diff_parsefn token indices args =
    case (token, indices, cpc_exact_args "cpc_sets_deq_diff_parsefn" 2 args) of
      ("@sets_deq_diff", [], [left, right]) =>
        let
          val (element, range) = cpc_function_types token left
          val _ = cpc_expect_type token Type.bool
            (Term.mk_var ("set_range", range))
          val _ = cpc_expect_same token left right
          val variable = Term.variant (Term.all_varsl [left, right])
            (Term.mk_var ("sets_deq_diff_x", element))
        in
          boolSyntax.mk_select (variable, boolSyntax.mk_neg
            (boolSyntax.mk_eq (Term.mk_comb (left, variable),
              Term.mk_comb (right, variable))))
        end
    | _ => cpc_skolem_error "cpc_sets_deq_diff_parsefn"
        "malformed @sets_deq_diff application"

  fun cpc_bag_element where_ bag =
    let val (element, count) =
      (Type.dom_rng (Term.type_of bag)
       handle Feedback.HOL_ERR _ => cpc_skolem_error where_
         "parameterized-skolem expected a Bag argument")
    in
      if Type.compare (count, numSyntax.num) = EQUAL then element
      else cpc_skolem_error where_
        "parameterized-skolem expected a Bag argument"
    end

  fun cpc_bag_element_type where_ bag_ty =
    let val (element, count) =
      (Type.dom_rng bag_ty
       handle Feedback.HOL_ERR _ => cpc_skolem_error where_
         "parameterized-skolem expected a nested Bag argument")
    in
      if cpc_type_eq (count, numSyntax.num) then element
      else cpc_skolem_error where_
        "parameterized-skolem expected a nested Bag argument"
    end

  fun cpc_bag_skolem_parsefn token indices args =
    if not (List.null indices) then
      cpc_skolem_error "cpc_bag_skolem_parsefn"
        (token ^ " does not accept indices")
    else
      case (token, args) of
        ("@bags_deq_diff", [left, right]) =>
          let
            val element = cpc_bag_element token left
            val _ =
              if Type.compare (Term.type_of left, Term.type_of right) = EQUAL
              then ()
              else cpc_skolem_error token
                "expected two Bags of the same type"
            val variable = Term.variant (Term.all_varsl [left, right])
              (Term.mk_var ("bags_deq_diff_x", element))
          in
            boolSyntax.mk_select (variable, boolSyntax.mk_neg
              (boolSyntax.mk_eq (Term.mk_comb (left, variable),
                Term.mk_comb (right, variable))))
          end
      | ("@tables_group_part", [table]) =>
          let
            val bag_ty = cpc_bag_element token table
            val element = cpc_bag_element_type token bag_ty
          in
            cpc_opaque_skolem token (Type.--> (element, bag_ty)) args
          end
      | ("@tables_group_part_element", [table, bag]) =>
          let
            val nested_bag_ty = cpc_bag_element token table
            val element = cpc_bag_element_type token nested_bag_ty
            val _ = cpc_expect_type token nested_bag_ty bag
          in
            cpc_opaque_skolem token element args
          end
      | ("@bags_map_sum", [function, bag, image]) =>
          let
            val element = cpc_bag_element token bag
            val (domain, range) = cpc_function_types token function
            val _ = cpc_type_eq (domain, element) orelse
              cpc_skolem_error token
                ("parameterized-skolem Bag-map function domain does not " ^
                 "match Bag element")
            val _ = cpc_expect_type token range image
          in
            cpc_opaque_skolem token
              (Type.--> (intSyntax.int_ty, intSyntax.int_ty)) args
          end
      | ("@bags_distinct_elements", [bag]) =>
          cpc_opaque_skolem token (Type.--> (intSyntax.int_ty,
            cpc_bag_element token bag)) args
      | ("@bags_distinct_elements_size", [bag]) =>
          (ignore (cpc_bag_element token bag);
           cpc_opaque_skolem token intSyntax.int_ty args)
      | ("@bags_map_preimage_injective", [function, bag, image]) =>
          let
            val element = cpc_bag_element token bag
            val (_, range) = cpc_function_types token function
            val _ = cpc_expect_function token element range function
            val _ = cpc_expect_type token range image
          in
            cpc_opaque_skolem token element args
          end
      | _ => cpc_skolem_error "cpc_bag_skolem_parsefn"
          ("malformed parameterized Bag skolem " ^ token)

  fun cpc_same_const thy name tm =
    case Lib.total Term.dest_thy_const tm of
      SOME {Thy, Name, ...} => Thy = thy andalso Name = name
    | NONE => false

  fun cpc_strip_regex_concat regex =
    case boolSyntax.strip_comb regex of
      (head, [left, right]) =>
        if cpc_same_const "smtstring" "reglan_concat" head then
          cpc_strip_regex_concat left @ cpc_strip_regex_concat right
        else [regex]
    | _ => [regex]

  fun cpc_regex_concat_pair regex =
    case boolSyntax.strip_comb regex of
      (head, [left, right]) =>
        if cpc_same_const "smtstring" "reglan_concat" head then
          SOME (left, right)
        else NONE
    | _ => NONE

  fun cpc_re_unfold_pos_direct_star regex =
    let
      fun recognized body middle suffix =
        case boolSyntax.strip_comb middle of
          (star, [star_body]) =>
            if cpc_same_const "smtstring" "reglan_star" star andalso
               Term.aconv body star_body andalso Term.aconv body suffix
            then SOME [body, middle, suffix]
            else NONE
        | _ => NONE
      val right_associated =
        case cpc_regex_concat_pair regex of
          SOME (body, rest) =>
            (case cpc_regex_concat_pair rest of
               SOME (middle, suffix) => recognized body middle suffix
             | NONE => NONE)
        | NONE => NONE
    in
      case right_associated of
        SOME components => SOME components
      | NONE =>
          (case cpc_regex_concat_pair regex of
             SOME (front, suffix) =>
               (case cpc_regex_concat_pair front of
                  SOME (body, middle) => recognized body middle suffix
                | NONE => NONE)
           | NONE => NONE)
    end

  fun cpc_re_unfold_pos_regexps regex =
    case cpc_re_unfold_pos_direct_star regex of
      SOME components => components
    | NONE => cpc_strip_regex_concat regex

  fun cpc_re_unfold_pos_decomposition_from regexps avoids string =
    let
      val list_ty = listSyntax.mk_list_type cpc_smtstr_ty
      val pieces = Term.variant avoids
        (Term.mk_var ("re_unfold_pos_pieces", list_ty))
      fun piece position = listSyntax.mk_el
        (numSyntax.mk_numeral (Arbnum.fromInt position), pieces)
      val positions = List.tabulate (List.length regexps, Lib.I)
      val selected = List.map piece positions
      val regex_list = listSyntax.mk_list
        (regexps, Term.type_of (List.hd regexps))
      val count = listSyntax.mk_length regex_list
      val position = Term.mk_var ("i", numSyntax.num)
      fun selected_list candidate = listSyntax.mk_genlist
        (Term.mk_abs (position, listSyntax.mk_el (position, candidate)),
         count)
      val concat_list = Term.prim_mk_const
        {Thy = "smtstring", Name = "smtstr_concat_list"}
      val membership_relation = Term.prim_mk_const
        {Thy = "smtstring", Name = "smt_in_re"}
      val list_relation = Term.inst
        [{redex = Type.alpha, residue = cpc_smtstr_ty},
         {redex = Type.beta, residue = Term.type_of (List.hd regexps)}]
        (Term.prim_mk_const {Thy = "list", Name = "LIST_REL"})
      val empty = Term.mk_comb
        (Term.prim_mk_const {Thy = "smtstring", Name = "SmtStr"},
         listSyntax.mk_nil numSyntax.num)
      fun ordinary candidate = boolSyntax.list_mk_conj
        [boolSyntax.mk_eq (listSyntax.mk_length candidate, count),
         boolSyntax.mk_eq
           (string, Term.mk_comb (concat_list, selected_list candidate)),
         Term.list_mk_comb
           (list_relation,
            [membership_relation, selected_list candidate, regex_list])]
      fun endpoints candidate = boolSyntax.mk_conj
        (boolSyntax.mk_neg (boolSyntax.mk_eq
           (listSyntax.mk_el (numSyntax.zero_tm, candidate), empty)),
         boolSyntax.mk_neg (boolSyntax.mk_eq
           (listSyntax.mk_el
             (Term.mk_comb
                (Term.prim_mk_const {Thy = "prim_rec", Name = "PRE"},
                 count),
              candidate),
            empty)))
      val other = Term.variant (pieces :: avoids)
        (Term.mk_var ("re_unfold_pos_other", list_ty))
      val guarded_exists = boolSyntax.mk_exists
        (other, boolSyntax.mk_conj (ordinary other, endpoints other))
      val predicate = boolSyntax.mk_conj
        (ordinary pieces,
         boolSyntax.mk_imp (guarded_exists, endpoints pieces))
    in
      {pieces = pieces, regexps = regexps, selected = selected,
       predicate = predicate,
       witness = boolSyntax.mk_select (pieces, predicate)}
    end

  fun cpc_re_unfold_pos_decomposition string regex =
    cpc_re_unfold_pos_decomposition_from
      (cpc_re_unfold_pos_regexps regex) (Term.all_varsl [string, regex])
      string

  (* A RE_UNFOLD_POS component is a projection of one shared Hilbert-choice
     decomposition, not an independent opaque string.  Rebuilding the same
     choice predicate for every index makes all projections coherent while
     leaving the choice entirely theorem backed. *)
  fun cpc_re_unfold_pos_component string regex index =
    let
      val index = Arbint.toInt (intSyntax.int_of_term index)
        handle Overflow => cpc_skolem_error
          "cpc_re_unfold_pos_component" "component index is too large"
      val _ = if index >= 0 then () else cpc_skolem_error
        "cpc_re_unfold_pos_component" "component index is negative"
      val {regexps, witness, ...} =
        cpc_re_unfold_pos_decomposition string regex
      val _ = if index < List.length regexps then () else cpc_skolem_error
        "cpc_re_unfold_pos_component"
        "component index is outside the regular-expression concat"
    in
      listSyntax.mk_el
        (numSyntax.mk_numeral (Arbnum.fromInt index), witness)
    end

  fun cpc_string_skolem_parsefn token indices args =
    if not (List.null indices) then
      cpc_skolem_error "cpc_string_skolem_parsefn"
        (token ^ " does not accept indices")
    else
      let
        val arity =
          case token of
            "@re_unfold_pos_component" => 3
          | "@strings_deq_diff" => 2
          | "@strings_stoi_result" => 1
          | "@strings_stoi_non_digit" => 1
          | "@strings_itos_result" => 1
          | "@strings_num_occur" => 2
          | "@strings_num_occur_re" => 2
          | "@strings_occur_index" => 2
          | "@strings_occur_index_re" => 2
          | "@strings_replace_all_result" => 1
          | "@witness_string_length" => 1
          | _ => cpc_skolem_error "cpc_string_skolem_parsefn"
              ("unknown parameterized String skolem " ^ token)
        val args = cpc_exact_args "cpc_string_skolem_parsefn" arity args
      in
      case (token, args) of
        ("@re_unfold_pos_component", [string, regex, index]) =>
          (cpc_expect_smtstr token string;
           cpc_expect_reglan token regex;
           cpc_expect_int token index;
           cpc_re_unfold_pos_component string regex index)
      | ("@strings_deq_diff", [left, right]) =>
          (cpc_expect_same_sequence token left right;
           cpc_opaque_skolem token intSyntax.int_ty args)
      | ("@strings_stoi_result", [string]) =>
          (cpc_expect_smtstr token string;
          cpc_opaque_skolem token
            (Type.--> (intSyntax.int_ty, intSyntax.int_ty)) args)
      | ("@strings_stoi_non_digit", [string]) =>
          (cpc_expect_smtstr token string;
           cpc_opaque_skolem token intSyntax.int_ty args)
      | ("@strings_itos_result", [integer]) =>
          (cpc_expect_int token integer;
          cpc_opaque_skolem token
            (Type.--> (intSyntax.int_ty, intSyntax.int_ty)) args)
      | ("@strings_num_occur", [left, right]) =>
          (cpc_expect_same_sequence token left right;
           cpc_opaque_skolem token intSyntax.int_ty args)
      | ("@strings_num_occur_re", [string, regex]) =>
          (cpc_expect_smtstr token string;
           cpc_expect_reglan token regex;
           cpc_opaque_skolem token intSyntax.int_ty args)
      | ("@strings_occur_index", [left, right]) =>
          (cpc_expect_same_sequence token left right;
          cpc_opaque_skolem token
            (Type.--> (intSyntax.int_ty, intSyntax.int_ty)) args)
      | ("@strings_occur_index_re", [string, regex]) =>
          (cpc_expect_smtstr token string;
           cpc_expect_reglan token regex;
          cpc_opaque_skolem token
            (Type.--> (intSyntax.int_ty, intSyntax.int_ty)) args)
      | ("@strings_replace_all_result", [sequence]) =>
          (ignore (cpc_sequence_element token sequence);
           cpc_opaque_skolem token
             (Type.--> (intSyntax.int_ty, Term.type_of sequence)) args)
      | ("@witness_string_length", [sort_marker]) =>
          (ignore (cpc_sequence_element token sort_marker);
           cpc_opaque_skolem token
             (boolSyntax.list_mk_fun
               ([intSyntax.int_ty, intSyntax.int_ty],
                Term.type_of sort_marker)) args)
      | _ => cpc_skolem_error "cpc_string_skolem_parsefn"
          ("malformed parameterized String skolem " ^ token)
      end

  type cpc_skolem_entry = {
    name: string,
    parse: string -> Term.term list -> Term.term list -> Term.term
  }

  fun cpc_skolem_entry parse name : cpc_skolem_entry =
    {name = name, parse = parse}

  (* The closed opaque-skolem inventory in cvc5 1.3.4's safe CPC
     signature: Cpc.eo plus Arrays/Builtin/Quantifiers/Sets/Strings and the
     seven Bag skolems from the expert signature. *)
  val cpc_parameterized_skolem_registry : cpc_skolem_entry list =
    [cpc_skolem_entry cpc_purify_parsefn "@purify",
     cpc_skolem_entry cpc_array_deq_diff_parsefn "@array_deq_diff",
     cpc_skolem_entry cpc_private_const_parsefn "@const",
     cpc_skolem_entry cpc_string_skolem_parsefn
       "@re_unfold_pos_component",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_deq_diff",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_stoi_result",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_stoi_non_digit",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_itos_result",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_num_occur",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_num_occur_re",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_occur_index",
     cpc_skolem_entry cpc_string_skolem_parsefn "@strings_occur_index_re",
     cpc_skolem_entry cpc_string_skolem_parsefn
       "@strings_replace_all_result",
     cpc_skolem_entry cpc_string_skolem_parsefn "@witness_string_length",
     cpc_skolem_entry cpc_sets_deq_diff_parsefn "@sets_deq_diff",
     cpc_skolem_entry cpc_quantifiers_skolemize_parsefn
       "@quantifiers_skolemize",
     cpc_skolem_entry cpc_bag_skolem_parsefn "@bags_deq_diff",
     cpc_skolem_entry cpc_bag_skolem_parsefn "@tables_group_part",
     cpc_skolem_entry cpc_bag_skolem_parsefn
       "@tables_group_part_element",
     cpc_skolem_entry cpc_bag_skolem_parsefn "@bags_map_sum",
     cpc_skolem_entry cpc_bag_skolem_parsefn
       "@bags_distinct_elements",
     cpc_skolem_entry cpc_bag_skolem_parsefn
       "@bags_distinct_elements_size",
     cpc_skolem_entry cpc_bag_skolem_parsefn
       "@bags_map_preimage_injective"]

  val cpc_parameterized_skolem_names =
    List.map (fn ({name, ...}: cpc_skolem_entry) => name)
      cpc_parameterized_skolem_registry

  val _ =
    let
      val unique = HOLset.numItems (HOLset.addList
        (HOLset.empty String.compare, cpc_parameterized_skolem_names))
    in
      if List.length cpc_parameterized_skolem_registry = 23 andalso
         unique = 23 then ()
      else cpc_skolem_error "cpc_parameterized_skolem_registry"
        "closed CPC parameterized-skolem registry must contain 23 unique names"
    end

  fun with_cpc_parameterized_skolems tmdict =
    List.foldl
      (fn ({name, parse}: cpc_skolem_entry, dict) =>
        Library.extend_dict ((name, parse), dict))
      tmdict cpc_parameterized_skolem_registry

  fun cpc_parameterized_skolem_for_test name args =
    case List.find
        (fn ({name = candidate, ...}: cpc_skolem_entry) =>
          candidate = name) cpc_parameterized_skolem_registry of
      SOME {parse, ...} => parse name [] args
    | NONE => cpc_skolem_error "cpc_parameterized_skolem_for_test"
        ("unknown parameterized skolem " ^ name)

  fun cpc_function_sort token indices args =
    if token = "->" andalso List.null indices andalso
       List.length args >= 2 then
      let val (domains, range) = Lib.front_last args in
        boolSyntax.list_mk_fun (domains, range)
      end
    else raise ERR "function_sort"
      "expected a function sort with a domain and range"

  fun with_cpc_literals (tydict, tmdict) =
    let
      (* cvc5 writes [Bag Bool] in qualified bag literals.  A proof sort is
         parsed through the term dictionary, so retain Bool only as a marker. *)
      fun bool_sort_marker token indices args =
        if token = "Bool" andalso List.null indices andalso List.null args then
          boolSyntax.T
        else raise ERR "bool_sort_marker" "expected the Bool sort marker"
      fun string_sort_marker token indices args =
        if token = "String" andalso List.null indices andalso
           List.null args then
          Term.mk_var ("@cpc.String", cpc_smtstr_ty)
        else raise ERR "string_sort_marker"
          "expected the String sort marker"
      fun bag_sort_marker token indices args =
        case (token, indices, args) of
          ("Bag", [], [element]) => Term.mk_var ("@cpc.Bag",
            Type.--> (Term.type_of element, numSyntax.num))
        | _ => raise ERR "bag_sort_marker" "expected a Bag sort marker"
      fun set_sort_marker token indices args =
        case (token, indices, args) of
          ("Set", [], [element]) =>
            if Type.compare (Term.type_of element, intSyntax.int_ty) = EQUAL
            then raise ERR "set_sort_marker"
              "integer Set sort is metadata, not an object term"
            else Term.mk_var ("@cpc.Set",
              Type.--> (Term.type_of element, Type.bool))
        | _ => raise ERR "set_sort_marker" "expected a Set sort marker"
      fun as_sort_marker token indices args =
        case (token, indices, args) of
          ("as", [], [term, sort]) =>
            if Type.compare (Term.type_of term, Term.type_of sort) = EQUAL
            then term
            else raise ERR "as_sort_marker" "qualification sort mismatch"
        | _ => raise ERR "as_sort_marker" "expected a qualified term"
      (* The source translation dictionary is deliberately as narrow as its
         declared logic.  CPC arithmetic lemmas may nevertheless contain
         rationals and their Real coercions, so add the mixed arithmetic
         overloads only while reading the proof. *)
      val tmdict = with_cpc_deindexed_entries tmdict
      val tmdict = Library.extend_dict (("String", string_sort_marker),
        Library.extend_dict (("Bool", bool_sort_marker),
          Library.extend_dict (("Bag", bag_sort_marker),
            Library.extend_dict (("Set", set_sort_marker),
              Library.extend_dict (("as", as_sort_marker),
                Library.union_dict tmdict
                  SmtLib_Theories.Reals_Ints.tmdict)))))
      val tmdict = with_cpc_parameterized_skolems tmdict
      val tmdict = Library.extend_dict
        (("@", SmtLib_Theories.apply_operator "@"), tmdict)
      val tmdict = Library.extend_dict (("=", cpc_equality_parsefn),
        Library.extend_dict (("distinct", cpc_distinct_parsefn), tmdict))
    in
    (Library.extend_dict (("->", cpc_function_sort), tydict),
      Library.extend_dict (("str.++",
        cpc_concat_parsefn "smtstr_concat"),
      Library.extend_dict (("re.++",
        cpc_concat_parsefn "reglan_concat"),
      Library.extend_dict (("re.union",
        cpc_concat_parsefn "reglan_union"),
      Library.extend_dict (("re.inter",
        cpc_concat_parsefn "reglan_inter"),
      Library.extend_dict (("to_int", cpc_intreal_parsefn),
      Library.extend_dict (("to_real", cpc_intreal_parsefn),
      Library.extend_dict (("int.pow2", cpc_intreal_parsefn),
      Library.extend_dict (("div_total", cpc_arith_total_parsefn),
      Library.extend_dict (("mod_total", cpc_arith_total_parsefn),
      Library.extend_dict (("/_total", cpc_arith_total_parsefn),
      Library.extend_dict (("@int_div_by_zero", cpc_arith_total_parsefn),
      Library.extend_dict (("@mod_by_zero", cpc_arith_total_parsefn),
      Library.extend_dict (("@div_by_zero", cpc_arith_total_parsefn),
      Library.extend_dict (("**_total", cpc_arith_total_parsefn),
      Library.extend_dict (("bvsltbv", cpc_bv_parsefn),
      Library.extend_dict (("bvultbv", cpc_bv_parsefn),
      Library.extend_dict (("concat", cpc_bv_parsefn),
      Library.extend_dict (("@bit", cpc_bv_parsefn),
      Library.extend_dict (("@from_bools", cpc_bv_parsefn),
      Library.extend_dict (("@bvsize", cpc_bv_parsefn),
        Library.extend_dict (("@bv", cpc_bv_parsefn),
          Library.extend_dict (("_", cpc_literal_parsefn),
            with_cpc_fp_entries tmdict)))))))))))))))))))))))
    end

  fun cpc_indexed_identifier declared name =
    name = "BitVec" orelse name = "FloatingPoint" orelse
    List.exists (fn (family, _) => family <> "_" andalso family = name)
      cpc_indexed_term_families orelse
    (not (declared name) andalso
     String.isPrefix "bv" name andalso String.size name > 2 andalso
     List.all Char.isDigit
       (String.explode (String.extract (name, 2, NONE))))

  fun parse_term dicts_ref raw_get_token =
    let
      (* Keep the lexical spelling through the shared term parser.  Its
         [symbol_key] callback selects the semantic dictionary key, while
         the marked spelling tells overload dispatch that a quoted atom may
         not fall through to the unquoted literal catch-all. *)
      val get_token = raw_get_token
      val first = get_token ()
      val first_semantic = cpc_semantic_token first
      fun ordinary tokens = SmtLib_Parser.parse_term_with_cfg cpc_cfg
        (Library.undo_look_ahead tokens get_token) (!dicts_ref)
    in
      if first_semantic <> "(" then ordinary [first]
      else
        let
          val marked_head = get_token ()
          val head = cpc_semantic_token marked_head
        in
          if marked_head = "_" orelse marked_head = "@" then
            let
              val first_operand = get_token ()
              val application_token =
                Library.undo_look_ahead [first_operand] get_token

              fun application_terms terms =
                let val token = application_token () in
                  if token = ")" then List.rev terms
                  else application_terms
                    (parse_term dicts_ref
                       (Library.undo_look_ahead [token]
                         application_token) :: terms)
                end
            in
              if marked_head = "_" andalso
                 cpc_indexed_identifier
                   (fn name => Option.isSome
                     (Redblackmap.peek (#2 (!dicts_ref), name)))
                   first_operand then
                ordinary ["(", marked_head, first_operand]
              else case application_terms [] of
                function :: arguments =>
                  if List.null arguments then
                    raise ERR "parse_term"
                      "CPC `_` application expects an argument"
                  else SmtLib_Parser.apply_term (Lib.snd (!dicts_ref))
                    "@" [] (function :: arguments)
              | [] => raise ERR "parse_term"
                  "CPC `_` application expects a function"
            end
          (* CPC declares [is] as a parameterized constant whose first
             explicit argument is a constructor symbol, rather than as the
             indexed identifier used by SMT-LIB.  Keep that symbol opaque
             until the datatype scrutinee has been typed; in particular, do
             not elaborate it as a nullary constructor application. *)
          else if head = "is" then
            let
              val constructor = get_token ()
              val _ =
                if constructor = "(" orelse constructor = ")" then
                  raise ERR "parse_term"
                    "CPC datatype tester expects a constructor symbol"
                else ()
              val scrutinee = parse_term dicts_ref get_token
              val _ = Library.expect_token ")" (get_token ())
              val constructor_parameter = Term.mk_var
                (cpc_symbol_name "parse_term" constructor,
                 Type.gen_tyvar ())
              val (_, tmdict) = !dicts_ref
            in
              SmtLib_Parser.apply_term tmdict "is"
                [constructor_parameter] [scrutinee]
            end
          else if head = "@var" then
            let
              val var_name = cpc_var_name (get_token ())
              val var_type = parse_cpc_type get_token
                (#1 (!dicts_ref))
              val _ = Library.expect_token ")" (get_token ())
            in
              cpc_source_variable (var_name, var_type)
            end
          else if head = "forall" orelse head = "exists" orelse
                  head = "lambda" then
            let
              val binders = get_token ()
              fun bind vars body =
                let
                  val term =
                    if head = "forall" then
                      boolSyntax.list_mk_forall (vars, body)
                    else if head = "exists" then
                      boolSyntax.list_mk_exists (vars, body)
                    else Term.list_mk_abs (vars, body)
                  val _ = record_cpc_binder_block
                    (head, List.length vars, term)
                in
                  term
                end
            in
              case lookup_cpc_list binders of
                SOME vars =>
                  let
                    val body = parse_term dicts_ref get_token
                    val _ = Library.expect_token ")" (get_token ())
                  in
                    bind vars body
                  end
              | NONE =>
                  if binders = "(" then
                    let
                      val binder_head = get_token ()
                      fun inline_binders terms =
                        let val token = get_token () in
                          if token = ")" then List.rev terms
                          else inline_binders
                            (parse_term dicts_ref
                              (Library.undo_look_ahead [token] get_token) ::
                             terms)
                        end
                    in
                      if binder_head = "@list" then
                        let
                          val vars = inline_binders []
                          val body = parse_term dicts_ref get_token
                          val _ = Library.expect_token ")" (get_token ())
                        in
                          bind vars body
                        end
                      else ordinary
                        ["(", marked_head, binders, binder_head]
                    end
                  else raise ERR "parse_term"
                    ("undefined CPC @list alias " ^ binders ^
                     " (known aliases: " ^
                     String.concatWith ", " (List.rev (!cpc_list_names)) ^ ")")
            end
          else ordinary ["(", marked_head]
        end
    end

  datatype raw_term =
      RawAtom of string
    | RawList of raw_term list

  (* CPC represents a datatype tester as the parameterized application
       (is Constructor scrutinee)
     even when it occurs below equality or another proof argument.  The
     shared SMT-LIB parser deliberately accepts only the standard indexed
     spelling.  Normalize the complete raw occurrence tree before
     elaboration so nested CPC testers take the same registered dictionary
     path as ((_ is Constructor) scrutinee).  Malformed arities remain
     untouched and therefore retain the ordinary parser diagnostic.
     CPC also spells higher-order application (_ f x).  Normalize nested
     occurrences to the shared parser's @ spelling, retaining genuine
     indexed identifiers and the heads of indexed operator applications. *)
  fun normalize_cpc_testers indexed raw =
    case raw of
      RawList [RawAtom "is", RawAtom constructor, scrutinee] =>
        RawList
          [RawList [RawAtom "_", RawAtom "is", RawAtom constructor],
           normalize_cpc_testers indexed scrutinee]
    | RawList [RawAtom "and"] => RawAtom "true"
    | RawList [RawAtom "or"] => RawAtom "false"
    | RawList [RawAtom "and", operand] =>
        normalize_cpc_testers indexed operand
    | RawList [RawAtom "or", operand] =>
        normalize_cpc_testers indexed operand
    | RawList (RawAtom "_" :: (operands as RawAtom name :: _)) =>
        if indexed name then raw
        else RawList (RawAtom "@" ::
          List.map (normalize_cpc_testers indexed) operands)
    | RawList (RawAtom "_" :: operands) =>
        RawList (RawAtom "@" :: List.map (normalize_cpc_testers indexed) operands)
    | RawList ((head as RawList (RawAtom "_" :: _)) :: operands) =>
        RawList (head :: List.map (normalize_cpc_testers indexed) operands)
    | RawList entries => RawList (List.map (normalize_cpc_testers indexed) entries)
    | RawAtom _ => raw

  fun read_raw_term get_token =
    case get_token () of
      "(" =>
        let
          fun entries acc =
            case get_token () of
              ")" => RawList (List.rev acc)
            | token => entries
                (read_raw_term
                  (Library.undo_look_ahead [token] get_token) :: acc)
        in
          entries []
        end
    | ")" => raise ERR "read_raw_term" "unexpected closing parenthesis"
    | token => RawAtom token

  fun raw_tokens raw =
    case raw of
      RawAtom token => [token]
    | RawList entries =>
        "(" :: List.concat (List.map raw_tokens entries) @ [")"]

  (* Shared syntax-only validation; no term elaboration or mutable
     parser dictionaries enter this check. *)
  fun validate_raw_term raw_error raw =
    let
    fun member token choices = List.exists (Lib.equal token) choices
    fun quoted_symbol token =
      SmtLib_Parser.proof_quoted_symbol_token token
    fun token_text token =
      Option.getOpt (quoted_symbol token, token)
    fun unquoted_is expected token =
      not (Option.isSome (quoted_symbol token)) andalso token = expected
    fun string_literal token =
      Option.isSome (SmtLib_Parser.proof_string_token token)
    val reserved =
      ["_", "!", "as", "let", "forall", "exists", "lambda",
       "match", "par"]
    fun all_chars predicate text =
      List.all predicate (String.explode text)
    fun ascii_letter c =
      (#"a" <= c andalso c <= #"z") orelse
      (#"A" <= c andalso c <= #"Z")
    fun simple_initial c =
      ascii_letter c orelse
      member c [#"~", #"!", #"@", #"$", #"%", #"^", #"&",
        #"*", #"_", #"-", #"+", #"=", #"<", #">", #".",
        #"?", #"/"]
    fun simple_symbol text =
      String.size text > 0 andalso
      simple_initial (String.sub (text, 0)) andalso
      all_chars (fn c => simple_initial c orelse Char.isDigit c) text
    fun keyword token =
      not (Option.isSome (quoted_symbol token)) andalso
      String.size token > 1 andalso String.sub (token, 0) = #":" andalso
      simple_symbol (String.extract (token, 1, NONE))
    fun digits text =
      String.size text > 0 andalso all_chars Char.isDigit text
    fun numeral text =
      text = "0" orelse
      (String.size text > 0 andalso String.sub (text, 0) <> #"0" andalso
       digits text)
    fun decimal text =
      case String.fields (Lib.equal #".") text of
        [whole, fraction] => numeral whole andalso digits fraction
      | _ => false
    fun radix_literal prefix predicate text =
      String.isPrefix prefix text andalso String.size text > 2 andalso
      all_chars predicate (String.extract (text, 2, NONE))
    fun hex_digit c =
      Char.isDigit c orelse (#"a" <= c andalso c <= #"f") orelse
      (#"A" <= c andalso c <= #"F")
    fun hexadecimal text =
      radix_literal "#x" hex_digit text
    fun binary text =
      radix_literal "#b" (fn c => c = #"0" orelse c = #"1") text
    fun unsigned_number text = numeral text orelse decimal text
    fun signed_number text =
      String.size text > 1 andalso String.sub (text, 0) = #"-" andalso
      unsigned_number (String.extract (text, 1, NONE))
    fun rational text =
      case String.fields (Lib.equal #"/") text of
        [numerator, denominator] =>
          (numeral numerator orelse signed_number numerator) andalso
          numeral denominator andalso denominator <> "0"
      | _ => false
    fun literal token =
      string_literal token orelse numeral token orelse decimal token orelse
      hexadecimal token orelse binary token orelse signed_number token orelse
      rational token
    fun valid_quoted text =
      (SmtLib_String_Literal.validate_lexical_text true text; true)
      handle SmtLib_String_Literal.InvalidStringLiteral _ => false
    fun validate_symbol description token =
      case SmtLib_Parser.proof_string_token token of
        SOME _ => raw_error
          ("string literal is not a valid " ^ description)
      | NONE =>
          (case quoted_symbol token of
             SOME text =>
               if valid_quoted text then ()
               else raw_error ("invalid quoted " ^ description)
           | NONE =>
               if simple_symbol token andalso not (keyword token) andalso
                  not (member token reserved)
               then ()
               else raw_error
                 ("invalid " ^ description ^ " '" ^ token ^ "'"))
    val validate_identifier_symbol = validate_symbol
    fun validate_index raw =
      case raw of
        RawAtom token =>
          if Option.isSome (quoted_symbol token) then
            validate_symbol "indexed-identifier index" token
          else if numeral token then ()
          else validate_identifier_symbol
            "indexed-identifier index" token
      | RawList _ => raw_error "indexed-identifier index is not atomic"
    fun validate_simple_identifier description raw =
      case raw of
        RawAtom token => validate_identifier_symbol description token
      | RawList (RawAtom marker :: RawAtom name :: indices) =>
          if unquoted_is "_" marker then
            (validate_identifier_symbol
               ("indexed " ^ description ^ " name") name;
             if List.null indices then
               raw_error ("indexed " ^ description ^
                 " requires at least one index")
             else List.app validate_index indices)
          else raw_error
            (description ^ " is not a simple/indexed identifier")
      | RawList _ =>
          raw_error (description ^ " is not a simple/indexed identifier")
    fun validate_sort raw =
      case raw of
        RawAtom _ => validate_simple_identifier "sort identifier" raw
      | RawList (RawAtom marker :: RawAtom _ :: _) =>
          if unquoted_is "_" marker then
            validate_simple_identifier "sort identifier" raw
          else validate_sort_application raw
      | RawList [] => raw_error "empty sort"
      | RawList _ => validate_sort_application raw
    and validate_sort_application raw =
      case raw of
        RawList (head :: arguments) =>
          (validate_simple_identifier "sort application head" head;
           if List.null arguments then
             raw_error "sort application requires at least one argument"
           else List.app validate_sort arguments)
      | _ => raw_error "malformed sort application"
    fun validate_identifier raw =
      case raw of
        RawAtom _ => validate_simple_identifier "identifier" raw
      | RawList [RawAtom marker, identifier, sort] =>
          if unquoted_is "as" marker then
            (validate_simple_identifier "ascribed identifier" identifier;
             validate_sort sort)
          else if unquoted_is "_" marker then
            validate_simple_identifier "identifier" raw
          else raw_error
            "application head is not a qualified identifier"
      | RawList (RawAtom marker :: _) =>
          if unquoted_is "as" marker then
            raw_error
              "qualified identifier 'as' expects an identifier and sort"
          else if unquoted_is "_" marker then
            validate_simple_identifier "identifier" raw
          else raw_error
            "application head is not a qualified identifier"
      | RawList _ => raw_error
          "application head is not a qualified identifier"
    fun validate_sorted_variable raw =
      case raw of
        RawList [RawAtom name, sort] =>
          (validate_symbol "bound variable" name; validate_sort sort)
      | _ => raw_error
          "sorted variable must have the form (name sort)"
    fun validate_cpc_var name sort =
      (case SmtLib_Parser.proof_string_token name of
         SOME _ => ()
       | NONE => validate_symbol "bound variable" name;
       validate_sort sort)
    fun validate_binders binders =
      case binders of
        RawAtom alias => validate_symbol "CPC binder-list alias" alias
      | RawList (RawAtom marker :: variables) =>
          if unquoted_is "@list" marker then
            if List.null variables then
              raw_error "CPC binder list must be nonempty"
            else List.app (fn variable =>
              case variable of
                RawAtom alias =>
                  validate_symbol "CPC bound-variable alias" alias
              | RawList [RawAtom var_marker, RawAtom name, sort] =>
                  if unquoted_is "@var" var_marker then
                    validate_cpc_var name sort
                  else raw_error
                    "CPC binder must be an alias or (@var name sort)"
              | _ => raw_error
                  "CPC binder must be an alias or (@var name sort)")
              variables
          else validate_sorted_variables binders
      | RawList _ => validate_sorted_variables binders
    and validate_sorted_variables binders =
      case binders of
        RawList variables =>
          if List.null variables then
            raw_error "sorted-variable list must be nonempty"
          else List.app validate_sorted_variable variables
      | _ => raw_error "sorted-variable list must be parenthesized"
    fun validate_pattern pattern =
      case pattern of
        RawAtom name => validate_symbol "match pattern" name
      | RawList (RawAtom constructor :: variables) =>
          (validate_symbol "match constructor" constructor;
           if List.null variables then
             raw_error "constructor pattern requires at least one variable"
           else List.app (fn variable => case variable of
               RawAtom name => validate_symbol "match binder" name
             | RawList _ => raw_error "match binder is not atomic")
             variables)
      | RawList _ => raw_error "malformed match pattern"
    fun validate_sexp sexp =
      case sexp of
        RawAtom token =>
          if literal token orelse keyword token then ()
          else validate_symbol "annotation s-expression atom" token
      | RawList entries => List.app validate_sexp entries
    fun validate_attributes attributes =
      let
        fun loop [] = ()
          | loop (RawAtom attribute :: rest) =
              if not (keyword attribute) then
                raw_error "annotation expects an attribute keyword"
              else
                (case rest of
                   RawAtom next :: _ =>
                     if keyword next then loop rest
                     else (validate_sexp (List.hd rest);
                           loop (List.tl rest))
                 | RawList value :: tail =>
                     (validate_sexp (RawList value); loop tail)
                 | [] => ())
          | loop _ = raw_error "annotation expects an attribute keyword"
      in
        if List.null attributes then
          raw_error "annotation requires at least one attribute"
        else loop attributes
      end
    fun validate_application_arity head operands =
      let
        fun exact expected =
          if List.length operands = expected then ()
          else raw_error ("'" ^ head ^ "' expects exactly " ^
            Int.toString expected ^ " operand(s)")
        fun at_least expected =
          if List.length operands >= expected then ()
          else raw_error ("'" ^ head ^ "' expects at least " ^
            Int.toString expected ^ " operand(s)")
      in
        case head of
          "true" => raw_error "'true' must be an atomic term"
        | "false" => raw_error "'false' must be an atomic term"
        | "not" => exact 1
        | "ite" => exact 3
        | "=" => at_least 2
        | "distinct" => at_least 2
        | "=>" => at_least 2
        | "and" => at_least 2
        | "or" => at_least 2
        | "xor" => at_least 2
        | _ => at_least 1
      end
    fun validate_raw raw =
      case raw of
        RawAtom token =>
          if literal token then ()
          else validate_identifier_symbol "term identifier" token
      | RawList (RawAtom marked_head :: rest) =>
          let
            val head = token_text marked_head
            val special =
              not (Option.isSome (quoted_symbol marked_head))
            fun special_head name = special andalso head = name
          in
            if special_head "as" then
              (case rest of
                 [identifier, sort] =>
                   (validate_simple_identifier
                      "ascribed identifier" identifier;
                    validate_sort sort)
               | _ => raw_error
                   ("qualified identifier 'as' expects an identifier " ^
                    "and sort"))
            else if special_head "_" then
              validate_simple_identifier "identifier" raw
            else if member head ["forall", "exists", "lambda"] andalso
                    special then
              (case rest of
                 [binders, body] =>
                   (validate_binders binders; validate_raw body)
               | _ => raw_error ("malformed " ^ head ^ " binder"))
            else if special_head "let" then
              (case rest of
                 [RawList bindings, body] =>
                   (if List.null bindings then
                      raw_error "let requires at least one binding"
                    else List.app (fn binding => case binding of
                        RawList [RawAtom name, rhs] =>
                          (validate_symbol "let variable" name;
                           validate_raw rhs)
                      | _ => raw_error
                          "let binding must have the form (name term)")
                      bindings;
                    validate_raw body)
               | _ => raw_error "malformed let term")
            else if special_head "!" then
              (case rest of
                 term :: attributes =>
                   (validate_raw term; validate_attributes attributes)
               | [] => raw_error "annotation is missing its term")
            else if special_head "match" then
              (case rest of
                 [scrutinee, RawList branches] =>
                   (validate_raw scrutinee;
                    if List.null branches then
                      raw_error "match requires at least one branch"
                    else List.app (fn branch => case branch of
                        RawList [pattern, body] =>
                          (validate_pattern pattern; validate_raw body)
                      | _ => raw_error
                          "match branch must have pattern and body")
                        branches)
               | _ => raw_error
                   "match expects a scrutinee and parenthesized branches")
            else if special_head "set.comprehension" then
              (case rest of
                 [binders as RawList (RawList _ :: _), predicate, value] =>
                   (validate_binders binders;
                    validate_raw predicate;
                    validate_raw value)
               | _ =>
                   (validate_identifier_symbol
                      "application head" marked_head;
                    validate_application_arity head rest;
                    List.app validate_raw rest))
            else if special_head "@list" then List.app validate_raw rest
            else if special_head "@" then
              (case rest of
                 rator :: arguments =>
                   if List.null arguments then
                     raw_error "'@' expects a rator and at least one operand"
                   else
                     (validate_raw rator; List.app validate_raw arguments)
               | [] => raw_error
                   "'@' expects a rator and at least one operand")
            else if special_head "@var" then
              (case rest of
                 [RawAtom name, sort] => validate_cpc_var name sort
               | _ => raw_error "@var expects a name and sort")
            else if special_head "is" then
              (case rest of
                 [RawAtom constructor, scrutinee] =>
                   (validate_symbol "tester constructor" constructor;
                    validate_raw scrutinee)
               | _ => raw_error
                   "CPC datatype tester expects a constructor and scrutinee")
            else
              (validate_identifier_symbol "application head" marked_head;
               if special then validate_application_arity head rest else
                 if List.null rest then
                   raw_error
                     "function application requires at least one argument"
                 else ();
               List.app validate_raw rest)
          end
      | RawList (head :: operands) =>
          (validate_identifier head;
           if List.null operands then
             raw_error "function application requires at least one argument"
           else List.app validate_raw operands)
      | RawList [] => raw_error "empty term"
    in validate_raw raw end

  fun raw_contains_let raw =
    case raw of
      RawAtom _ => false
    | RawList (RawAtom "let" :: _) => true
    | RawList entries => List.exists raw_contains_let entries

  fun exact_application head operands =
    ApplicationProvenance (head, operands)

  fun exact_binders head names body =
    BinderBlockProvenance (head, List.length names, body)

  (* Equality endpoints are semantic inputs to omitted SYM, TRANS,
     EQ_RESOLVE, and CONG.  Retain their boundary even when both endpoints
     are conjunction-free; AtomicProvenance for the whole equality would
     erase which exact side an equality-consuming route selected. *)
  fun sparse_equality left right = EqualityProvenance (left, right)

  fun lookup_lexical_provenance environment name =
    let
      val key = provenance_key name
      fun lookup [] = NONE
        | lookup ((bound, provenance) :: rest) =
            if provenance_key bound = key then SOME provenance
            else lookup rest
    in
      lookup environment
    end

  fun binder_names raw =
    case raw of
      RawList (RawAtom "@list" :: binders) =>
        let
          fun binder_name (RawAtom alias) = alias
            | binder_name (RawList
                [RawAtom "@var", RawAtom name, _]) = cpc_var_name name
            | binder_name _ = raise ERR "provenance_of_raw"
                "unsupported CPC inline binder"
        in
          SOME (List.map binder_name binders)
          handle Feedback.HOL_ERR _ => NONE
        end
    | RawList binders =>
        let
          fun binder_name (RawList [RawAtom name, _]) = name
            | binder_name _ = raise ERR "provenance_of_raw"
                "unsupported SMT-LIB binder declaration"
        in
          SOME (List.map binder_name binders)
          handle Feedback.HOL_ERR _ => NONE
        end
    | RawAtom alias =>
        (case lookup_cpc_list alias of
           SOME variables =>
             (SOME (List.map (Lib.fst o Term.dest_var) variables)
              handle Feedback.HOL_ERR _ => NONE)
         | NONE => NONE)

  fun let_bindings environment raw =
    case raw of
      RawList bindings =>
        let
          fun binding (RawList [RawAtom name, rhs]) =
                (provenance_key name,
                 provenance_of_raw_in environment rhs)
            | binding _ = raise ERR "provenance_of_raw"
                "unsupported SMT-LIB let binding"
        in
          SOME (List.map binding bindings)
          handle Feedback.HOL_ERR _ => NONE
        end
    | _ => NONE

  and provenance_of_raw_in environment raw =
    case raw of
      RawAtom token =>
        (case lookup_lexical_provenance environment token of
           SOME provenance => provenance
         | NONE =>
             (case lookup_term_provenance token of
                SOME provenance => provenance
              | NONE => AtomicProvenance))
    | RawList (RawAtom "and" :: operands) =>
        if List.length operands >= 2 then
          ConjunctionProvenance
            (ParsedConjunction,
             List.map (provenance_of_raw_in environment) operands)
        else UnavailableProvenance
          "parsed CPC conjunction has fewer than two operands"
    | RawList [RawAtom "=", left, right] =>
        sparse_equality (provenance_of_raw_in environment left)
          (provenance_of_raw_in environment right)
    | RawList [RawAtom head, binders, body] =>
        if head = "forall" orelse head = "exists" orelse
           head = "lambda"
         then
          (case binder_names binders of
             SOME names => exact_binders head names
               (provenance_of_raw_in
                 (List.map (fn name =>
                    (provenance_key name, AtomicProvenance)) names @
                  environment) body)
           | NONE => UnavailableProvenance
               ("unsupported " ^ head ^ " binder provenance"))
        else if head = "let" then
          (case let_bindings environment binders of
             SOME bindings =>
               provenance_of_raw_in (bindings @ environment) body
           | NONE => UnavailableProvenance
               "unsupported SMT-LIB let provenance")
        else exact_application head
          [provenance_of_raw_in environment binders,
           provenance_of_raw_in environment body]
    | RawList (RawAtom head :: operands) =>
        if List.exists (fn private_name => private_name = head)
             ["@fp.SIGN", "@fp.EXPONENT", "@fp.SIGNIFICAND",
              "@fp.ZERO", "@fp.NAN", "@fp.INF",
              "@fp.RMBITBLAST"] then
          AtomicProvenance
        else if head = "match" orelse head = "par" then
          UnavailableProvenance
            ("unsupported binding form " ^ head)
        else if head = "@var" then AtomicProvenance
        else exact_application head
          (List.map (provenance_of_raw_in environment) operands)
    | RawList entries =>
        exact_application "<computed-head>"
          (List.map (provenance_of_raw_in environment) entries)

  fun provenance_of_raw raw = provenance_of_raw_in [] raw

  (* Read exactly one CPC occurrence before elaborating it to HOL.  The raw
     occurrence tree retains every path to a nested conjunction and every
     conjunction's exact operand boundaries.  Conjunction-free subtrees use
     one atomic marker; no HOL-term equality participates in provenance
     recovery. *)
  fun parse_located_term dicts_ref get_token : located_term =
    let
      val raw = normalize_cpc_testers
        (cpc_indexed_identifier (fn name => Option.isSome
          (Redblackmap.peek (#2 (!dicts_ref), name))))
        (read_raw_term get_token)
      val tokens = ref (raw_tokens raw)
      fun next_token () =
        case !tokens of
          token :: rest => (tokens := rest; token)
        | [] => raise ERR "parse_located_term"
            "internal CPC occurrence token stream exhausted"
      val parsed_term = parse_term dicts_ref next_token
      val _ = List.null (!tokens) orelse
        raise ERR "parse_located_term"
          "internal CPC occurrence parser left trailing tokens"
      (* SMT-LIB lets elaborate to kernel LET applications, while the exact
         lexical provenance above already describes their simultaneous,
         capture-avoiding substitution.  Reduce precisely those occurrences
         before pairing the HOL term with that substituted occurrence tree.
         The conversion is proof-producing; aliases consequently store the
         same normalized term/provenance pair as direct commands. *)
      val term =
        if raw_contains_let raw then
          boolSyntax.rhs (Thm.concl
            (Conv.DEPTH_CONV pairLib.let_CONV parsed_term))
          handle Conv.UNCHANGED => parsed_term
        else parsed_term
    in
      {term = term, provenance = provenance_of_raw raw}
    end

  fun parse_recorded_term dicts_ref get_token =
    #term (parse_located_term dicts_ref get_token)

  fun unavailable_term reason term : located_term =
    {term = term, provenance = UnavailableProvenance reason}

  fun skip_sexp get_token =
    let
      fun skip depth =
        case get_token () of
          "(" => skip (depth + 1)
        | ")" => if depth = 0 then () else skip (depth - 1)
        | _ => skip depth
    in
      skip 0
    end

  (* Read the remainder of a declaration after its command name.  We use the
     token copy both to decide whether it redeclares a symbol already supplied
     by HolSmt's translation dictionaries and, when it does not, to feed the
     ordinary SMT-LIB declaration parsers. *)
  fun declaration_tokens get_token =
    let
      fun loop depth acc =
        let val token = get_token () in
          case token of
            "(" => loop (depth + 1) (token :: acc)
          | ")" => if depth = 0 then List.rev (token :: acc)
                   else loop (depth - 1) (token :: acc)
          | _ => loop depth (token :: acc)
        end
    in
      loop 0 []
    end

  fun datatype_binding_names tokens =
    let
      fun bindings ("(" :: name :: _ :: ")" :: rest) acc =
            bindings rest (name :: acc)
        | bindings (")" :: _) acc = List.rev acc
        | bindings _ _ = []
    in
      case tokens of "(" :: rest => bindings rest [] | _ => []
    end

  type term_declaration = {
    key: string,
    name: string,
    domain: Type.hol_type list,
    range: Type.hol_type,
    parse: Term.term SmtLib_Parser.parse_fn
  }

  fun parse_term_declaration parse_domain get_token (tydict, _) =
    let
      val marked_name = get_token ()
      val key = cpc_symbol_key "parse_declaration" marked_name
      val name = cpc_symbol_name "parse_declaration" marked_name
      val domain =
        if parse_domain then parse_cpc_type_list get_token tydict
        else []
      val range = parse_cpc_type get_token tydict
      val _ = Library.expect_token ")" (get_token ())
      val tm = cpc_source_variable
        (name, boolSyntax.list_mk_fun (domain, range))
      fun parse _ indices args =
        if not (List.null indices) orelse
           (parse_domain andalso
            List.length args <> List.length domain) then
          raise ERR ("<" ^ name ^ ">")
            "wrong number of CPC declaration arguments"
        else
          Term.list_mk_comb (tm, args)
          handle Feedback.HOL_ERR holerr =>
            raise ERR ("<" ^ name ^ ">")
              ("ill-typed CPC declaration application: " ^
               Feedback.message_of holerr)
    in
      {key = key, name = name, domain = domain,
       range = range, parse = parse}
    end

  fun declaration_compatible tmdict
      ({key, domain, range, ...}: term_declaration) =
    let
      fun make_args _ [] = []
        | make_args index (ty :: rest) =
            Term.mk_var
              ("cpc_decl_arg" ^ Int.toString index, ty) ::
            make_args (index + 1) rest
      val signatures =
        if List.null domain andalso Lib.can Type.dom_rng range then
          let val (function_domain, function_range) =
            boolSyntax.strip_fun range
          in
            [([], range), (function_domain, function_range)]
          end
        else [(domain, range)]
      val candidates =
        case Redblackmap.peek (tmdict, key) of
          SOME parsefns => parsefns
        | NONE => []
      fun compatible_signature parsefn (argument_types, result_type) =
        Type.compare
          (Term.type_of
             (parsefn (SmtLib_Parser.proof_symbol_text key) []
               (make_args 0 argument_types)),
           result_type) = EQUAL
        handle Feedback.HOL_ERR _ => false
             | _ => false
      fun compatible parsefn =
        List.exists (compatible_signature parsefn) signatures
    in
      List.exists compatible candidates
    end

  fun parse_or_keep_term_declaration parse_domain dicts_ref get_token =
    let
      val tokens = declaration_tokens get_token
      val declaration = parse_term_declaration parse_domain
        (Library.undo_look_ahead tokens get_token) (!dicts_ref)
      val (tydict, tmdict) = !dicts_ref
      val {key, name, parse, ...} = declaration
      val source_symbol = set_member (!cpc_source_term_symbols) key
      val proof_symbol = set_member (!cpc_proof_term_symbols) key
      val builtin_symbol = set_member (!cpc_reserved_symbols) key orelse
        set_member (!cpc_reserved_symbols) name
      fun incompatible () = raise ERR "parse_declaration"
        ("incompatible redeclaration of CPC symbol " ^ name)
    in
      if builtin_symbol then
        raise ERR "parse_declaration"
          ("CPC declaration may not shadow builtin symbol " ^ name)
      else if proof_symbol then
        raise ERR "parse_declaration"
          ("duplicate CPC declaration of symbol " ^ name)
      else if source_symbol then
        if declaration_compatible tmdict declaration then ()
        else incompatible ()
      else if Option.isSome (Redblackmap.peek (tmdict, key)) then
        incompatible ()
      else
        (dicts_ref :=
           (tydict, Library.extend_dict ((key, parse), tmdict));
         cpc_proof_term_symbols :=
           HOLset.add (!cpc_proof_term_symbols, key))
    end

  val parse_declare_const = false
  val parse_declare_fun = true

  fun parse_declare_sort get_token (tydict, tmdict) =
    let
      val marked_name = get_token ()
      val key = cpc_symbol_key "parse_declare_sort" marked_name
      val name = cpc_symbol_name "parse_declare_sort" marked_name
      val arity_text = get_token ()
      val arity =
        case Int.fromString arity_text of
          SOME value =>
            if value < 0 then raise ERR "parse_declare_sort"
              "CPC sort arity must be non-negative"
            else value
        | NONE => raise ERR "parse_declare_sort"
            "CPC sort arity must be a numeral"
      val _ = Library.expect_token ")" (get_token ())
      val ty = Type.mk_vartype ("'cpc_" ^ name)
      fun parsefn _ indices args =
        if List.null indices andalso arity = 0 andalso List.null args then ty
        else raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
    in
      {key = key, name = name, arity = arity, parse = parsefn,
       dicts = (tydict, tmdict)}
    end

  fun sort_declaration_compatible tydict key arity =
    let
      val arguments = List.tabulate (arity, fn index =>
        Type.mk_vartype ("'cpc_sort_arg" ^ Int.toString index))
    in
      case Redblackmap.peek (tydict, key) of
        NONE => false
      | SOME parsefns => List.exists
          (fn parsefn =>
            (ignore
               (parsefn (SmtLib_Parser.proof_symbol_text key) [] arguments);
             true)
            handle Feedback.HOL_ERR _ => false
                 | _ => false) parsefns
    end

  fun parse_or_keep_sort_declaration dicts_ref get_token =
    let
      val tokens = declaration_tokens get_token
      val declaration = parse_declare_sort
        (Library.undo_look_ahead tokens get_token) (!dicts_ref)
      val {key, name, arity, parse, dicts = (tydict, tmdict)} = declaration
      val source_symbol = set_member (!cpc_source_sort_symbols) key
      val proof_symbol = set_member (!cpc_proof_sort_symbols) key
      val builtin_symbol = set_member (!cpc_reserved_symbols) key orelse
        set_member (!cpc_reserved_symbols) name
    in
      if builtin_symbol then
        raise ERR "parse_declaration"
          ("CPC declaration may not shadow builtin sort " ^ name)
      else if proof_symbol then
        raise ERR "parse_declaration"
          ("duplicate CPC declaration of sort " ^ name)
      else if source_symbol then
        if sort_declaration_compatible tydict key arity then ()
        else raise ERR "parse_declaration"
          ("incompatible redeclaration of CPC sort " ^ name)
      else if arity <> 0 then
        raise ERR "parse_declaration"
          ("unsupported non-nullary CPC sort declaration " ^ name)
      else if Option.isSome (Redblackmap.peek (tydict, key)) then
        raise ERR "parse_declaration"
          ("incompatible redeclaration of CPC sort " ^ name)
      else
        (dicts_ref :=
           (Library.extend_dict ((key, parse), tydict), tmdict);
         cpc_proof_sort_symbols :=
           HOLset.add (!cpc_proof_sort_symbols, key))
    end

  type datatype_selector = {
    key: string,
    name: string,
    sort: raw_term
  }

  type datatype_constructor = {
    key: string,
    name: string,
    selectors: datatype_selector list
  }

  type datatype_declaration = {
    sort_key: string,
    sort_name: string,
    arity: int,
    params: string list,
    constructors: datatype_constructor list
  }

  fun all_chars predicate text =
    List.all predicate (String.explode text)

  fun valid_simple_symbol text =
    let
      fun letter c =
        (#"a" <= c andalso c <= #"z") orelse
        (#"A" <= c andalso c <= #"Z")
      fun initial c =
        letter c orelse List.exists (Lib.equal c)
          [#"~", #"!", #"@", #"$", #"%", #"^", #"&", #"*",
           #"_", #"-", #"+", #"=", #"<", #">", #".", #"?", #"/"]
    in
      String.size text > 0 andalso initial (String.sub (text, 0)) andalso
      all_chars (fn c => initial c orelse Char.isDigit c) text
    end

  fun datatype_symbol_using symbol_key where_ role token =
    let
      val key = symbol_key token
      val name = SmtLib_Parser.proof_symbol_text key
      val _ =
        case SmtLib_Parser.proof_quoted_symbol_token token of
          SOME _ => ()
        | NONE =>
            if valid_simple_symbol token andalso
               String.sub (token, 0) <> #":" then ()
            else raise ERR where_
              ("invalid " ^ role ^ " name '" ^ token ^ "'")
    in
      (key, name)
    end

  fun datatype_symbol where_ role token =
    datatype_symbol_using (cpc_symbol_key where_) where_ role token

  fun distinct_datatype_names where_ role names =
    let
      fun loop _ [] = ()
        | loop seen ((key, name) :: rest) =
            if set_member seen key then raise ERR where_
              ("duplicate " ^ role ^ " name " ^ name)
            else loop (HOLset.add (seen, key)) rest
    in
      loop (HOLset.empty String.compare) names
    end

  fun datatype_arity where_ name text =
    case Int.fromString text of
      SOME arity =>
        if arity >= 0 andalso all_chars Char.isDigit text andalso
           String.size text > 0 then arity
        else raise ERR where_
          ("datatype arity for '" ^ name ^ "' must be a natural numeral")
    | NONE => raise ERR where_
        ("datatype arity for '" ^ name ^ "' must be a natural numeral")

  fun parse_datatype_body_using symbol_key where_ sort_key sort_name arity body =
    let
      val (param_tokens, constructor_raws) =
        case body of
          RawList [RawAtom "par", RawList params, RawList constructors] =>
            (params, constructors)
        | RawList (RawAtom "par" :: _) => raise ERR where_
            "parametric datatype body must be (par (params) (constructors))"
        | RawList constructors => ([], constructors)
        | RawAtom _ => raise ERR where_ "datatype body must be parenthesized"
      fun parameter raw =
        case raw of
          RawAtom token => datatype_symbol_using symbol_key where_ "datatype parameter" token
        | RawList _ => raise ERR where_ "datatype parameter must be a symbol"
      val parameter_names = List.map parameter param_tokens
      val _ = distinct_datatype_names where_ "datatype parameter"
        parameter_names
      val _ =
        if List.length parameter_names = arity then ()
        else raise ERR where_
          ("datatype arity for '" ^ sort_name ^ "' is " ^
           Int.toString arity ^ " but its body has " ^
           Int.toString (List.length parameter_names) ^ " parameter(s)")
      fun selector raw : datatype_selector =
        case raw of
          RawList [RawAtom token, sort] =>
            let val (key, name) =
              datatype_symbol_using symbol_key where_ "datatype selector" token
            in {key = key, name = name, sort = sort} end
        | _ => raise ERR where_
            "datatype selector must have the form (name sort)"
      fun constructor raw : datatype_constructor =
        case raw of
          RawList (RawAtom token :: selector_raws) =>
            let
              val (key, name) =
                datatype_symbol_using symbol_key where_ "datatype constructor" token
              val selectors = List.map selector selector_raws
              val _ = distinct_datatype_names where_ "datatype selector"
                (List.map (fn ({key, name, ...}: datatype_selector) =>
                  (key, name)) selectors)
            in
              {key = key, name = name, selectors = selectors}
            end
        | _ => raise ERR where_
            "datatype constructor must be a nonempty parenthesized form"
      val _ = if List.null constructor_raws then
          raise ERR where_ "datatype constructor list must be nonempty"
        else ()
      val constructors = List.map constructor constructor_raws
      val _ = distinct_datatype_names where_ "datatype constructor"
        (List.map (fn ({key, name, ...}: datatype_constructor) =>
          (key, name)) constructors)
      val selector_names = List.concat (List.map
        (fn ({selectors, ...}: datatype_constructor) => List.map
          (fn ({key, name, ...}: datatype_selector) => (key, name))
          selectors) constructors)
      val _ = distinct_datatype_names where_ "datatype selector"
        selector_names
    in
      {sort_key = sort_key, sort_name = sort_name, arity = arity,
       params = List.map #1 parameter_names, constructors = constructors}
    end

  fun parse_datatype_body where_ sort_key sort_name arity body =
    parse_datatype_body_using (cpc_symbol_key where_)
      where_ sort_key sort_name arity body

  fun source_sort_type where_ tydict key arguments =
    let
      val candidates =
        case Redblackmap.peek (tydict, key) of
          SOME parsefns => parsefns
        | NONE => []
      fun first [] = raise ERR where_
            ("source datatype sort " ^
             SmtLib_Parser.proof_symbol_text key ^ " is unavailable")
        | first (parsefn :: rest) =
            (parsefn (SmtLib_Parser.proof_symbol_text key) [] arguments
             handle Feedback.HOL_ERR _ => first rest
                  | _ => first rest)
    in
      first candidates
    end

  fun validate_datatype_declarations_using
      (namespace : SmtLib_GraphFrontend.namespace) dicts_ref declarations =
    let
      val (tydict, tmdict) = !dicts_ref
      val sort_names = List.map
        (fn ({sort_key, sort_name, ...}: datatype_declaration) =>
          (sort_key, sort_name)) declarations
      val _ = distinct_datatype_names "declare-datatypes" "datatype sort"
        sort_names
      val value_names = List.concat (List.map
        (fn ({constructors, ...}: datatype_declaration) =>
          List.concat (List.map
            (fn ({key, name, selectors}: datatype_constructor) =>
              (key, name) :: List.map
                (fn ({key, name, ...}: datatype_selector) => (key, name))
                selectors) constructors)) declarations)
      val _ = distinct_datatype_names "declare-datatypes"
        "datatype constructor/selector" value_names
      fun reject_sort ({sort_key, sort_name, arity, ...}:
          datatype_declaration) =
        if set_member (#reserved namespace) sort_key orelse
           set_member (#reserved namespace) sort_name then
          raise ERR "declare-datatypes"
            ("datatype may not shadow builtin sort " ^ sort_name)
        else if set_member (#proof_sorts namespace) sort_key then
          raise ERR "declare-datatypes"
            ("datatype sort conflicts with a proof declaration " ^ sort_name)
        else if not (set_member (#source_sorts namespace) sort_key) orelse
                not (sort_declaration_compatible tydict sort_key arity) then
          raise ERR "declare-datatypes"
            ("datatype sort is not identical to source sort " ^ sort_name)
        else ()
      val _ = List.app reject_sort declarations
      fun validate_one ({sort_key, sort_name, arity, params, constructors}:
          datatype_declaration) =
        let
          val param_tys = List.tabulate (arity, fn index =>
            Type.mk_vartype ("'cpc_datatype_param" ^ Int.toString index))
          val datatype_ty = source_sort_type "declare-datatypes" tydict
            sort_key param_tys
          val parameter_pairs = ListPair.zip (params, param_tys)
          fun add_parameter ((key, ty), dictionary) =
            let
              val name = SmtLib_Parser.proof_symbol_text key
              val _ =
                if set_member (#reserved namespace) key orelse
                   set_member (#reserved namespace) name orelse
                   set_member (#source_sorts namespace) key orelse
                   set_member (#proof_sorts namespace) key then
                  raise ERR "declare-datatypes"
                    ("datatype parameter shadows namespace symbol " ^ name)
                else ()
              fun parse _ indices arguments =
                if List.null indices andalso List.null arguments then ty
                else raise ERR "declare-datatypes"
                  ("datatype parameter " ^ name ^ " takes no arguments")
            in
              Library.extend_dict ((key, parse), dictionary)
            end
          val body_tydict = List.foldl add_parameter tydict parameter_pairs
          fun selector_type ({sort, ...}: datatype_selector) =
            let
              val tokens = ref (raw_tokens sort)
              fun next () =
                case !tokens of
                  token :: rest => (tokens := rest; token)
                | [] => raise ERR "declare-datatypes"
                    "datatype selector sort ended unexpectedly"
              val ty = parse_cpc_type next body_tydict
              val _ = if List.null (!tokens) then () else
                raise ERR "declare-datatypes"
                  "datatype selector sort has trailing syntax"
            in
              ty
            end
          fun constructor_domains ty =
            case Lib.total Type.dom_rng ty of
              NONE => []
            | SOME (domain, range) =>
                domain :: constructor_domains range
          val source_constructor_templates =
            TypeBase.constructors_of datatype_ty
            handle Feedback.HOL_ERR holerr =>
              raise ERR "declare-datatypes"
                ("source sort " ^ sort_name ^
                 " has no TypeBase datatype mapping: " ^
                 Feedback.message_of holerr)
          val source_constructors =
            List.map (TypeBasePure.cinst datatype_ty)
              source_constructor_templates
          val _ =
            if List.length constructors = List.length source_constructors
            then ()
            else raise ERR "declare-datatypes"
              ("datatype " ^ sort_name ^
               " constructor set is not identical to source: expected " ^
               Int.toString (List.length source_constructors) ^
               ", declared " ^ Int.toString (List.length constructors))
          fun require_source_symbol role key name =
            if set_member (#reserved namespace) key orelse
               set_member (#reserved namespace) name then
              raise ERR "declare-datatypes"
                ("datatype " ^ role ^ " may not shadow builtin symbol " ^
                 name)
            else if set_member (#proof_terms namespace) key then
              raise ERR "declare-datatypes"
                ("datatype " ^ role ^
                 " conflicts with a proof declaration " ^ name)
            else if not (set_member (#source_terms namespace) key) then
              raise ERR "declare-datatypes"
                ("datatype " ^ role ^
                 " is not identical to source symbol " ^ name)
            else ()
          fun parse_source role key name arguments =
            let
              val _ = require_source_symbol role key name
            in
              SmtLib_Parser.apply_term tmdict key [] arguments
              handle Feedback.HOL_ERR holerr =>
                raise ERR "declare-datatypes"
                  ("datatype " ^ role ^
                   " is not identical to source symbol " ^ name ^ ": " ^
                   Feedback.message_of holerr)
            end
          fun map_constructor
              ({key, name, selectors}: datatype_constructor) =
            let
              val _ = require_source_symbol "constructor" key name
              val declared_selector_tys = List.map selector_type selectors
              fun exact_parser_result constructor =
                let
                  val domains = constructor_domains
                    (Term.type_of constructor)
                  val arguments = Lib.mapi
                    (fn index => fn ty => Term.mk_var
                      ("cpc_datatype_argument" ^ Int.toString index, ty))
                    domains
                  val expected = Term.list_mk_comb (constructor, arguments)
                  val parsed =
                    SOME (SmtLib_Parser.apply_term tmdict key [] arguments)
                    handle Feedback.HOL_ERR _ => NONE
                in
                  case parsed of
                    SOME result => Term.aconv result expected
                  | NONE => false
                end
              fun probes_as (template, candidate) =
                if exact_parser_result template orelse
                   exact_parser_result candidate
                then SOME candidate
                else NONE
              val mappings = List.mapPartial probes_as
                (ListPair.zip
                  (source_constructor_templates, source_constructors))
              val source_constructor =
                case mappings of
                  [candidate] => candidate
                | _ => raise ERR "declare-datatypes"
                    ("datatype constructor " ^ name ^
                     " does not have one exact source parser mapping in " ^
                     sort_name)
              val source_selector_tys =
                constructor_domains (Term.type_of source_constructor)
              val _ =
                if List.length selectors = List.length source_selector_tys
                then ()
                else raise ERR "declare-datatypes"
                  ("datatype constructor " ^ name ^
                   " selector count is not identical to source: expected " ^
                   Int.toString (List.length source_selector_tys) ^
                   ", declared " ^ Int.toString (List.length selectors))
              val _ =
                if ListPair.allEq (fn (declared, source) =>
                     Type.compare (declared, source) = EQUAL)
                     (declared_selector_tys, source_selector_tys)
                then ()
                else raise ERR "declare-datatypes"
                  ("datatype constructor " ^ name ^
                   " has selector types different from its source")
            in
              (source_constructor, selectors, source_selector_tys)
            end
          val mapped_constructors = List.map map_constructor constructors
          fun same_constructor left right = Term.same_const left right
          fun unique_mapped [] = true
            | unique_mapped ((constructor, _, _) :: rest) =
                not (List.exists (fn (other, _, _) =>
                  same_constructor constructor other) rest) andalso
                unique_mapped rest
          val _ =
            if unique_mapped mapped_constructors andalso
               List.all (fn source_constructor =>
                 List.exists (fn (mapped, _, _) =>
                   same_constructor source_constructor mapped)
                   mapped_constructors) source_constructors
            then ()
            else raise ERR "declare-datatypes"
              ("datatype " ^ sort_name ^
               " constructor set is not identical to source")
          val scrutinee = Term.mk_var
            ("cpc_datatype_scrutinee", datatype_ty)
          fun validate_selectors
              (constructor, selectors, source_selector_tys) =
            let
              fun validate (index,
                  ({key, name, ...}: datatype_selector), source_range) =
                let
                  val parsed = parse_source "selector" key name [scrutinee]
                  val expected =
                    SmtLib_Parser.canonical_datatype_selector_case
                      constructor index scrutinee
                in
                  if Type.compare (Term.type_of parsed, source_range) = EQUAL
                     andalso Term.aconv parsed expected then ()
                  else raise ERR "declare-datatypes"
                    ("datatype selector " ^ name ^
                     " is not identical to source constructor/field " ^
                     "association " ^ Int.toString index)
                end
              val indexed = ListPair.zip
                (List.tabulate (List.length selectors, Lib.I),
                 ListPair.zip (selectors, source_selector_tys))
            in
              List.app (fn (index, (selector, source_range)) =>
                validate (index, selector, source_range)) indexed
            end
        in
          List.app validate_selectors mapped_constructors
        end
    in
      List.app validate_one declarations
    end

  fun validate_datatype_declarations dicts_ref declarations =
    validate_datatype_declarations_using
      {reserved = !cpc_reserved_symbols,
       source_terms = !cpc_source_term_symbols,
       source_sorts = !cpc_source_sort_symbols,
       proof_terms = !cpc_proof_term_symbols,
       proof_sorts = !cpc_proof_sort_symbols} dicts_ref declarations

  fun parse_declare_datatype_command dicts_ref get_token =
    let
      val marked_name = get_token ()
      val (sort_key, sort_name) =
        datatype_symbol "declare-datatype" "datatype sort" marked_name
      val body = read_raw_term get_token
      val _ = Library.expect_token ")" (get_token ())
      val arity =
        case body of
          RawList [RawAtom "par", RawList params, RawList _] =>
            List.length params
        | _ => 0
      val declaration = parse_datatype_body "declare-datatype"
        sort_key sort_name arity body
    in
      validate_datatype_declarations dicts_ref [declaration]
    end

  fun parse_declare_datatypes_command dicts_ref get_token =
    let
      val bindings_raw = read_raw_term get_token
      val bodies_raw = read_raw_term get_token
      val _ = Library.expect_token ")" (get_token ())
      val bindings =
        case bindings_raw of
          RawList [] => raise ERR "declare-datatypes"
            "datatype sort binding list must be nonempty"
        | RawList entries => entries
        | RawAtom _ => raise ERR "declare-datatypes"
            "datatype sort bindings must be parenthesized"
      val bodies =
        case bodies_raw of
          RawList [] => raise ERR "declare-datatypes"
            "datatype body list must be nonempty"
        | RawList entries => entries
        | RawAtom _ => raise ERR "declare-datatypes"
            "datatype bodies must be parenthesized"
      val _ = if List.length bindings = List.length bodies then () else
        raise ERR "declare-datatypes"
          "datatype sort and body lists have different lengths"
      fun binding raw =
        case raw of
          RawList [RawAtom token, RawAtom arity_text] =>
            let
              val (key, name) = datatype_symbol "declare-datatypes"
                "datatype sort" token
            in
              (key, name,
               datatype_arity "declare-datatypes" name arity_text)
            end
        | _ => raise ERR "declare-datatypes"
            "datatype sort binding must have the form (name arity)"
      fun declaration ((key, name, arity), body) =
        parse_datatype_body "declare-datatypes" key name arity body
      val declarations = List.map declaration
        (ListPair.zip (List.map binding bindings, bodies))
    in
      validate_datatype_declarations dicts_ref declarations
    end

  fun parse_paren_name_list get_token =
    let
      fun loop acc =
        case get_token () of
          ")" => List.rev acc
        | name => loop (name :: acc)
      val first = get_token ()
    in
      if first = "(" then loop [] else [first]
    end

  fun parse_premise_ids get_token =
    List.map (cpc_id_key "parse_step" "premise ID")
      (parse_paren_name_list get_token)

  (* A CPC definition is a term alias, not a HOL hypothesis.  Resolving it in
     the parser preserves sharing without granting the solver any theorem. *)
  fun parse_define dicts_ref get_token =
    let
      val marked_name = get_token ()
      val key = cpc_symbol_key "parse_define" marked_name
      val name = cpc_symbol_name "parse_define" marked_name
      val _ =
        if set_member (!cpc_reserved_symbols) key orelse
           set_member (!cpc_reserved_symbols) name then
          raise ERR "parse_define"
            ("CPC definition may not shadow builtin symbol " ^ name)
        else if set_member (!cpc_proof_term_symbols) key then
          raise ERR "parse_define"
            ("duplicate CPC declaration or definition of symbol " ^ name)
        else if set_member (!cpc_source_term_symbols) key orelse
                Option.isSome (Redblackmap.peek (#2 (!dicts_ref), key)) then
          raise ERR "parse_define"
            ("CPC definition may not redefine source symbol " ^ name)
        else ()
      (* Most CPC definitions use SMT-LIB's ``()`` binder list, but cvc5
         also emits proof-local aliases without that list (notably for its
         @list bookkeeping values).  Both forms are nullary definitions. *)
      val definition_start = get_token ()
      val first =
        if definition_start = "(" then
          let val close = get_token () in
            if close = ")" then get_token ()
            else raise ERR "parse_define"
              "CPC parameterized definitions are unsupported"
          end
        else definition_start
      val defined_term =
        if first = "@list" then
          (* An unparenthesized @list is the same opaque resolution metadata
             as ``(@list ...)`` below. *)
          (skip_sexp get_token; NONE)
        else if first = "(" then
          let val head = get_token () in
            if head = "@list" then
              let
                fun list_terms acc =
                  let val token = get_token () in
                    if token = ")" then List.rev acc
                    else list_terms (parse_term dicts_ref
                      (Library.undo_look_ahead [token] get_token) :: acc)
                  end
                val terms = list_terms []
                val _ = add_cpc_list key terms
                val _ = Library.expect_token ")" (get_token ())
              in NONE end
            else if head = "@purify" then
              let
                val payload = parse_located_term dicts_ref get_token
                val _ = Library.expect_token ")" (get_token ())
              in
                (* CPC's purify definition names the payload and its
                   `skolem_intro` step exposes that definitional equality.
                   Keeping the alias avoids inventing an unconstrained HOL
                   variable for a proof-local sharing marker. *)
                SOME payload
              end
            else if head = "@var" then
              let
                val var_name = cpc_var_name (get_token ())
                val var_type = parse_cpc_type get_token
                  (#1 (!dicts_ref))
                val _ = Library.expect_token ")" (get_token ())
              in
                SOME {term = cpc_source_variable (var_name, var_type),
                  provenance = AtomicProvenance}
              end
            else
              SOME (parse_located_term dicts_ref
                (Library.undo_look_ahead ["(", head] get_token))
          end
        else SOME (parse_located_term dicts_ref
          (Library.undo_look_ahead [first] get_token))
      val _ = case defined_term of
          SOME ({term, provenance} : located_term) =>
            let
              val term = intern_cpc_term term
            in
              Library.expect_token ")" (get_token ());
              add_term dicts_ref key term;
              add_term_provenance key provenance
            end
        | NONE => ()
      val _ = cpc_proof_term_symbols :=
        HOLset.add (!cpc_proof_term_symbols, key)
    in
      ()
    end

  fun duplicate_id id known_ids =
    HOLset.member (!known_ids, id)

  fun ensure_fresh_id where_ id known_ids =
    if duplicate_id id known_ids then
      raise ERR where_ ("duplicate CPC command ID " ^ id)
    else ()

  fun require_known_premise id known_ids premise =
    if HOLset.member (!known_ids, premise) then ()
    else raise ERR "parse_step"
      ("unknown premise ID '" ^ premise ^ "' in CPC step " ^ id)

  fun is_set_sort_metadata rule_name position =
    case rule_name of
      "sets-card-emp" => position = 2
    | "sets-is-empty-elim" => position = 2
    | "sets-member-emp" => position = 3
    | "sets-minus-self" => position = 2
    | _ => false

  fun parse_step dicts_ref version known_ids record_unsupported get_token =
    let
      val id = cpc_id_key "parse_step" "command ID" (get_token ())
      val _ = ensure_fresh_id "parse_step" id known_ids
      val first = get_token ()
      (* CPC serializes the conclusion before [:rule].  Buffer exactly one
         raw term so rule dispatch can happen before SMT semantic parsing.
         Only an exact registered unsupported RARE rule may bypass semantic
         elaboration, and even that route validates the complete step below. *)
      val (raw_conclusion, attr) =
        if first = ":rule" then (NONE, first)
        else
          (SOME (read_raw_term
             (Library.undo_look_ahead [first] get_token)),
           get_token ())
      val _ = if attr = ":rule" then () else
        raise ERR "parse_step" "expected :rule"
      val rule_name = get_token ()
      val rule =
        case lookup_rule version rule_name of
          SOME rule => rule
        | NONE => raise ERR "parse_step"
            (registry_lookup_failure version rule_name)
      val unsupported_diagnostic =
        rare_unsupported_diagnostic rule_name
      (* Unsupported entries may contain symbols for which HOL deliberately
         has no dictionary entry.  They still have to be valid CPC steps:
         consume and check every premise/argument occurrence, every attribute,
         and the step's own closing delimiter before issuing the registered
         semantic diagnostic. *)
      fun structural_token context =
        get_token () handle SmtLib_Parser.CPCProofEOF =>
          raise ERR "parse_step"
            ("unexpected end of unsupported CPC step " ^ id ^ " " ^ context)
      (* This is a syntax-only CST validator.  Exact unsupported rules may
         mention operators that cannot be elaborated to HOL, but they do not
         get a weaker term language: applications, qualified identifiers,
         binders, lets, matches and annotations must still satisfy the
         SMT-LIB/CPC grammar accepted by this parser. *)
      fun raw_error detail = raise ERR "parse_step"
        ("malformed raw term in unsupported CPC step " ^ id ^ ": " ^
         detail)
      val validate_raw = validate_raw_term raw_error
      fun structural_premises () =
        let
          val _ = if structural_token "while reading :premises" = "("
            then ()
            else raise ERR "parse_step"
              ("expected parenthesized :premises in unsupported CPC step " ^
               id)
          fun ids () =
            case structural_token "while reading :premises" of
              ")" => ()
            | "(" => raise ERR "parse_step"
                ("invalid premise ID in unsupported CPC step " ^ id)
            | raw_premise =>
                let
                  val premise =
                    cpc_id_key "parse_step" "premise ID" raw_premise
                in
                  if HOLset.member (!known_ids, premise) then
                    ids ()
                  else raise ERR "parse_step"
                    ("unknown premise ID '" ^
                     SmtLib_Parser.proof_symbol_text raw_premise ^
                     "' in unsupported CPC step " ^ id)
                end
        in
          ids ()
        end
      fun structural_args () =
        let
          val _ = if structural_token "while opening :args" = "(" then ()
            else raise ERR "parse_step"
              ("expected parenthesized :args in unsupported CPC step " ^ id)
          fun terms () =
            case structural_token "while reading :args" of
              ")" => ()
            | token =>
                (validate_raw (read_raw_term
                   (Library.undo_look_ahead [token]
                     (fn () => structural_token "while reading :args")));
                 terms ())
        in
          terms ()
        end
      fun consume_unsupported seen_premises seen_args diagnostic =
        case structural_token "before its closing delimiter" of
          ")" => ()
        | ":premises" =>
            if seen_premises then raise ERR "parse_step"
              ("duplicate :premises in unsupported CPC step " ^ id)
            else (structural_premises ();
              consume_unsupported true seen_args diagnostic)
        | ":args" =>
            if seen_args then raise ERR "parse_step"
              ("duplicate :args in unsupported CPC step " ^ id)
            else (structural_args ();
              consume_unsupported seen_premises true diagnostic)
        | attribute => raise ERR "parse_step"
            ("unknown CPC step attribute " ^ attribute ^
             " in cvc5 version " ^ version)
      fun parse_supported () =
      let
      fun parse_buffered raw =
        parse_located_term dicts_ref
          (Library.undo_look_ahead (raw_tokens raw) (fn () =>
            raise ERR "parse_step"
              ("buffered conclusion ended early in CPC step " ^ id)))
      val conclusion = Option.map parse_buffered raw_conclusion
      fun attrs seen_premises seen_args premises args =
        case get_token () of
          ")" => {id = id,
                   conclusion = Option.map intern_located conclusion,
                   rule = rule, premises = premises,
                   args = List.map intern_located args}
        | ":premises" =>
            if seen_premises then raise ERR "parse_step"
              ("duplicate :premises in CPC step " ^ id)
            else
              let
                val premises = parse_premise_ids get_token
                val _ = List.app
                  (require_known_premise id known_ids) premises
              in
                attrs true seen_args premises args
              end
        | ":args" =>
            if seen_args then raise ERR "parse_step"
              ("duplicate :args in CPC step " ^ id)
            else
            let
              val _ = Library.expect_token "(" (get_token ())
              (* Resolution annotations such as @list are proof-search hints,
                 not premises of the kernel replay.  Preserve the rule step
                 while consuming their full s-expression syntax; this avoids
                 pretending that cvc5's private annotation vocabulary is an
                 SMT-LIB term language. *)
              fun ignore_terms () =
                let val token = get_token () in
                  if token = ")" then []
                  else (if token = "(" then skip_sexp get_token else ();
                        ignore_terms ())
                end
              fun resolution_args () =
                let
                  val first = get_token ()
                in
                  if first = ")" then []
                  else
                    let
                      (* ProofRule::RESOLUTION is annotated with the
                         polarity of its pivot in the first premise and the
                         pivot itself.  These are required to reconstruct
                         the (otherwise omitted) resolvent. *)
                      val polarity = parse_located_term dicts_ref
                        (Library.undo_look_ahead [first] get_token)
                      val pivot = parse_located_term dicts_ref get_token
                      val _ = ignore_terms ()
                    in [polarity, pivot] end
                end
              fun parse_list_after_open () =
                let
                  fun entries acc =
                    let val token = get_token () in
                      if token = ")" then List.rev acc
                      else entries (parse_located_term dicts_ref
                        (Library.undo_look_ahead [token] get_token) :: acc)
                    end
                in entries [] end
              fun parse_list token =
                if token = "(" then
                  let
                    val _ = Library.expect_token "@list" (get_token ())
                  in parse_list_after_open () end
                else
                  case lookup_cpc_list token of
                    SOME terms => List.map
                      (unavailable_term
                        "expanded CPC resolution-list alias") terms
                  | NONE => raise ERR "parse_step"
                      ("undefined CPC resolution @list alias " ^ token)
              fun chain_resolution_args () =
                let
                  val polarities = parse_list (get_token ())
                  val pivots = parse_list (get_token ())
                  val _ = Library.expect_token ")" (get_token ())
                  val _ = if List.length polarities = List.length pivots
                    then () else raise ERR "parse_step"
                      "CPC chain_resolution annotation lengths differ"
                in polarities @ pivots end
              fun macro_resolution_args () =
                let
                  val first = get_token ()
                in
                  if first = ")" then []
                  else
                    let
                      val target = parse_located_term dicts_ref
                        (Library.undo_look_ahead [first] get_token)
                      val next = get_token ()
                    in
                      if next = ")" then [target]
                      else
                        let
                          val polarities = parse_list next
                          val pivots = parse_list (get_token ())
                          val _ = Library.expect_token ")" (get_token ())
                        in target :: polarities @ pivots end
                    end
                end
              fun and_elim_index () =
                let
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC and_elim index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC and_elim index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [unavailable_term "CPC and_elim index metadata"
                    (intSyntax.mk_injected
                      (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun not_or_elim_index () =
                let
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC not_or_elim index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC not_or_elim index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [unavailable_term "CPC not_or_elim index metadata"
                    (intSyntax.mk_injected
                      (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun cnf_and_pos_args () =
                let
                  val first = get_token ()
                  val conjunction = parse_located_term dicts_ref
                    (Library.undo_look_ahead [first] get_token)
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC cnf_and_pos index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC cnf_and_pos index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [conjunction,
                   unavailable_term "CPC cnf_and_pos index metadata"
                     (intSyntax.mk_injected
                       (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun cnf_or_neg_args () =
                let
                  val first = get_token ()
                  val disjunction = parse_located_term dicts_ref
                    (Library.undo_look_ahead [first] get_token)
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC cnf_or_neg index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC cnf_or_neg index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [disjunction,
                   unavailable_term "CPC cnf_or_neg index metadata"
                     (intSyntax.mk_injected
                       (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun exists_elim_args () =
                let
                  val _ = Library.expect_token "(" (get_token ())
                  val _ = Library.expect_token "=" (get_token ())
                  val first = get_token ()
                  val (lhs, rhs) = if first = "(" then
                    let
                      val quantifier = get_token ()
                      val _ = if quantifier = "exists" then () else
                        raise ERR "parse_step"
                          "expected existential left side for exists-elim"
                      val binder_name = get_token ()
                      val binders =
                        case lookup_cpc_list binder_name of
                          SOME vars => vars
                        | NONE => raise ERR "parse_step"
                            ("undefined CPC @list alias " ^ binder_name)
                      val body = parse_term dicts_ref get_token
                      val _ = Library.expect_token ")" (get_token ())
                      val rhs = parse_term dicts_ref get_token
                    in (boolSyntax.list_mk_exists (binders, body), rhs) end
                    else
                      (parse_term dicts_ref
                         (Library.undo_look_ahead [first] get_token),
                       parse_term dicts_ref get_token)
                  val _ = Library.expect_token ")" (get_token ())
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [unavailable_term
                    "CPC exists-elim argument reconstructed from metadata"
                    (boolSyntax.mk_eq (lhs, rhs))]
                end
              fun quant_rewrite_args () =
                let val first = get_token () in
                  if first <> "(" then
                    let
                      val proposition = parse_located_term dicts_ref
                        (Library.undo_look_ahead [first] get_token)
                      val _ = Library.expect_token ")" (get_token ())
                    in [proposition] end
                  else
                    let
                      val _ = Library.expect_token "=" (get_token ())
                      val _ = Library.expect_token "(" (get_token ())
                      val quantifier = get_token ()
                      val binder_name = get_token ()
                      val binders =
                        case lookup_cpc_list binder_name of
                          SOME vars => vars
                        | NONE => raise ERR "parse_step"
                            ("undefined CPC @list alias " ^ binder_name)
                      val body = parse_located_term dicts_ref get_token
                      val _ = Library.expect_token ")" (get_token ())
                      val rhs = parse_located_term dicts_ref get_token
                      val _ = Library.expect_token ")" (get_token ())
                      val _ = Library.expect_token ")" (get_token ())
                      val lhs = if quantifier = "forall" then
                        boolSyntax.list_mk_forall (binders, #term body)
                        else if quantifier = "exists" then
                          boolSyntax.list_mk_exists (binders, #term body)
                        else raise ERR "parse_step"
                          "expected quantified left side for CPC quantifier rewrite"
                      val _ = record_cpc_binder_block
                        (quantifier, List.length binders, lhs)
                      val binder_provenance = exact_binders quantifier binders
                        (#provenance body)
                    in
                      [{term = boolSyntax.mk_eq (lhs, #term rhs),
                        provenance = EqualityProvenance
                          (binder_provenance, #provenance rhs)}]
                    end
                end
              (* CPC Set rules carry their set sort as an argument, e.g.
                 [(Set Int)].  This is proof metadata, not a HOL term; retain
                 it only as a variable of the parsed sort so rule-specific
                 replay can ignore it without rejecting a recorded proof. *)
              fun sort_marker tokens =
                let val (tydict, _) = !dicts_ref in
                  Term.mk_var ("@cpc.sort",
                    parse_cpc_type
                      (Library.undo_look_ahead tokens get_token) tydict)
                end
              fun terms acc =
                let val token = get_token () in
                  if token = ")" then List.rev acc
                  else if token = "@bv_empty" andalso
                          rule_name = "bv-extract-concat-1" andalso
                          List.length acc = 1 then
                    terms (unavailable_term "empty CPC bit-vector list"
                      (listSyntax.mk_nil Type.bool) :: acc)
                  else if token = "(" then
                    let val head = get_token () in
                      if head = "@list" then
                        (* Lists in CPC arguments carry a homogeneous
                           sequence of object terms (not a HOL list term).
                           Flatten them for handlers such as instantiate. *)
                        terms (List.revAppend
                          (List.map (unavailable_term
                            "expanded CPC argument-list syntax")
                            (list_terms []), acc))
                      else if head = "Set" andalso
                              is_set_sort_metadata rule_name
                                (List.length acc + 1) then
                        let
                          val tm = sort_marker ["(", head]
                            handle Feedback.HOL_ERR holerr =>
                              raise ERR "parse_step"
                                ("could not parse Set sort metadata for CPC " ^
                                 "step " ^ id ^ " (rule " ^ rule_name ^ "): " ^
                                 Feedback.message_of holerr)
                        in terms
                          (unavailable_term "CPC Set sort metadata" tm :: acc)
                        end
                      else
                        let
                          val tm = parse_located_term dicts_ref
                            (Library.undo_look_ahead ["(", head] get_token)
                            handle Feedback.HOL_ERR holerr =>
                              raise ERR "parse_step"
                                ("could not parse :args for CPC step " ^ id ^
                                 " (rule " ^ rule_name ^ "): " ^
                                 Feedback.message_of holerr)
                        in terms (tm :: acc) end
                    end
                  else
                    (case lookup_cpc_list token of
                       SOME listed_terms =>
                         terms (List.revAppend
                           (List.map (unavailable_term
                             "expanded CPC argument-list alias") listed_terms,
                            acc))
                     | NONE =>
                         let
                           val tm = parse_located_term dicts_ref
                             (Library.undo_look_ahead [token] get_token)
                             handle Feedback.HOL_ERR holerr =>
                               raise ERR "parse_step"
                                 ("could not parse :args for CPC step " ^ id ^
                                  " (rule " ^ rule_name ^ "): " ^
                                  Feedback.message_of holerr)
                         in terms (tm :: acc) end)
                end
              and list_terms acc =
                let val token = get_token () in
                  if token = ")" then List.rev acc
                  else list_terms (parse_recorded_term dicts_ref
                    (Library.undo_look_ahead [token] get_token) :: acc)
                end
              fun cpc_list_term terms =
                case terms of
                  first :: rest =>
                    let
                      val element_type = Term.type_of first
                      val _ = List.all (fn term =>
                          Type.compare (Term.type_of term, element_type) =
                            EQUAL) rest orelse
                        raise ERR "parse_step"
                          ("CPC structured list has mixed element types in " ^
                           "step " ^ id ^ " (rule " ^ rule_name ^ ")")
                    in
                      listSyntax.mk_list (terms, element_type)
                    end
                | [] => listSyntax.mk_list
                    ([], Type.mk_vartype "'cpc_list")
              fun validate_set_sort_metadata args =
                let
                  fun check (set, marker) =
                    if Type.compare (Term.type_of set, Term.type_of marker) =
                         EQUAL then ()
                    else raise ERR "parse_step"
                      ("CPC Set sort metadata does not match its set argument " ^
                       "in step " ^ id ^ " (rule " ^ rule_name ^ ")")
                in
                  case (rule_name, args) of
                    ("sets-card-emp", [set, marker]) => check (set, marker)
                  | ("sets-is-empty-elim", [set, marker]) =>
                      check (set, marker)
                  | ("sets-member-emp", [_ , set, marker]) =>
                      check (set, marker)
                  | ("sets-minus-self", [set, marker]) => check (set, marker)
                  | _ => ()
                end
              fun structured_terms acc =
                let val token = get_token () in
                  if token = ")" then List.rev acc
                  else if token = "(" then
                    let val head = get_token () in
                      if head = "@list" then
                        structured_terms
                          (unavailable_term "CPC structured-list metadata"
                            (cpc_list_term (list_terms [])) :: acc)
                      else
                        let
                          val tm = parse_located_term dicts_ref
                            (Library.undo_look_ahead ["(", head]
                              get_token)
                        in structured_terms (tm :: acc) end
                    end
                  else
                    (case lookup_cpc_list token of
                       SOME listed_terms => structured_terms
                         (unavailable_term "CPC structured-list alias"
                           (cpc_list_term listed_terms) :: acc)
                     | NONE =>
                         let
                           val tm = parse_located_term dicts_ref
                             (Library.undo_look_ahead [token] get_token)
                         in structured_terms (tm :: acc) end)
                end
            in
              if rule_name = "resolution" then
                attrs seen_premises true premises (resolution_args ())
              else if rule_name = "chain_resolution" then
                attrs seen_premises true premises (chain_resolution_args ())
              else if #replay_handler rule = "resolution" then
                (* Macro/chain resolution gives its result clause first;
                   the remaining arguments only describe its pivots. *)
                attrs seen_premises true premises
                  (macro_resolution_args ())
              else if #replay_handler rule = "and_elim" then
                attrs seen_premises true premises (and_elim_index ())
              else if #replay_handler rule = "not_or_elim" then
                attrs seen_premises true premises (not_or_elim_index ())
              else if #replay_handler rule = "exists_elim" then
                attrs seen_premises true premises (exists_elim_args ())
              else if #replay_handler rule = "quant_rewrite" then
                attrs seen_premises true premises (quant_rewrite_args ())
              else if rule_name = "cnf_and_pos" then
                attrs seen_premises true premises (cnf_and_pos_args ())
              else if rule_name = "cnf_or_neg" then
                attrs seen_premises true premises (cnf_or_neg_args ())
              else if rule_name = "arith-mod-over-mod" orelse
                      rule_name = "arith-mod-over-mod-mult" then
                attrs seen_premises true premises (structured_terms [])
              else if #replay_handler rule = "rare_inventory" then
                (* Declarative RARE recipes distinguish one term from a
                   variadic list formal.  Preserve each CPC @list (and each
                   recorded alias for one) as exactly one HOL list wrapper;
                   the owning replay contract validates and unwraps it. *)
                attrs seen_premises true premises (structured_terms [])
              else
                let val args = terms [] in
                  (validate_set_sort_metadata
                    (List.map (fn (located : located_term) => #term located)
                      args);
                   attrs seen_premises true premises args)
                end
            end
        | attribute => raise ERR "parse_step"
            ("unknown CPC step attribute " ^ attribute ^
             " in cvc5 version " ^ version)
      in
        attrs false false [] []
      end
    in
      case unsupported_diagnostic of
        SOME diagnostic =>
          (Option.app validate_raw raw_conclusion;
           consume_unsupported false false diagnostic;
           record_unsupported (rule_name, diagnostic);
           (id, NONE))
      | NONE => (id, SOME (parse_supported ()))
    end

  fun register_command_signature seen_steps kind id tokens =
    let
    fun same_tokens left right =
      ListPair.allEq (op =) (left, right)
    fun normalize_premise_ids tokens =
      let
        fun normal acc [] = List.rev acc
          | normal acc (":premises" :: "(" :: rest) =
              premises ("(" :: ":premises" :: acc) rest
          | normal acc (token :: rest) = normal (token :: acc) rest
        and premises acc [] = List.rev acc
          | premises acc (")" :: rest) = normal (")" :: acc) rest
          | premises acc (_ :: rest) =
              premises ("@premise" :: acc) rest
      in
        normal [] tokens
      end
    fun register_step_signature kind id tokens =
      let
        (* [tokens] starts with the raw command-ID token.  Use its already
           validated semantic key so normalized-identical scoped reuse is
           independent of equivalent quoted/unquoted spelling. *)
        val signature_tokens =
          kind :: id :: normalize_premise_ids (List.tl tokens)
      in
        case Redblackmap.peek (!seen_steps, id) of
          NONE => seen_steps :=
            Redblackmap.insert (!seen_steps, id, signature_tokens)
        | SOME known_tokens =>
            if same_tokens signature_tokens known_tokens then ()
            else raise ERR "parse_commands"
              ("duplicate CPC command ID " ^ id)
      end
    in register_step_signature kind id tokens end

  fun parse_commands dicts_ref version known_ids scope_snapshots
      seen_steps record_unsupported get_token stop acc =
    let
      fun add_id id =
        (ensure_fresh_id "parse_commands" id known_ids;
         known_ids := HOLset.add (!known_ids, id))
      fun recurse acc =
        parse_commands dicts_ref version known_ids scope_snapshots
          seen_steps record_unsupported get_token stop acc
      val register_step_signature = register_command_signature seen_steps
      fun parse_recorded_step kind =
        let
          val consumed = ref ([] : string list)
          fun recording_token () =
            let val token = get_token () in
              consumed := token :: !consumed;
              token
            end
          val result as (id, _) =
            parse_step dicts_ref version known_ids record_unsupported
              recording_token
          val _ = register_step_signature kind id (List.rev (!consumed))
        in
          result
        end
      fun close_scope id =
        case !scope_snapshots of
          previous :: rest =>
            (known_ids := previous;
             scope_snapshots := rest;
             add_id id)
        | [] => raise ERR "parse_commands"
            ("step-pop without matching assume-push in CPC step " ^ id)
      val token =
        (SOME (get_token ()))
        handle SmtLib_Parser.CPCProofEOF => NONE
    in
      case token of
        NONE =>
          if stop then raise ERR "parse_commands"
            "unexpected end of nested CPC wrapper"
          else List.rev acc
      | SOME ")" =>
          if stop then List.rev acc
          else raise ERR "parse_commands"
            "unexpected closing delimiter at CPC top level"
      | SOME "(" =>
          let val head = get_token () in
            case head of
              "(" => raise ERR "parse_commands"
                "nested or second CPC proof wrapper is not permitted"
            | other =>
                if not stop then raise ERR "parse_commands"
                  "CPC command found outside a proof wrapper"
                else
                  case other of
                    "declare-const" =>
                      (parse_or_keep_term_declaration parse_declare_const
                         dicts_ref get_token;
                       recurse acc)
                  | "declare-fun" =>
                      (parse_or_keep_term_declaration parse_declare_fun
                         dicts_ref get_token;
                       recurse acc)
                  | "declare-sort" =>
                      (parse_or_keep_sort_declaration dicts_ref get_token;
                       recurse acc)
                  | "declare-datatype" =>
                      (parse_declare_datatype_command dicts_ref get_token;
                       recurse acc)
                  | "declare-datatypes" =>
                      (parse_declare_datatypes_command dicts_ref get_token;
                       recurse acc)
                  | "define" =>
                      (parse_define dicts_ref get_token;
                       recurse acc)
                  | "assume" =>
                      let
                        val id = cpc_id_key "parse_commands" "command ID"
                          (get_token ())
                        val _ = ensure_fresh_id "parse_commands" id known_ids
                        val tm = parse_located_term dicts_ref get_token
                        val _ = Library.expect_token ")" (get_token ())
                        val command = ASSUME (id, tm)
                        val _ = add_id id
                      in
                        recurse (command :: acc)
                      end
                  | "assume-push" =>
                      let
                        val id = cpc_id_key "parse_commands" "command ID"
                          (get_token ())
                        val _ = ensure_fresh_id "parse_commands" id known_ids
                        val tm = parse_located_term dicts_ref get_token
                        val _ = Library.expect_token ")" (get_token ())
                        val command = ASSUME_PUSH (id, tm)
                        val _ = scope_snapshots :=
                          !known_ids :: !scope_snapshots
                        val _ = add_id id
                      in
                        recurse (command :: acc)
                      end
                  | "step" =>
                      let
                        val (id, step) = parse_recorded_step "step"
                        val _ = add_id id
                      in
                        case step of
                          SOME step => recurse (STEP step :: acc)
                        | NONE => recurse acc
                      end
                  | "step-pop" =>
                      let
                        val (id, step) = parse_recorded_step "step-pop"
                        val _ = close_scope id
                      in
                        case step of
                          SOME step => recurse (STEP step :: acc)
                        | NONE => recurse acc
                      end
                  | _ => raise ERR "parse_commands"
                      ("unknown CPC construct " ^ other ^
                       " in cvc5 version " ^ version)
          end
      | SOME other => raise ERR "parse_commands"
          ("unexpected CPC token '" ^
           SmtLib_Parser.proof_symbol_text other ^ "'")
    end
in
  datatype raw_term = datatype raw_term
  val read_raw_term = read_raw_term
  val raw_tokens = raw_tokens
  val normalize_cpc_testers = normalize_cpc_testers
  val validate_raw_term = validate_raw_term
  val intern_cpc_term = intern_cpc_term
  val intern_cpc_shell = intern_cpc_shell
  val cpc_indexed_term_registry = cpc_indexed_term_registry
  val with_cpc_deindexed_entries = with_cpc_deindexed_entries
  val cpc_parameterized_skolem_names = cpc_parameterized_skolem_names
  val cpc_parameterized_skolem_for_test =
    cpc_parameterized_skolem_for_test
  val cpc_re_unfold_pos_decomposition = cpc_re_unfold_pos_decomposition
  val cpc_re_unfold_pos_regexps = cpc_re_unfold_pos_regexps
  val cpc_re_unfold_pos_component = cpc_re_unfold_pos_component
  type cpc_fp_private_binding = cpc_fp_private_binding
  val cpc_fp_private_bindings = cpc_fp_private_bindings
  val with_cpc_fp_private_proof = with_cpc_fp_private_proof
  val with_cpc_fp_private_source_terms = with_cpc_fp_private_source_terms
  val is_cpc_fp_private_marker = is_cpc_fp_private_marker
  val is_cpc_fp_private_marker_observed =
    is_cpc_fp_private_marker_observed
  val cpc_fp_private_unbound_markers = cpc_fp_private_unbound_markers

  fun parse_stream_with_version (dicts : dicts) version instream : proof =
    let
      (* Resolve once, here: everything downstream -- rule lookup, gating and
         diagnostics -- then works with a tested version. *)
      val version = resolve_version version
      val _ = cpc_list_definitions := Redblackmap.mkDict String.compare
      val _ = cpc_list_names := []
      val _ = cpc_fp_private_bindings_ref := []
      val _ = cpc_fp_private_unbound_markers_ref := []
      val _ = cpc_fp_private_identity_index := empty_private_identity_index ()
      val _ = cpc_fp_private_parse_avoid := []
      val _ = cpc_fp_private_allocated := Term.empty_varset
      val _ = cpc_source_variables := Redblackmap.mkDict Term.var_compare
      val _ = cpc_source_images := Term.empty_varset
      val _ = cpc_reserved_source_scope := []
      val _ = cpc_term_provenances := Redblackmap.mkDict String.compare
      val _ = cpc_term_intern :=
        Array.array (term_intern_bucket_count, [])
      val _ = cpc_forall_blocks := []
      fun keys dictionary = Redblackmap.foldl
        (fn (key, _, set) => HOLset.add (set, key))
        (HOLset.empty String.compare) dictionary
      val (all_tydict, all_tmdict) =
        SmtLib_Logics.parsedicts_of_logic "ALL"
      val baseline_dicts = with_cpc_literals
        (all_tydict, Library.union_dict all_tmdict
          SmtLib_Theories.CVC5_Seq.tmdict)
      val baseline = HOLset.union
        (keys (#1 baseline_dicts), keys (#2 baseline_dicts))
      val syntax_names =
        ["_", "!", "as", "let", "forall", "exists", "lambda",
         "match", "par", "declare-const", "declare-fun",
         "declare-sort", "declare-datatype", "declare-datatypes",
         "define", "assume", "assume-push", "step", "step-pop"]
      val _ = cpc_reserved_symbols := HOLset.addList
        (baseline, syntax_names)
      fun source_keys dictionary = HOLset.filter
        (fn key => not (set_member (!cpc_reserved_symbols) key))
        (keys dictionary)
      val _ = cpc_source_sort_symbols := source_keys (#1 dicts)
      val _ = cpc_source_term_symbols := source_keys (#2 dicts)
      val _ = cpc_proof_sort_symbols := HOLset.empty String.compare
      val _ = cpc_proof_term_symbols := HOLset.empty String.compare
      val known_ids = ref (HOLset.empty String.compare)
      val scope_snapshots = ref ([] : string HOLset.set list)
      val seen_steps = ref
        (Redblackmap.mkDict String.compare :
          (string, string list) Redblackmap.dict)
      val pending = ref (NONE : (string * string) option)
      fun record_unsupported diagnostic =
        case !pending of
          NONE => pending := SOME diagnostic
        | SOME _ => ()
      (* CPC conclusions and arguments can contain SMT-LIB string literals.
         Preserve token kind and apply cvc5's proof lexical policy. *)
      val get_token =
        SmtLib_Parser.make_cpc_proof_stream_tokenizer instream
      val _ =
        (Library.expect_token "(" (get_token ()))
        handle SmtLib_Parser.CPCProofEOF =>
          raise ERR "parse_stream_with_version"
            "unexpected end before CPC proof wrapper"
      val commands =
        parse_commands (ref (with_cpc_literals dicts)) version known_ids
          scope_snapshots seen_steps record_unsupported get_token true []
        handle SmtLib_Parser.CPCProofEOF =>
          raise ERR "parse_stream_with_version"
            "unexpected end of CPC proof wrapper"
      val _ = List.null (!scope_snapshots) orelse
        raise ERR "parse_stream_with_version"
          "unclosed assume-push scope at end of CPC proof wrapper"
      val trailing =
        (SOME (get_token ()))
        handle SmtLib_Parser.CPCProofEOF => NONE
      val _ =
        case trailing of
          NONE => ()
        | SOME token => raise ERR "parse_stream_with_version"
            ("second CPC proof wrapper or trailing token '" ^
             SmtLib_Parser.proof_symbol_text token ^ "'")
      val _ =
        case !pending of
          SOME (rule_name, diagnostic) => raise ERR rule_name diagnostic
        | NONE => ()
      val proof = {commands = commands, cvc_version = version}
      val _ = retain_cpc_fp_private_proof proof
    in
      proof
    end

  fun parse_stream dicts instream =
    parse_stream_with_version dicts unknown_cvc_version instream

  (* Explicitly audited CPC constructors receive only bounded typed holes.
     Shape-dependent BV/FP and skolem builders remain separate adapters. *)
  (* Qualification in the ordinary proof grammar uses term-valued sort
     markers. Reuse its actual callbacks as bounded recipes, rather than
     silently substituting generic sort-directed ascription semantics. *)
  fun graph_qualification_entries () =
    let val (_,dictionary) = with_cpc_literals
          (Redblackmap.mkDict String.compare,
           Redblackmap.mkDict String.compare)
    in List.concat (List.map (fn name =>
      List.map (fn parse => (name,parse))
        (valOf (Redblackmap.peek (dictionary,name))))
      ["Bool","String","Set","Bag","as"]) end

  (* Keep an allocated private marker's identity in source syntax as well
     as in the backend. A lexical binder may print the same descriptor. *)
  fun graph_private_descriptor backend value =
    case B.variable_descriptor backend value of
        SOME descriptor => descriptor
      | NONE => raise ERR "graph_cpc_source"
          "private marker has no variable descriptor"

  (* Stable source-independent CPC symbols denote one proof-local identity,
     not one identity per binder/LET. Allocate outside temporary binder
     construction scopes; retain the original lexical allocation label when
     already at the root construction scope. Source-dependent/fresh FP
     allocation and source snapshots belong to the guarded frontend. *)
  fun graph_private_allocator (terms:'a F.constructed_session) =
    let
      val backend = #backend (#reader terms)
      val root = B.root backend
      val root_scope = B.frame_scope backend root
      fun compare ((lk,lt),(rk,rt)) =
        (B.syntax_spend backend 1;
         case String.compare (lk,rk) of
             EQUAL => Type.compare (lt,rt) | order => order)
      val symbols = ref (Redblackmap.mkDict compare)
      fun allocate frame
          (specification as {kind,hol_type,source,stable}) =
        if stable andalso not (Option.isSome source) then
          let val key = (kind,hol_type)
          in case Redblackmap.peek (!symbols,key) of SOME marker => marker
           | NONE =>
               let
                 val owner = if B.frame_scope backend frame=root_scope then
                     frame else root
                 val marker = (#private_symbol terms) owner specification
                 val _ = symbols := Redblackmap.insert (!symbols,key,marker)
               in marker end
          end
        else (#private_symbol terms) frame specification
    in allocate end

  (* Keep source provenance canonical even when the occurrence is captured
     by an explicit private binder. capture_alias resolves allocation IDs,
     never a private marker's printed lexical descriptor. *)
  fun graph_private_reference backend frame marker =
    #1 (B.capture_alias backend frame (marker,[]))

  fun graph_private_atom backend frame marker =
    (B.note_constructor_source backend
       (C.private_atom (graph_private_descriptor backend marker));
     graph_private_reference backend frame marker)

  fun install_graph_qualifications backend add_recipe add_constructor
      private_symbol =
    let
      fun install (name,parse) =
        if name = "Bool" orelse name = "as" then add_recipe (name,parse)
        else add_constructor (name,fn frame => fn token => fn indices =>
          fn arguments =>
          let
            (* Only schematic atoms reach the native marker callback. Its
               result is a single typed marker, never an operand expansion. *)
            val holes = List.map (Term.genvar o B.type_of backend) arguments
            val marker = B.index_callback backend (fn () =>
              parse token (List.map (fn _ => boolSyntax.T) indices) holes)
            val _ = B.note_index_callback backend (token,parse,SOME marker)
            val _ = B.syntax_spend backend
              (1 + 4 * IntInf.fromInt (List.length arguments))
          in graph_private_atom backend frame (private_symbol frame
            {kind = #1 (Term.dest_var marker), hol_type = Term.type_of marker,
             source = NONE, stable = true}) end)
    in List.app install (graph_qualification_entries ()) end

  (* CPC's flattened indexed applications reuse the registered typed
     constructor, moving only admitted index IDs/literals. Actual operands
     never become arguments to a native term builder. *)
  fun install_graph_indexed (backend:'a B.backend)
      (limits:SmtReplayResourcePolicy.recipe_policy)
      (terms:'a F.constructed_session) =
    let
      val (_,dictionary) = SmtLib_Logics.parsedicts_of_logic "ALL"
      val recipe = SmtLib_GraphTheories.recipe_parsefn_with_policy
        backend limits
      fun observed native token action =
        let val result = action ()
            val _ = B.note_index_callback backend (token,native,NONE)
        in result end
      fun move count action =
        case B.constructor_sources backend of NONE => action ()
        | SOME {indices,arguments} =>
            let val (result,source) = B.with_constructor_sources backend
                  {indices=indices @ List.take (arguments,count),
                   arguments=List.drop (arguments,count)} action
                val _ = Option.app (B.note_constructor_source backend) source
            in result end
      fun leading token count arguments =
        let val values = List.take (arguments,count)
            val sources = case B.constructor_sources backend of
                SOME {arguments,...} => List.take (arguments,count)
              | NONE => []
            fun index (value,source) =
              if token="divisible" then P.ValueIndex (value,"(") else
              let val spend = B.syntax_spend backend
              in case SmtLib_ConstructorSyntax.retained_native spend source of
                   SOME term => P.LiteralIndex term
                 | NONE =>
                     if SmtLib_ConstructorSyntax.is_numeric_literal spend
                         source then P.ValueIndex (value,"(")
                     else
                       (* This is a bounded malformed-index diagnostic, not
                          a reconstruction of a LET-eliminated operand.
                          The authoritative callback owns its exception. *)
                       P.LiteralIndex (Term.mk_var ("cpc_nonliteral_index",
                         SmtLib_ConstructorSyntax.type_of source))
              end
        in if List.length sources=count then
             ListPair.mapEq index (values,sources)
           else List.map (fn value => P.ValueIndex (value,"(")) values end
      fun indexed (name,arity) =
        case Redblackmap.peek (dictionary,name) of NONE => ()
        | SOME _ =>
          let
            val native = cpc_deindexed_parsefn dictionary name arity
            fun parse _ indices arguments =
              P.apply_term dictionary name indices arguments
            fun construct frame token indices arguments =
              if name="_" andalso token<>"_" then
                SmtLib_Theories.decline "<cpc_deindexed_parsefn>"
                  "generic indexed adapter does not match this token"
              else observed native token (fn () =>
                if not (null indices) then
                  recipe parse frame token indices arguments
                else if List.length arguments < arity then
                  (* Run the original rejection on bounded typed holes. *)
                  recipe native frame token [] arguments
                else let val indices = leading token arity arguments
                  in move arity (fn () => recipe parse frame token indices
                    (List.drop (arguments,arity))) end)
          in (#add_constructor_parser terms) (name,construct) end
      fun fp frame token indices arguments =
        observed cpc_to_fp_bv_parsefn token (fn () =>
          if not (null indices) orelse List.length arguments < 2 then
            recipe cpc_to_fp_bv_parsefn frame token indices arguments
          else let val indices = leading token 2 arguments
            in move 2 (fn () => recipe cpc_to_fp_bv_parsefn frame token
              indices (List.drop (arguments,2))) end)
      fun bv frame token indices arguments =
        observed cpc_bv_parsefn token (fn () =>
          if not (null indices) then
            recipe cpc_bv_parsefn frame token indices arguments
          else case (token,arguments) of
              ("@bv",[value,width]) =>
                let val indices = leading token 2 arguments
                    fun scalar (P.LiteralIndex term) = term
                      | scalar (P.ValueIndex (value,_)) =
                          B.small_index_with_policy backend frame
                            (#index_limit limits) value
                      | scalar _ = raise ERR "graph_index"
                          "nonliteral private index"
                in move 2 (fn () =>
                let val value = scalar (hd indices)
                    val width = scalar (List.last indices)
                    fun parse token indices arguments =
                      cpc_bv_parsefn token [] [value,width]
                in recipe parse frame token [] [] end) end
            | ("@bit",[index,word]) =>
                let val source = hd (leading token 1 arguments)
                in move 1 (fn () =>
                let val index = case source of P.LiteralIndex term => term
                      | _ => B.small_index_with_policy backend frame
                          (#index_limit limits) index
                    fun parse token indices arguments =
                      cpc_bv_parsefn token indices (index::arguments)
                in recipe parse frame token [] [word] end) end
            | _ => recipe cpc_bv_parsefn frame token indices arguments)
      val _ = List.app indexed cpc_indexed_term_families
      val _ = (#add_constructor_parser terms) ("to_fp_bv",fp)
      val _ = List.app (fn name =>
        (#add_constructor_parser terms) (name,bv)) ["@bv","@bit"]
      val _ = (#add_constructor_parser terms) ("@from_bools",
        SmtLib_GraphWordBuilders.bbterm backend limits)
    in () end

  (* The registry is shared by both typed factories. Native callbacks see
     only bounded type holes and admitted source indices, never operands. *)
  fun install_graph_cpc_constructors (backend:'a B.backend)
      (limits:SmtReplayResourcePolicy.recipe_policy)
      (terms:'a F.constructed_session) private_symbol =
    let
      val spend = B.syntax_spend backend
      val _ = B.enable_forall_blocks backend
      val _ = if List.all SmtReplayResourcePolicy.positive
          [#template_limit limits,#index_limit limits,
           #operand_limit limits,#token_limit limits] then () else
        raise ERR "graph_cpc_skolem" "nonpositive constructor contract"
      fun add (name,construct) = (#add_constructor_parser terms)
        (name,fn frame => fn token => fn indices => fn arguments =>
          let
            val _ = if SmtReplayResourcePolicy.allows
                (#operand_limit limits)
                (IntInf.fromInt (List.length indices +
                  List.length arguments)) then () else
              raise ERR "graph_cpc_skolem" "operand contract exceeded"
            val _ = if SmtReplayResourcePolicy.allows
                (#token_limit limits) (IntInf.fromInt (String.size token))
              then () else raise ERR "graph_cpc_skolem"
                "token contract exceeded"
          in construct frame token indices arguments end)
      val recipe = SmtLib_GraphTheories.recipe_parsefn_with_policy
        backend limits
      fun holes arguments = List.map
        (Term.genvar o B.type_of backend) arguments
      fun sources frame arguments = case B.constructor_sources backend of
          SOME {arguments,...} => arguments
        | NONE => List.map (B.source_syntax backend frame) arguments
      fun compile template variables = B.compile_recipe_with_policy
        {template=template,holes=variables,
         template_limit= #template_limit limits}
      fun note template variables originals =
        let
          (* Every free template head must be an explicit operand, whose
             source carries its allocated identity rather than a spelling. *)
          val _ = if List.all (fn free => List.exists
              (fn hole => Term.aconv free hole) variables)
              (Term.free_vars template) then () else
            raise ERR "graph_cpc_source" "unowned source template variable"
          val _ = spend (3 + 4 * IntInf.fromInt (List.length variables))
        in B.note_constructor_source backend (C.from_template
          {template=template,holes=variables,operands=originals}) end
      fun symbol frame term =
        let val (name,ty) = Term.dest_var term in
          private_symbol frame
            {kind=name,hol_type=ty,source=NONE,stable=true}
        end
      fun source_index originals frame position actual =
        let
          val source = List.nth (originals,position)
          fun nonliteral () =
            Term.mk_var ("cpc_nonliteral_index",C.type_of source)
          fun expanded () = raise ERR "graph_index"
            "expanded private index operand"
          fun admitted term =
            case SmtReplayImport.raw_size_with_policy
                (#index_limit limits) term of SOME _ => term
              | NONE => expanded ()
          (* A lexical source descriptor is not the scalar it denotes.
             Inspect only the actual argument's stock numeral spine. This
             neither evaluates arithmetic nor opens a binder or LET, and
             cannot unfold an arbitrary shared arithmetic DAG. *)
          fun constant expected value =
            (spend 1;case B.view backend frame value of
               B.Atom term => Term.is_const term andalso
                 Term.same_const term expected
             | _ => false)
          fun unary expected value =
            (spend 1;case B.view backend frame value of
               B.Apply (f,x) =>
                 if constant expected f then SOME x else NONE
             | _ => NONE)
          fun bits value = constant numSyntax.alt_zero_tm value orelse
            (case unary numSyntax.bit1_tm value of SOME rest => bits rest
             | NONE => case unary numSyntax.bit2_tm value of
                 SOME rest => bits rest | NONE => false)
          fun natural value = constant numSyntax.zero_tm value orelse
            (case unary numSyntax.numeral_tm value of
               SOME rest => bits rest | NONE => false)
          fun integer value = case unary intSyntax.negate_tm value of
              SOME rest => integer rest
            | NONE => case unary intSyntax.int_injection value of
                SOME rest => natural rest | NONE => false
          fun scalar () =
            if natural actual orelse integer actual then
              (B.small_index_with_policy backend frame
                (#index_limit limits) actual
               handle error as Feedback.HOL_ERR detail =>
                 if Feedback.top_function_of detail = "index" andalso
                    Feedback.message_of detail = "expanded literal index"
                 then expanded () else raise error)
            else nonliteral ()
        in case C.retained_native spend source of
            SOME term => if Term.is_var term then scalar ()
              else admitted term
          | NONE => if C.is_numeric_literal spend source then scalar ()
              else nonliteral ()
        end
      fun opaque native frame token indices arguments =
        let
          val variables = holes arguments
          val template = B.index_callback backend
            (fn () => native token
              (List.map (fn _ => boolSyntax.T) indices) variables)
          val (head,actual) = boolSyntax.strip_comb template
          val _ = if Term.is_var head andalso
              List.length actual = List.length variables andalso
              ListPair.allEq (Lib.uncurry Term.aconv) (actual,variables)
            then () else raise ERR "graph_cpc_skolem"
              "registry callback is not an audited opaque application"
          val head_hole = Term.genvar (Term.type_of head)
          val transport = Term.list_mk_comb (head_hole,variables)
          val marker = symbol frame head
          val value = B.construct_with_policy backend frame
            (compile transport (head_hole::variables))
            (graph_private_reference backend frame marker::arguments)
          val _ = note transport (head_hole::variables)
            (C.private_atom (graph_private_descriptor backend marker) ::
             sources frame arguments)
          val _ = B.note_index_callback backend (token,native,NONE)
        in value end
      fun private_const frame token indices arguments =
        let
          val variables = holes arguments
          (* Preserve the native order of malformed/signature checks before
             observing the source index. Only the index is ever realized. *)
          val _ = if token="@const" andalso null indices andalso
              List.length arguments=2 then () else
            ignore (B.index_callback backend (fn () =>
              cpc_private_const_parsefn token
                (List.map (fn _ => boolSyntax.T) indices) variables))
          val [number,marker] = arguments
          val _ = cpc_expect_type "cpc_private_const_parsefn"
            intSyntax.int_ty (hd variables)
            handle Feedback.HOL_ERR _ =>
              raise ERR "cpc_private_const_parsefn"
                "@const index must have HOL int type"
          val original = source_index (sources frame arguments) frame
            0 number
          val native = B.index_callback backend (fn () =>
            cpc_private_const_parsefn token []
              [original,Term.genvar (B.type_of backend marker)])
          val magnitude = numeral_of_term token original
          val magnitude = valOf
            (IntInf.fromString (Arbnum.toString magnitude))
          val _ = if SmtReplayResourcePolicy.allows
              (#index_limit limits) magnitude then () else
            raise ERR "graph_index" "private numeric index exceeds contract"
          val value = graph_private_atom backend frame (symbol frame native)
          val _ = B.note_index_callback backend
            (token,cpc_private_const_parsefn,SOME native)
        in value end
      fun scoped native frame token indices arguments =
        let
          val variables = holes arguments
          val originals = sources frame arguments
          val avoids = C.all_variables spend originals
          val ordinary = B.index_callback backend (fn () =>
            native token (List.map (fn _ => boolSyntax.T) indices)
              variables)
          (* These three entries introduce one stock choice binder. Rename
             its bounded template against source names, not graph names. *)
          fun rename term =
            if Term.is_abs term then
              let val (old,body) = Term.dest_abs term
                  val fresh = Term.variant avoids old
              in Term.mk_abs (fresh,
                Term.subst [{redex=old,residue=fresh}] body) end
            else if Term.is_comb term then
              let val (f,x) = Term.dest_comb term
              in Term.mk_comb (rename f,rename x) end
            else term
          val ordinary = rename ordinary
          (* Lambda lifting keeps every actual operand outside native
             binders. The graph builder owns the resulting bound scopes. *)
          val transport = Term.list_mk_comb
            (Term.list_mk_abs (variables,ordinary),variables)
          val value = B.construct_with_policy backend frame
            (compile transport variables) arguments
          val _ = note ordinary variables originals
          val _ = B.note_index_callback backend (token,native,NONE)
        in value end

      (* Rebuild source SYNTAX nodewise, not source terms or graph operands.
         Free lexical descriptors and private atoms are different cases.
         Memo environments contain only relevant free descriptors; fresh
         binders in unrelated branches cannot split a shared-child cache. *)
      fun build_source frame original =
        let
          val base = frame
          (* Descriptor keys are the actual allocated markers, never their
             native constructor names or lexical lookup keys. The inventory
             is shared across construction scopes. *)
          val markers = List.foldl (fn ({marker,...},table) =>
            (spend 1;Redblackmap.insert (table,
              graph_private_descriptor backend marker,marker)))
            (Redblackmap.mkDict
              (fn pair => (spend 1;Term.compare pair)))
            ((#private_bindings (#reader terms)) ())
          val serial = ref (0:IntInf.int)
          fun compare ((a,xs),(b,ys)) =
            (spend 1;case IntInf.compare (a,b) of
               EQUAL => List.collate
                 (fn pair => (spend 1;IntInf.compare pair)) (xs,ys)
             | order => order)
          val memo = ref (Redblackmap.mkDict compare)
          fun equal (left,right) =
            C.aconv spend (C.variable left,C.variable right)
          fun lookup variable [] = NONE
            | lookup variable ((old,value,_,_)::rest) =
                if equal (old,variable) then SOME value
                else lookup variable rest
          fun walk frame environment source =
            let
              val free = C.free_variables spend source
              fun project [] _ = []
                | project ((entry as (variable,_,_,_))::rest) seen =
                    if List.exists (fn old => equal (variable,old)) seen
                    then project rest seen
                    else if List.exists
                        (fn other => equal (variable,other)) free then
                      entry::project rest (variable::seen)
                    else project rest (variable::seen)
              val relevant = project environment []
              (* Hoist invariant syntax only to this build's base frame.
                 No lexical free variables does not mean globally closed:
                 private atoms may belong to an enclosing non-root scope.
                 Never strand shared children in a retired sibling scope. *)
              val frame = case relevant of
                  (_,_,_,owner)::_ => owner
                | [] => base
              val key = (C.identity source,
                List.map (fn (_,_,id,_) => id) relevant)
            in case Redblackmap.peek (!memo,key) of SOME value => value
             | NONE =>
               let
                 val value = case C.view spend source of
                     C.Variable variable =>
                       (case lookup variable environment of
                          SOME value => value
                        | NONE =>
                          let val (name,ty) = Term.dest_var variable
                          in case B.lookup backend frame name of
                              SOME value =>
                                if cpc_type_eq (B.type_of backend value,ty)
                                then value else raise ERR "graph_cpc_source"
                                  "lexical source sort mismatch"
                            | NONE =>
                                let
                                  val private = (#private_bindings
                                    (#reader terms)) ()
                                  fun is_private node = List.exists
                                    (fn {marker,...} =>
                                      (spend 1;B.same_value backend
                                        (node,marker))) private
                                  val flexible = List.exists
                                    (fn {node,lexical,...} =>
                                      equal (variable,lexical) andalso
                                      not (is_private node))
                                    (B.solver_variables backend)
                                in B.variable backend frame
                                  (if flexible then G.SolverFlexible
                                   else G.RigidSource) (name,ty) end
                          end)
                   | C.Atom term =>
                       if Term.is_var term then
                         (* Private atoms never enter lexical lookup, even
                            on a descriptor collision with a source binder.
                            Missing provenance must not allocate a new ID. *)
                         (spend 1;case Redblackmap.peek (markers,term) of
                            SOME marker =>
                              graph_private_reference backend frame marker
                          | NONE => raise ERR "graph_cpc_source"
                              "unknown private marker descriptor")
                       else if Term.is_const term then
                         B.literal backend frame term
                       else raise ERR "graph_cpc_source"
                         "source view returned a compound atom"
                   | C.Apply (f,x) => B.application backend frame
                       (walk frame relevant f,walk frame relevant x)
                   | C.Abstract (variable,body) =>
                       let val (name,ty) = Term.dest_var variable in
                         B.abstraction backend frame (name,name,ty)
                           (fn inner =>
                             let
                               val value = valOf (B.lookup backend inner name)
                               val _ = serial := !serial+1
                             in walk inner
                               ((variable,value,!serial,inner)::relevant)
                               body end)
                       end
                 val _ = memo := Redblackmap.insert (!memo,key,value)
               in value end
            end
        in walk frame [] original end
      fun unary constant body =
        C.application (C.native constant,body)
      fun binder constant variable body =
        unary (Term.inst
          [{redex=Type.alpha,residue=Term.type_of variable}] constant)
          (C.abstraction (variable,body))
      fun dest_binder constant source = case C.dest_comb spend source of
          SOME (head,body) =>
            if C.is_constant spend constant head then C.dest_abs spend body
            else NONE
        | NONE => NONE
      fun integer where_ token originals frame position actual =
        (intSyntax.int_of_term
          (source_index originals frame position actual)
         handle Feedback.HOL_ERR _ => raise ERR where_
           "expected a concrete integer binder index")
      fun quantifiers frame token indices arguments =
        let
          val where_ = "cpc_quantifiers_skolemize_parsefn"
          val _ = cpc_exact_args where_ 2 arguments
          val _ = if token="@quantifiers_skolemize" andalso null indices
            then () else raise ERR where_
              "malformed @quantifiers_skolemize application"
          val [quantified,index_value] = arguments
          val _ = cpc_expect_int token
            (Term.genvar (B.type_of backend index_value))
          val originals = sources frame arguments
          val index = integer where_ token originals frame 1 index_value
          val _ = if Arbint.< (index,Arbint.zero) then
              raise ERR where_ "binder index is negative" else ()
          val source = hd originals
          val _ = case dest_binder boolSyntax.universal source of
              SOME _ => ()
            | NONE => raise ERR where_ "expected a FORALL Boolean formula"
          val (canonical,count) = case B.forall_block backend source of
              SOME result => result
            | NONE => raise ERR where_
                "source FORALL binder-block metadata is unavailable"
          val _ = if count > 0 then () else
            raise Feedback.mk_HOL_ERR "CPC_Proof" "cpc_skolem_witnesses"
              "expected a positive immediate FORALL binder count"
          val _ = if Arbint.< (index,Arbint.fromInt count) then ()
            else raise ERR where_
              "binder index is outside the quantified formula"
          fun peel 0 source variables = (List.rev variables,source)
            | peel remaining source variables =
                (case dest_binder boolSyntax.universal source of
                   SOME (variable,body) =>
                     peel (remaining-1) body (variable::variables)
                 | NONE => raise ERR where_
                     "immediate FORALL binder count exceeds binder spine")
          val (variables,body) = peel count canonical []
          val existential = List.foldr
            (fn (variable,body) => binder boolSyntax.existential variable body)
            (unary boolSyntax.negation body) variables
          fun select current source =
            case dest_binder boolSyntax.existential source of
              NONE => raise ERR where_ "malformed generated existential spine"
            | SOME (variable,body) =>
                let val witness = binder boolSyntax.select variable body
                in if Arbint.compare (index,current)=EQUAL then witness
                  else select (Arbint.+ (current,Arbint.one))
                    (C.substitute spend [(variable,witness)] body) end
          val witness = select Arbint.zero existential
          val value = build_source frame witness
          val _ = B.note_constructor_source backend witness
        in value end
      fun concat_pair regex = case C.dest_comb spend regex of
          SOME (front,right) =>
            (case C.dest_comb spend front of
               SOME (head,left) =>
                 if C.is_constant spend
                     (Term.prim_mk_const
                       {Thy="smtstring",Name="reglan_concat"}) head
                 then SOME (left,right) else NONE
             | NONE => NONE)
        | NONE => NONE
      fun regexps regex =
        let
          fun recognized body middle suffix =
            case C.dest_comb spend middle of
              SOME (head,star_body) =>
                if C.is_constant spend
                    (Term.prim_mk_const
                      {Thy="smtstring",Name="reglan_star"}) head andalso
                    C.aconv spend (body,star_body) andalso
                    C.aconv spend (body,suffix)
                then SOME [body,middle,suffix] else NONE
            | NONE => NONE
          val right = case concat_pair regex of
              SOME (body,rest) =>
                (case concat_pair rest of SOME (middle,suffix) =>
                   recognized body middle suffix | NONE => NONE)
            | NONE => NONE
          val direct = case right of SOME result => SOME result
            | NONE => case concat_pair regex of
                SOME (front,suffix) =>
                  (case concat_pair front of SOME (body,middle) =>
                     recognized body middle suffix | NONE => NONE)
              | NONE => NONE
          val emitted = ref (0:IntInf.int)
          fun flatten source tail = case concat_pair source of
              SOME (left,right) => flatten left (flatten right tail)
            | NONE =>
                (emitted := !emitted+1;
                 if SmtReplayResourcePolicy.allows
                     (#template_limit limits) (!emitted) then source::tail
                 else raise ERR "graph_cpc_skolem"
                   "decomposition exceeds contract")
        in case direct of SOME result => result
          | NONE => flatten regex [] end
      fun regex_component frame token indices arguments =
        let
          val _ = if null indices then () else
            raise ERR "cpc_string_skolem_parsefn"
              (token ^ " does not accept indices")
          val _ = cpc_exact_args "cpc_string_skolem_parsefn" 3 arguments
          val [string,regex,index_value] = arguments
          val [string_hole,regex_hole,index_hole] = holes arguments
          val _ = cpc_expect_smtstr token string_hole
          val _ = cpc_expect_reglan token regex_hole
          val _ = cpc_expect_int token index_hole
          val originals = sources frame arguments
          val index_term = source_index originals frame 2 index_value
          val index = Arbint.toInt (intSyntax.int_of_term index_term)
            handle Overflow => raise ERR "cpc_re_unfold_pos_component"
              "component index is too large"
          val _ = if index >= 0 then () else
            raise ERR "cpc_re_unfold_pos_component"
              "component index is negative"
          val components = regexps (List.nth (originals,1))
          val _ = if index < List.length components then () else
            raise ERR "cpc_re_unfold_pos_component"
              "component index is outside the regular-expression concat"
          val _ = if SmtReplayResourcePolicy.allows
              (#template_limit limits)
              (IntInf.fromInt (List.length components)) then () else
            raise ERR "graph_cpc_skolem" "decomposition exceeds contract"
          val component_holes = List.map (Term.genvar o C.type_of) components
          val variables = string_hole::component_holes
          val avoids = C.all_variables spend
            (List.take (originals,2))
          val {witness,...} = cpc_re_unfold_pos_decomposition_from
            component_holes avoids string_hole
          val ordinary = listSyntax.mk_el
            (numSyntax.mk_numeral (Arbnum.fromInt index),witness)
          val transport = Term.list_mk_comb
            (Term.list_mk_abs (variables,ordinary),variables)
          val compiled = compile transport variables
          val operands = string::List.map (build_source frame) components
          val value = B.construct_with_policy backend frame compiled operands
          val _ = note ordinary variables (hd originals::components)
        in value end
      fun install ({name,parse}:cpc_skolem_entry) =
        if name="@const" then add (name,private_const)
        else if name="@purify" then add (name,recipe parse)
        else if List.exists (Lib.equal name)
            ["@array_deq_diff","@sets_deq_diff","@bags_deq_diff"] then
          add (name,scoped parse)
        else if name="@quantifiers_skolemize" then add (name,quantifiers)
        else if name="@re_unfold_pos_component" then
          add (name,regex_component)
        else add (name,opaque parse)
    in List.app install cpc_parameterized_skolem_registry end

  fun install_graph_recipes (options : SmtLib_GraphFrontend.options)
      (terms : SmtLib_GraphFrontend.session) =
    let
      fun bounded_distinct token indices arguments =
        let val count = List.length arguments
            val limit = #template_limit (#recipe_limits options)
            (* Regex distinct builds pairwise relations. Admit its quadratic
               schematic work before invoking the authoritative builder. *)
            val regex = case arguments of first :: _ =>
                cpc_type_eq (Term.type_of first, cpc_reglan_ty)
              | [] => false
            val _ = if regex andalso count > 0 andalso
                count > limit div count div 16 then
              raise ERR "graph_distinct" "distinct schema exceeds contract"
            else ()
        in cpc_distinct_parsefn token indices arguments end
      val entries =
        [("=", cpc_equality_parsefn), ("distinct", bounded_distinct),
         ("str.++", cpc_concat_parsefn "smtstr_concat"),
         ("re.++", cpc_concat_parsefn "reglan_concat"),
         ("re.union", cpc_concat_parsefn "reglan_union"),
         ("re.inter", cpc_concat_parsefn "reglan_inter"),
         ("to_int", cpc_intreal_parsefn), ("to_real", cpc_intreal_parsefn),
         ("int.pow2", cpc_intreal_parsefn)]
      val totals = List.map (fn name => (name, cpc_arith_total_parsefn))
        ["div_total", "mod_total", "/_total", "@int_div_by_zero",
         "@mod_by_zero", "@div_by_zero", "**_total"]
      val backend = #backend (#reader terms)
      val graph = #graph options
      val private_symbol = graph_private_allocator terms
      val _ = install_graph_qualifications backend
        (#add_recipe_parser terms) (#add_constructor_parser terms)
        private_symbol
      val limits = #recipe_limits options
      fun finite n = SmtReplayResourcePolicy.AtMost (IntInf.fromInt n)
      val _ = install_graph_indexed backend
        {template_limit=finite (#template_limit limits),
         index_limit=finite (#index_limit limits),
         operand_limit=finite (#operand_limit limits),
         token_limit=finite (#token_limit limits)} terms
      val width_limit = #index_limit limits
      fun admitted term =
        case SmtReplayImport.bounded_raw_size width_limit term of
          SOME _ => term
        | NONE => raise ERR "graph_index" "expanded private literal index"
      fun natural term =
        let val value = numeral_of_term "graph private index" (admitted term)
        in if Arbnum.<= (value, Arbnum.fromInt width_limit) then value else
          raise ERR "graph_index" "private numeric index exceeds contract" end
      fun index (P.SourceIndex (node,_)) = index (P.ValueIndex (node,"("))
        | index (P.LexicalIndex pair) = index (P.ValueIndex pair)
        | index (P.LiteralIndex term) = natural term
        | index (P.ValueIndex (node, _)) =
            (case G.unfolded_nodes graph
                G.RawNodes width_limit node of
               SOME size => if size <= width_limit then
                   natural (G.representative graph node)
                 else raise ERR "graph_index" "expanded private index operand"
             | NONE => raise ERR "graph_index" "opaque private index operand")
        | index _ = raise ERR "graph_index" "nonliteral private index"
      fun marker frame token indices args =
        let
          val ty = case (token, indices, args) of
              ("Int", [], []) => intSyntax.int_ty
            | ("BitVec", [bits], []) =>
                wordsSyntax.mk_word_type (fcpLib.index_type (index bits))
            | ("FloatingPoint", [eb, sb], []) =>
                SmtLib_Theories.smtfp_type (index eb, index sb)
            | ("->", [], _ :: _ :: _) =>
                let val (domains, range) = Lib.front_last args in
                  boolSyntax.list_mk_fun
                    (List.map (B.type_of backend) domains,
                     B.type_of backend range) end
            | _ => raise ERR "cpc_sort_marker_parsefn"
                ("malformed CPC sort marker " ^ token)
        in graph_private_atom backend frame (private_symbol frame
          {kind = "@cpc." ^ token, hol_type = ty,
           source = NONE, stable = true}) end
      fun private_fp frame token indices args =
        if not (null indices) then raise ERR "cpc_fp_private_parsefn"
          "unexpected indices"
        else case args of
            [sort_marker] => graph_private_atom backend frame
              (private_symbol frame
                {kind = token, hol_type = B.type_of
                   backend sort_marker, source = NONE, stable = false})
          | [sort_marker, source] => graph_private_atom backend frame
              (private_symbol frame
                {kind = token, hol_type = B.type_of
                   backend sort_marker, source = SOME source, stable = true})
          | _ => raise ERR "cpc_fp_private_parsefn"
              (token ^ " expects a sort marker and at most one " ^
               "floating-point operand")
      fun private_total frame token indices args =
        if not (null indices) orelse null args then
          raise ERR "cpc_fp_total_parsefn" "malformed private FP operator"
        else
          let val types = List.map (B.type_of backend) args
              val ty = boolSyntax.list_mk_fun (types, hd types)
              val head = private_symbol frame
                {kind = token, hol_type = ty, source = NONE, stable = true}
              val originals = case B.constructor_sources backend of
                  SOME {arguments,...} => arguments
                | NONE => List.map (B.source_syntax backend frame) args
              val source = List.foldl (fn (arg,head) =>
                C.application (head,arg))
                (C.private_atom (graph_private_descriptor backend head))
                originals
              val _ = B.note_constructor_source backend source
          in List.foldl (fn (arg, head) =>
            B.application backend frame (head, arg))
            (graph_private_reference backend frame head) args end
      fun arithmetic frame token indices args =
        if null indices andalso null args andalso
            List.exists (Lib.equal token)
              ["@int_div_by_zero", "@mod_by_zero", "@div_by_zero"] then
          graph_private_atom backend frame (private_symbol frame
            {kind = token, hol_type = if token = "@div_by_zero"
               then realSyntax.real_ty else intSyntax.int_ty,
             source = NONE, stable = true})
        else SmtLib_GraphTheories.recipe_parsefn backend limits
          cpc_arith_total_parsefn frame token indices args
      val _ = List.app (#add_recipe_parser terms) entries
      val _ = List.app (fn (name, _) =>
        (#add_constructor_parser terms) (name, arithmetic)) totals
      val _ = List.app (fn name =>
        (#add_constructor_parser terms) (name, marker))
        ["Int", "BitVec", "FloatingPoint", "->"]
      val _ = List.app (fn name =>
        (#add_constructor_parser terms) (name, private_fp))
        ["@fp.SIGN", "@fp.EXPONENT", "@fp.SIGNIFICAND", "@fp.ZERO",
         "@fp.NAN", "@fp.INF"]
      val _ = List.app (fn name =>
        (#add_constructor_parser terms) (name, private_total))
        ["fp.max_total", "fp.min_total"]
      val _ = List.app (#add_recipe_parser terms)
        [("@fp.RMBITBLAST", cpc_fp_rounding_parsefn),
         ("bvite", cpc_bvite_parsefn), ("bvsltbv", cpc_bv_parsefn),
         ("bvultbv", cpc_bv_parsefn), ("concat", cpc_bv_parsefn),
         ("@bvsize", cpc_bv_parsefn)]
      val _ = install_graph_cpc_constructors backend
        {template_limit=finite (#template_limit limits),
         index_limit=finite (#index_limit limits),
         operand_limit=finite (#operand_limit limits),
         token_limit=finite (#token_limit limits)} terms private_symbol
    in () end

  (* Additive direct-ID frontend. This reads terms for graph proof records;
     script/rule reconstruction still uses the compatibility entry above
     until its specialized graph adapters and certificate gates pass. *)
  type graph_located_term = SmtLib_GraphFrontend.term
  type graph_step = proof_rule SmtLib_GraphFrontend.step
  fun graph_term_reader_with_version options version instream =
    let
      val version = resolve_version version
      val baseline = with_cpc_literals
        (SmtLib_Logics.parsedicts_of_logic "ALL")
      val reserved_names = Redblackmap.foldl
        (fn (key, _, keys) => key :: keys)
        (Redblackmap.foldl (fn (key, _, keys) => key :: keys)
          ["_", "!", "as", "let", "forall", "exists", "lambda", "match",
           "par", "declare-const", "declare-fun", "declare-sort",
           "declare-datatype", "declare-datatypes", "define",
           "assume", "assume-push", "step", "step-pop"] (#1 baseline))
        (#2 baseline)
      val terms = SmtLib_GraphFrontend.create_session options
        {solver = "cvc5", version = version,
         policy = SmtLib_GraphFrontend.CPC, reserved_names = reserved_names}
        (SmtLib_Parser.make_cpc_proof_stream_tokenizer instream)
      val _ = install_graph_recipes options terms
      val _ = (#add_literal_parser terms)
        (fn token => cpc_literal_parsefn token [] [])
    in #reader terms end
  fun graph_term_reader options instream =
    graph_term_reader_with_version options unknown_cvc_version instream

  (* Complete incremental command grammar. Semantic arguments retain their
     source occurrence trees; list/index/sort/hint roles are separate data,
     never counterfeit HOL terms. Proof-block lifetime belongs to replay. *)
  datatype 'a constructed_graph_argument =
      GraphTerm of 'a F.constructed_term
    | GraphList of 'a constructed_graph_argument list | GraphIndex of int
    | GraphSort of Type.hol_type | GraphHint of raw_term
  type graph_argument = G.node constructed_graph_argument
  type 'a constructed_graph_rule_step =
    {id : string, rule : proof_rule, premises : string list,
     conclusion : 'a F.constructed_term option,
     args : 'a constructed_graph_argument list,
     raw_conclusion : raw_term option, raw_args : raw_term list}
  type graph_rule_step = G.node constructed_graph_rule_step
  datatype 'a constructed_graph_command =
      GraphAssume of string * 'a F.constructed_term
    | GraphAssumePush of string * 'a F.constructed_term
    | GraphStep of {step : 'a constructed_graph_rule_step, pop : bool}
  type graph_command = G.node constructed_graph_command
  type 'a constructed_graph_proof =
    {commands : 'a constructed_graph_command list,cvc_version : string}
  type graph_proof = G.node constructed_graph_proof
  type 'a constructed_graph_command_reader =
    {next : unit -> 'a constructed_graph_command option,
     terms : 'a F.constructed_session,cvc_version : string}
  type graph_command_reader = G.node constructed_graph_command_reader

  (* The semantic backend eliminates LETs using IDs. Definition references
     retain shared occurrence metadata; term LET uses remain lexical atoms,
     not copies of their RHS operand boundaries. Lexical masks are independent
     of generated private-marker identities. Source atoms stay atomic. *)
  fun graph_premise_list (RawList entries) = entries
    | graph_premise_list (raw as RawAtom _) = [raw]

  (* Match parse_step's ordinary term-argument diagnostic, without turning
     cumulative resource exhaustion or a poisoned backend's primary error
     into a new parser exception. Special list/index/hint roles retain their
     own native diagnostics. *)
  fun graph_step_argument backend id rule_name parse raw =
    parse raw handle error as Feedback.HOL_ERR holerr =>
      if B.failure_requires_propagation backend then raise error
      else raise ERR "parse_step"
        ("could not parse :args for CPC step " ^ id ^
         " (rule " ^ rule_name ^ "): " ^ Feedback.message_of holerr)

  (* List entries are object terms, not nested argument packets or sort
     metadata. Like native list_terms, they have no outer :args wrapper. *)
  fun graph_object_argument parse_term parse_list lookup_list raw =
    case raw of
      RawList (RawAtom "@list" :: entries) =>
        GraphList (List.map (GraphTerm o parse_list) entries)
    | RawAtom name => (case lookup_list name of
        SOME entries => GraphList (List.map GraphTerm entries)
      | NONE => GraphTerm (parse_term raw))
    | _ => GraphTerm (parse_term raw)

  (* Match native's namespace order before consuming any definition body.
     Source callbacks may also live in the supplied declaration dictionary. *)
  fun graph_definition_name (namespace : F.namespace) dictionary key token =
    let
      val symbol = case P.proof_string_token token of
          SOME _ => raise ERR "parse_define" "string literal used as a symbol"
        | NONE => key token
      val name = P.proof_symbol_text symbol
      val _ =
        if set_member (#reserved namespace) symbol orelse
           set_member (#reserved namespace) name then
          raise ERR "parse_define"
            ("CPC definition may not shadow builtin symbol " ^ name)
        else if set_member (#proof_terms namespace) symbol then
          raise ERR "parse_define"
            ("duplicate CPC declaration or definition of symbol " ^ name)
        else if set_member (#source_terms namespace) symbol orelse
                Option.isSome (Redblackmap.peek (dictionary, symbol)) then
          raise ERR "parse_define"
            ("CPC definition may not redefine source symbol " ^ name)
        else ()
    in token end

  (* Lazy syntax adaptation at the native definition-list boundary only.
     The shared typed parser owns recursion, scopes and elaboration. Yield
     each operand before requesting its successor: an inner unknown symbol
     must win over later EOF. No object is buffered or reparsed and no
     semantic callback runs here.

     Only native parse_term's recursive CPC branches adapt their operands.
     Ordinary applications (including qualified heads, LET and annotations)
     keep ordinary parsing below them: adapting their subtrees would admit
     nested CPC testers that native rejects. Only ordinary term-head @var
     is quoted to bypass the graph parser's CPC branch. Its operands still
     parse first, preserving native unknown-symbol error order. Sorts,
     sorted binder declarations and annotation attributes remain data. Do not
     normalize AND/OR arity at this boundary either. *)
  val graph_ordinary_var_head =
    let val chars = ref (String.explode "|@var|")
        fun input () = case !chars of [] => NONE
          | char::rest => (chars := rest;SOME char)
    in P.make_cpc_proof_tokenizer_from_input input () end

  fun graph_definition_tokens indexed resolve_binder_list next =
    let
      fun finished () = raise ERR "graph_definition_tokens"
        "read beyond definition-list element"
      val resume = ref finished
      fun emit token continuation = (resume := continuation; token)
      fun literal token continuation () = emit token continuation
      fun close continuation () =
        let val token = next ()
            val _ = Library.expect_token ")" token
        in emit token continuation end
      fun data_from "(" continuation =
            emit "(" (data_tail continuation)
        | data_from token continuation = emit token continuation
      and data_tail continuation () =
        case next () of
          ")" => emit ")" continuation
        | token => data_from token (data_tail continuation)
      fun ordinary_term continuation () =
            ordinary_from (next ()) continuation
      and ordinary_from "(" continuation =
            emit "(" (ordinary_head continuation)
        | ordinary_from token continuation = emit token continuation
      and ordinary_terms continuation () =
        case next () of
          ")" => emit ")" continuation
        | token => ordinary_from token (ordinary_terms continuation)
      and ordinary_head continuation () =
        ordinary_head_from (next ()) continuation
      and ordinary_head_from token continuation =
        if token = "@var" then
          emit graph_ordinary_var_head
            (ordinary_terms continuation)
        else if token = "let" then
          emit token (ordinary_let continuation)
        else if token = "forall" orelse token = "exists" orelse
                token = "lambda" then
          emit token (ordinary_binders continuation)
        else if token = "!" then
          emit token (ordinary_term (data_tail continuation))
        else if token = "_" then
          emit token (fn () => emit (next ()) (ordinary_terms continuation))
        else if token = "as" then
          emit token (ordinary_as continuation)
        else ordinary_from token (ordinary_terms continuation)
      and ordinary_binders continuation () =
        case next () of
          "(" => emit "(" (fn () =>
            let val head = next () in
              if head = "@list" then
                emit head (ordinary_terms
                  (ordinary_term (close continuation)))
              else if head = ")" then
                emit head (ordinary_term (close continuation))
              else data_from head
                (data_tail (ordinary_term (close continuation)))
            end)
        | token => emit token (ordinary_term (close continuation))
      and ordinary_as continuation () =
        let val name = next () in
          if List.exists (Lib.equal name)
              ["const", "seq.empty", "set.empty", "set.universe",
               "bag.empty", "union"] then
            emit name (fn () => data_from (next ()) (close continuation))
          else ordinary_from name (ordinary_terms continuation)
        end
      and ordinary_let continuation () =
        emit (next ()) (ordinary_bindings
          (ordinary_term (close continuation)))
      and ordinary_bindings continuation () =
        case next () of
          ")" => emit ")" continuation
        | token => emit token (fn () => emit (next ())
            (ordinary_term (close (ordinary_bindings continuation))))
      fun term continuation () = term_from (next ()) continuation
      and term_from "(" continuation = emit "(" (head continuation)
        | term_from token continuation = emit token continuation
      and terms continuation () =
        case next () of
          ")" => emit ")" continuation
        | token => term_from token (terms continuation)
      and head continuation () =
        let val marked = next () in
        case cpc_semantic_token marked of
          "_" =>
            let val name = next () in
              if marked = "_" andalso indexed name then
                emit "_" (literal name (data_tail continuation))
              else emit "@" (fn () =>
                term_from name (terms continuation))
            end
        | "@" =>
            if marked = "@" then emit "@" (terms continuation)
            else ordinary_head_from marked continuation
        | "is" => emit "(" (literal "_" (literal "is"
            (tester continuation)))
        | token =>
            if token = "forall" orelse token = "exists" orelse
               token = "lambda" then
              emit token (binders continuation)
            else if token = "@var" then
              emit token (data_tail continuation)
            else ordinary_head_from marked continuation
        end
      and tester continuation () =
        let val constructor = next ()
            val _ = if constructor = "(" orelse constructor = ")" then
              raise ERR "parse_term"
                "CPC datatype tester expects a constructor symbol"
              else ()
        in emit constructor (literal ")" (term (close continuation))) end
      and binders continuation () =
        case next () of
          "(" => emit "(" (binder_head continuation)
        | token =>
            (resolve_binder_list token;
             emit P.cpc_recursive_named_binders
               (literal token (term (close continuation))))
      and binder_head continuation () =
        let val token = next () in
          if token = "@list" then
            emit P.cpc_recursive_binders (terms (term (close continuation)))
          else if token = ")" then
            emit token (ordinary_term (close continuation))
          else
            (* Native falls back to the ordinary shared parser for a
               standard sorted-variable block, including its body. *)
            data_from token
              (data_tail (ordinary_term (close continuation)))
        end
      val _ = resume := term finished
    in fn () => (!resume) () end

  (* Heterogeneous metadata, not structured rule formals. Unlike parse(raw),
     native list definitions elaborate recursive parse_term operands before
     reading the following syntax, including inside each list element.
     Top-level @var has no shared-parser callback: parse its sort and close
     before constructing it. Inline binder operands use the same recursive
     grammar, while binders below ordinary applications remain ordinary. *)
  fun graph_read_definition_list indexed resolve_binder_list next parse_from parse_sort
      private_variable locate =
    let
      fun ordinary prefix = parse_from (graph_definition_tokens indexed
        resolve_binder_list (Library.undo_look_ahead prefix next))
      fun object "(" =
            let val head = next () in
              if cpc_semantic_token head = "@var" then
                let
                  val name = cpc_var_name (next ())
                  val ty = parse_sort next
                  val _ = Library.expect_token ")" (next ())
                in private_variable (name, ty) end
              else ordinary ["(", head]
            end
        | object first = ordinary [first]
      fun entries acc =
        case next () of
          ")" => List.rev acc
        | first =>
            let val term = locate (object first)
            in entries (term :: acc) end
    in entries [] end

  (* Keep only alias names here, never copied list syntax or operands. The
     recursive parser resolves aliases before touching the body, unlike its
     ordinary sorted-binder fallback. *)
  fun graph_definition_lists indexed lookup_list symbol_key define_list =
    let
      val names = ref []
      fun resolve token =
        if Option.isSome (lookup_list token) then () else
          raise ERR "parse_term"
            ("undefined CPC @list alias " ^ token ^ " (known aliases: " ^
             String.concatWith ", " (List.rev (!names)) ^ ")")
      fun define (name, entries) =
        (define_list (name, entries); names := symbol_key name :: !names)
    in (graph_read_definition_list indexed resolve, define) end

  (* Only structured rule formals are homogeneous lists. Ordinary argument
     packets flatten @list and deliberately allow heterogeneous objects. *)
  fun graph_check_structured_argument backend id rule_name argument =
    let
      fun element_type (GraphTerm term) = B.type_of backend (#node term)
        | element_type _ = raise ERR "parse_step"
            "non-object element in CPC structured list"
      val _ = case argument of
          GraphList (first :: rest) =>
            let val ty = element_type first
            in if List.all (fn entry =>
                Type.compare (element_type entry, ty) = EQUAL) rest then ()
              else raise ERR "parse_step"
                ("CPC structured list has mixed element types in step " ^
                 id ^ " (rule " ^ rule_name ^ ")") end
        | _ => ()
    in argument end

  fun graph_structured_argument backend id rule_name parse lookup_list raw =
    graph_check_structured_argument backend id rule_name
      (graph_object_argument parse parse lookup_list raw)

  (* Native structured lists elaborate each element before reading the
     next. Buffer only the individual object, never the entire list. *)
  fun graph_read_structured_step_arguments next backend id rule_name
      parse lookup_list =
    let
      val _ = Library.expect_token "(" (next ())
      val check = graph_check_structured_argument backend id rule_name
      val argument = graph_structured_argument backend id rule_name
        parse lookup_list
      fun object first = read_raw_term
        (Library.undo_look_ahead [first] next)
      fun list raws terms =
        case next () of
          ")" => (RawList (RawAtom "@list" :: List.rev raws),
            check (GraphList (List.rev terms)))
        | first =>
            let val raw = object first
                val term = parse raw
            in list (raw :: raws) (GraphTerm term :: terms) end
      fun arguments raws args =
        case next () of
          ")" => (List.rev raws, List.rev args)
        | first =>
            let
              val (raw,arg) = if first = "(" then
                let val head = next () in
                  if head = "@list" then list [] [] else
                    let val raw = read_raw_term
                          (Library.undo_look_ahead [first,head] next)
                    in (raw,argument raw) end
                end
              else let val raw = RawAtom first
                   in (raw,argument raw) end
            in arguments (raw :: raws) (arg :: args) end
    in arguments [] [] end

  fun graph_argument_count (GraphList entries) = List.length entries
    | graph_argument_count _ = 1

  fun graph_step_argument_at backend id rule_name parse sort lookup_list
      position raw =
    let
      val ordinary = graph_object_argument
        (graph_step_argument backend id rule_name parse) parse lookup_list
      fun metadata raw =
        GraphSort (sort raw)
        handle error as Feedback.HOL_ERR holerr =>
          if B.failure_requires_propagation backend then raise error
          else raise ERR "parse_step"
            ("could not parse Set sort metadata for CPC step " ^ id ^
             " (rule " ^ rule_name ^ "): " ^ Feedback.message_of holerr)
    in case raw of
        RawList (RawAtom "Set" :: _) =>
          if is_set_sort_metadata rule_name position then metadata raw
          else ordinary raw
      | _ => ordinary raw
    end

  fun graph_step_arguments backend id rule_name parse sort lookup_list raws =
    let
      val argument = graph_step_argument_at backend id rule_name
        parse sort lookup_list
      fun arguments position [] = []
        | arguments position (raw :: rest) =
            let val arg = argument position raw
            in arg :: arguments (position + graph_argument_count arg) rest end
    in arguments 1 raws end

  (* Consume ordinary arguments once, elaborating each before reading the
     next. In particular, a bad Set marker precedes any later syntax error.
     Packet lengths still determine the native flattened metadata position. *)
  fun graph_read_step_arguments next argument =
    let
      val _ = Library.expect_token "(" (next ())
      fun arguments position raws args =
        case next () of
          ")" => (List.rev raws, List.rev args)
        | first =>
            let
              val raw = read_raw_term
                (Library.undo_look_ahead [first] next)
              val arg = argument position raw
            in arguments (position + graph_argument_count arg)
              (raw :: raws) (arg :: args) end
    in arguments 1 [] [] end

  fun graph_structured_rule_arguments (rule : proof_rule) =
    #replay_handler rule = "rare_inventory" orelse
    #name rule = "arith-mod-over-mod" orelse
    #name rule = "arith-mod-over-mod-mult"

  fun graph_ordinary_rule_arguments (rule : proof_rule) =
    not (List.exists (Lib.equal (#replay_handler rule))
      ["and_elim", "not_or_elim", "resolution", "exists_elim",
       "quant_rewrite", "rare_inventory"] orelse
      List.exists (Lib.equal (#name rule))
        ["cnf_and_pos", "cnf_or_neg", "arith-mod-over-mod",
         "arith-mod-over-mod-mult"])

  (* Only type parsing may be replayed for native diagnostics. Keep current
     declared sorts, replacing the frontend's -> entry by the native one.
     Resource/poison failures remain primary, as does a graph failure when
     native type parsing succeeds. *)
  fun graph_parse_sort backend tokens parse_sort sort_dictionary raw =
    tokens raw parse_sort handle error as Feedback.HOL_ERR _ =>
      if B.failure_requires_propagation backend then raise error
      else
        (ignore (tokens raw (fn next => parse_cpc_type next
           (Library.extend_dict (("->", cpc_function_sort),
             sort_dictionary ()))));
         raise error)

  (* Ordinary native :args validates the set against its sort marker only
     after all arguments parse. Read admitted type metadata, never realize
     a graph operand. Lists retain their packet role but count as the same
     flattened argument sequence used by the native validator. *)
  fun graph_validate_set_sort_metadata backend id rule_name args =
    let
      fun types (GraphTerm term) = [SOME (B.type_of backend (#node term))]
        | types (GraphSort ty) = [SOME ty]
        | types (GraphList entries) = List.concat (List.map types entries)
        | types _ = [NONE]
      fun check (SOME set, SOME marker) =
            if Type.compare (set,marker) = EQUAL then ()
            else raise ERR "parse_step"
              ("CPC Set sort metadata does not match its set argument " ^
               "in step " ^ id ^ " (rule " ^ rule_name ^ ")")
        | check _ = ()
      fun validate member =
        case (member,List.concat (List.map types args)) of
          (false,[set,marker]) => check (set,marker)
        | (true,[_,set,marker]) => check (set,marker)
        | _ => ()
      val _ = case rule_name of
          "sets-card-emp" => validate false
        | "sets-is-empty-elim" => validate false
        | "sets-member-emp" => validate true
        | "sets-minus-self" => validate false
        | _ => ()
    in args end

  fun graph_locations (backend:'a B.backend) symbol_key =
    let
      val serial = ref 0
      val definitions = ref (Redblackmap.mkDict String.compare)
      fun binding occurrence =
        (serial := !serial + 1;(!serial,occurrence))
      fun resolve environment
          (whole as P.ConstructionOccurrence {value,role,token,children}) =
        let
          val _ = B.syntax_spend backend
            (1 + IntInf.fromInt (List.length children))
          fun rebuild children = P.ConstructionOccurrence
            {value=value,role=role,token=token,children=children}
          fun lookup [] = Redblackmap.peek (!definitions,symbol_key token)
            | lookup ((key,entry)::rest) =
                (B.syntax_spend backend 1;
                 if key=symbol_key token then entry else lookup rest)
        in case role of
            P.ConstructionAtom =>
              (case lookup environment of NONE => whole
               | SOME (stamp,occurrence) => P.ConstructionOccurrence
                   {value=value,role=P.ConstructionReference stamp,
                    token=token,children=[occurrence]})
          | P.ConstructionLet names =>
              let
                val rhs = List.map (resolve environment)
                  (List.take (children,List.length names))
                (* Elaboration substitutes values, not occurrence roles.
                   Keep a term LET's lexical uses atomic; in particular a
                   use of c cannot supply the immediate slots of its RHS.
                   RHSs see the outer frame (simultaneous LET). *)
                val masks = List.map (fn (key,_) => (key,NONE)) names
                val body = resolve (masks @ environment)
                  (List.last children)
              in rebuild (rhs @ [body]) end
          | P.ConstructionBinder {variables,...} =>
              let val masks = List.concat (List.map (fn (key,name,_) =>
                    [(key,NONE),(symbol_key name,NONE)]) variables)
              in rebuild (List.map (resolve (masks @ environment)) children)
              end
          | _ => rebuild (List.map (resolve environment) children)
        end
      fun locate (term:'a F.constructed_term) : 'a F.constructed_term =
        {node= #node term,scope= #scope term,
         source_syntax= #source_syntax term,binder_blocks= #binder_blocks term,
         occurrence=resolve [] (#occurrence term)}
      fun define (name,term:'a F.constructed_term) =
        definitions := Redblackmap.insert
          (!definitions,symbol_key name,binding (#occurrence term))
    in {locate=locate,define=define} end

  fun graph_command_reader_with_factory make_session
      (options : SmtLib_GraphFrontend.options)
      (declaration_dicts : dicts) requested_version instream
      : graph_command_reader =
    let
      val version = resolve_version requested_version
      val baseline = with_cpc_literals
        (SmtLib_Logics.parsedicts_of_logic "ALL")
      val syntax_names =
        ["_", "!", "as", "let", "forall", "exists", "lambda", "match",
         "par", "declare-const", "declare-fun", "declare-sort",
         "declare-datatype", "declare-datatypes", "define", "assume",
         "assume-push", "step", "step-pop"]
      val reserved_names = Redblackmap.foldl
        (fn (key, _, keys) => key :: keys)
        (Redblackmap.foldl (fn (key, _, keys) => key :: keys)
          syntax_names (#1 baseline)) (#2 baseline)
      val token = P.make_cpc_proof_stream_tokenizer instream
      val terms = make_session options
        {solver = "cvc5", version = version, policy = F.CPC,
         reserved_names = reserved_names} token
      val _ = install_graph_recipes options terms
      val indexed = cpc_indexed_identifier (fn name =>
        let val namespace = (#namespace terms) () in
          set_member (#proof_terms namespace) name orelse
          set_member (#source_terms namespace) name orelse
          Option.isSome (Redblackmap.peek (#2 declaration_dicts, name))
        end)
      val (graph_read_definition_list, define_list) = graph_definition_lists
        indexed (#lookup_list terms) (#symbol_key terms) (#define_list terms)
      val _ = (#add_literal_parser terms)
        (fn token => cpc_literal_parsefn token [] [])
      val locations = graph_locations (#backend (#reader terms))
        (#symbol_key terms)
      val known = ref (HOLset.empty String.compare)
      val snapshots = ref ([] : string HOLset.set list)
      val seen = ref
        (Redblackmap.mkDict String.compare :
          (string, string list) Redblackmap.dict)
      val pending = ref (NONE : (string * string) option)
      val ended = ref false
      val _ = Library.expect_token "(" (token ())
      fun error message = raise ERR "graph_commands" message
      fun tokens raw action =
        let val remaining = ref (raw_tokens raw)
            fun next () = case !remaining of
                first :: rest => (remaining := rest; first)
              | [] => error "buffered term ended unexpectedly"
            val result = action next
            val _ = if null (!remaining) then () else
              error "buffered term has trailing syntax"
        in result end
      fun sort raw = graph_parse_sort (#backend (#reader terms)) tokens
        (#parse_sort terms) (#sort_dictionary terms) raw
      fun graph_application raw = case raw of
          RawList (RawAtom "_" :: RawAtom name :: indices) =>
            if name = "BitVec" orelse name = "FloatingPoint" then
              let
                val arity = if name = "BitVec" then 1 else 2
                val _ = if List.length indices = arity then () else
                  error ("malformed CPC indexed sort marker " ^ name)
                (* These are actual indexed sort markers, not the CPC
                   higher-order application form. The installed marker
                   recipe admits every literal/value index and its width
                   before constructing the authoritative HOL type. *)
              in RawList (RawAtom "_" :: RawAtom name ::
                List.map graph_application indices) end
            else if indexed name then raw
            else RawList (RawAtom "@" ::
              List.map graph_application (RawAtom name :: indices))
        | RawList (RawAtom "_" :: arguments) =>
            RawList (RawAtom "@" :: List.map graph_application arguments)
        | RawList ((head as RawList (RawAtom "_" :: _)) :: arguments) =>
            RawList (head :: List.map graph_application arguments)
        | RawList entries => RawList (List.map graph_application entries)
        | RawAtom _ => raw
      fun parse raw : graph_located_term = (#locate locations) (
        case raw of
          RawList [RawAtom "@var", RawAtom name, ty] =>
            (#private_variable terms) (cpc_var_name name, sort ty)
        | _ => tokens (graph_application (normalize_cpc_testers indexed raw))
            (#parse_from terms))
      fun raw_list context raw = case raw of RawList entries => entries
        | _ => error (context ^ " must be parenthesized")
      fun atom context raw = case raw of RawAtom text => text
        | _ => error (context ^ " must be atomic")
      fun id text = cpc_id_key "graph_commands" "command ID" text
      fun fresh name = ensure_fresh_id "graph_commands" name known
      fun add name = known := HOLset.add (!known, name)
      fun close name = case !snapshots of
          previous :: rest => (known := previous; snapshots := rest; add name)
        | [] => error ("step-pop without assume-push in CPC step " ^ name)
      fun declarations kind =
        let val name = token ()
            val domain = if kind = "declare-fun" then
                List.map sort (raw_list "function domain"
                  (read_raw_term token))
              else []
            val range = sort (read_raw_term token)
            val _ = Library.expect_token ")" (token ())
        in (#declare terms) (name, boolSyntax.list_mk_fun (domain, range)) end
      fun datatype_declaration kind =
        let
          val namespace = (#namespace terms) ()
          val symbol_key = #symbol_key terms
          fun binding raw = case raw of
              RawList [RawAtom name, RawAtom arity] =>
                let val (key, text) = datatype_symbol_using symbol_key
                      "declare-datatypes" "datatype sort" name
                in (key, text, datatype_arity "declare-datatypes" text arity)
                end
            | _ => error "malformed datatype binding"
          val declarations = if kind = "declare-datatype" then
              let
                val name = token ()
                val (key, text) = datatype_symbol_using symbol_key
                  kind "datatype sort" name
                val body = read_raw_term token
                val arity = case body of
                    RawList [RawAtom "par", RawList params, RawList _] =>
                      List.length params
                  | _ => 0
              in [parse_datatype_body_using symbol_key
                kind key text arity body] end
            else
              let val bindings = List.map binding
                    (raw_list "datatype bindings" (read_raw_term token))
                  val bodies = raw_list "datatype bodies"
                    (read_raw_term token)
                  val _ = if List.length bindings = List.length bodies then
                    () else error "datatype binding/body count mismatch"
              in ListPair.mapEq (fn ((key, name, arity), body) =>
                parse_datatype_body_using symbol_key kind key name arity body)
                (bindings, bodies) end
          val _ = Library.expect_token ")" (token ())
        in validate_datatype_declarations_using namespace
          (ref ((#sort_dictionary terms) (), #2 declaration_dicts))
          declarations end
      fun define_term pair =
        ((#define terms) pair;(#define locations) pair)
      fun define () =
        let
          val name = graph_definition_name ((#namespace terms) ())
            (#2 declaration_dicts) (#symbol_key terms) (token ())
          val start = token ()
          val first = if start = "(" then
              (Library.expect_token ")" (token ()); token ()) else start
          fun ordinary prefix =
            let
              val raw = read_raw_term
                (Library.undo_look_ahead prefix token)
              val _ = Library.expect_token ")" (token ())
            in case raw of
                RawList [RawAtom "@var", RawAtom variable, ty] =>
                  ignore ((#define_variable terms)
                    (name, cpc_var_name variable, sort ty))
              | RawList [RawAtom "@purify", payload] =>
                  define_term (name, parse payload)
              | _ => define_term (name, parse raw)
            end
        in
          if first = "@list" then
            (skip_sexp token; (#define_opaque terms) name)
          else if first = "(" then
            let val head = token () in
              if head = "@list" then
                let
                  val entries = graph_read_definition_list token
                    (#parse_from terms) (#parse_sort terms)
                    (#private_variable terms) (#locate locations)
                  val _ = define_list (name, entries)
                in Library.expect_token ")" (token ()) end
              else ordinary [first, head]
            end
          else ordinary [first]
        end
      val argument = graph_object_argument parse parse (#lookup_list terms)
      fun index raw =
        let val text = atom "CPC index" raw
        in case Int.fromString text of
            SOME index => if index >= 0 then GraphIndex index else
              error "negative CPC index"
          | NONE => error "non-numeral CPC index" end
      fun rule_arguments name rule_name (rule : proof_rule) raws =
        if #replay_handler rule = "and_elim" orelse
           #replay_handler rule = "not_or_elim" then
          (case raws of [raw] => [index raw]
           | _ => error "elimination rule expects one index")
        else if #name rule = "cnf_and_pos" orelse
                #name rule = "cnf_or_neg" then
          (case raws of [object, number] =>
              [GraphTerm (parse object), index number]
           | _ => error "CNF rule expects an object and index")
        else if #name rule = "resolution" then
          (case raws of polarity :: pivot :: hints =>
              GraphTerm (parse polarity) :: GraphTerm (parse pivot) ::
                List.map GraphHint hints
           | [] => []
           | _ => error "resolution requires polarity and pivot")
        else if #replay_handler rule = "resolution" then
          (case raws of [] => []
           | target :: rest => GraphTerm (parse target) ::
               List.map argument rest)
        else if #replay_handler rule = "exists_elim" orelse
                #replay_handler rule = "quant_rewrite" then
          List.map argument raws
        else if #replay_handler rule = "rare_inventory" orelse
                #name rule = "arith-mod-over-mod" orelse
                #name rule = "arith-mod-over-mod-mult" then
          List.map (graph_structured_argument (#backend (#reader terms))
            name rule_name parse (#lookup_list terms)) raws
        else graph_validate_set_sort_metadata
          (#backend (#reader terms)) name rule_name
          (graph_step_arguments (#backend (#reader terms)) name rule_name
            parse sort (#lookup_list terms) raws)
      fun step kind =
        let
          val consumed = ref ([] : string list)
          fun next () = let val text = token () in
            consumed := text :: !consumed; text end
          val name = id (next ())
          val _ = fresh name
          val first = next ()
          val conclusion = if first = ":rule" then NONE else
            SOME (read_raw_term (Library.undo_look_ahead [first] next))
          val _ = if first = ":rule" then () else
            Library.expect_token ":rule" (next ())
          val rule_name = next ()
          val rule = case lookup_rule version rule_name of
              SOME rule => rule
            | NONE => raise ERR "graph_step"
                (registry_lookup_failure version rule_name)
          (* Supported conclusions precede all attributes. Unsupported
             inventory entries must remain entirely syntax-only. *)
          val eager = not (Option.isSome
            (rare_unsupported_diagnostic rule_name))
          val parsed_conclusion = if eager then
              SOME (Option.map parse conclusion) else NONE
          val parsed_args = ref NONE
          fun attrs saw_premises saw_args premises args =
            case next () of
              ")" => (premises, args)
            | ":premises" =>
                if saw_premises then error "duplicate :premises" else
                  let val premises = List.map
                        (cpc_id_key "graph_step" "premise ID" o
                          atom "premise ID")
                        (graph_premise_list (read_raw_term next))
                      val _ = List.app
                        (require_known_premise name known) premises
                  in attrs true saw_args premises args end
            | ":args" => if saw_args then error "duplicate :args" else
                let
                  val raws =
                    if eager andalso (graph_ordinary_rule_arguments rule
                        orelse graph_structured_rule_arguments rule) then
                      let
                        val backend = #backend (#reader terms)
                        val (raws, args) =
                          if graph_structured_rule_arguments rule then
                            graph_read_structured_step_arguments next backend
                              name rule_name parse (#lookup_list terms)
                          else graph_read_step_arguments next
                            (graph_step_argument_at backend name rule_name
                              parse sort (#lookup_list terms))
                        val _ = parsed_args := SOME
                          (graph_validate_set_sort_metadata backend name
                            rule_name args)
                      in raws end
                    else
                      let
                        val raws = raw_list "arguments" (read_raw_term next)
                        val _ = if eager then parsed_args :=
                          SOME (rule_arguments name rule_name rule raws)
                          else ()
                      in raws end
                in attrs saw_premises true premises raws end
            | attribute => error ("unknown CPC step attribute " ^ attribute)
          val (premises, args) = attrs false false [] []
          val _ = register_command_signature seen kind name
            (List.rev (!consumed))
          val _ = if kind = "step-pop" then close name else add name
        in case rare_unsupported_diagnostic rule_name of
            SOME diagnostic =>
              let fun raw_error detail = raise ERR "parse_step"
                    ("malformed raw term in unsupported CPC step " ^ name ^
                     ": " ^ detail)
                  val _ = Option.app (validate_raw_term raw_error) conclusion
                  val _ = List.app (validate_raw_term raw_error) args
                  val _ = if Option.isSome (!pending) then () else
                    pending := SOME (rule_name, diagnostic)
              in NONE end
          | NONE => SOME (GraphStep
              {step = {id = name, rule = rule, premises = premises,
                 conclusion = (case parsed_conclusion of
                     SOME result => result
                   | NONE => Option.map parse conclusion),
                 args = (case !parsed_args of SOME result => result
                   | NONE => rule_arguments name rule_name rule args),
                 raw_conclusion = conclusion, raw_args = args},
               pop = kind = "step-pop"})
        end
      fun finish () =
        let val _ = if null (!snapshots) then () else
              error "unclosed assume-push scope at end of CPC proof wrapper"
            val trailing = SOME (token ()) handle P.CPCProofEOF => NONE
            val _ = case trailing of NONE => () | SOME text =>
              error ("second CPC proof wrapper or trailing token '" ^
                P.proof_symbol_text text ^ "'")
            val _ = ended := true
        in case !pending of NONE => NONE
          | SOME (rule, diagnostic) => raise ERR rule diagnostic end
      fun next () = if !ended then NONE else
        case token () of
          ")" => finish ()
        | "(" =>
            (case token () of
               "declare-const" => (declarations "declare-const"; next ())
             | "declare-fun" => (declarations "declare-fun"; next ())
             | "declare-sort" =>
                 let val name = token ()
                     val arity = datatype_arity "declare-sort" name (token ())
                     val _ = Library.expect_token ")" (token ())
                 in (#declare_sort terms) (name, arity); next () end
             | "declare-datatype" =>
                 (datatype_declaration "declare-datatype"; next ())
             | "declare-datatypes" =>
                 (datatype_declaration "declare-datatypes"; next ())
             | "define" => (define (); next ())
             | "assume" => assumption false
             | "assume-push" => assumption true
             | "step" => (case step "step" of
                 NONE => next () | command => command)
             | "step-pop" => (case step "step-pop" of
                 NONE => next () | command => command)
             | command => error ("unknown CPC construct " ^ command))
        | text => error ("unexpected CPC token '" ^
            P.proof_symbol_text text ^ "'")
      and assumption push =
        let val name = id (token ())
            val _ = fresh name
            val value = parse (read_raw_term token)
            val _ = Library.expect_token ")" (token ())
            val _ = if push then snapshots := !known :: !snapshots else ()
            val _ = add name
        in SOME (if push then GraphAssumePush (name, value)
          else GraphAssume (name, value)) end
      fun checked_next () = next () handle P.CPCProofEOF =>
        raise ERR "parse_stream_with_version"
          "unexpected end of CPC proof wrapper"
    in {next = checked_next, terms = terms, cvc_version = version} end

  fun graph_command_reader_with_version options declaration_dicts version input =
    graph_command_reader_with_factory F.create_session
      options declaration_dicts version input

  fun graph_configured_command_reader_with_version
      (configured : F.configured_options) declaration_dicts version input =
    graph_command_reader_with_factory
      (fn _ => F.create_configured_session configured)
      (#base configured) declaration_dicts version input

  fun packet requested_version (reader : graph_command_reader)
      : graph_proof SmtLib_GraphProof.packet =
    let
        fun commands acc = case (#next reader) () of
            NONE => List.rev acc | SOME command => commands (command :: acc)
        val proof = {commands = commands [], cvc_version = #cvc_version reader}
    in SmtLib_GraphProof.new
      {reader = #reader (#terms reader), proof = proof,
       requested_version = requested_version, close = fn () => ()} end

  fun parse_graph_packet_with_version options declaration_dicts version input =
    let val reader = graph_command_reader_with_version
          options declaration_dicts version input
    in packet version reader end

  fun parse_graph_configured_packet_with_version configured declaration_dicts
      version input =
    packet version (graph_configured_command_reader_with_version
      configured declaration_dicts version input)

  fun parse_graph_translation_packet_with_version options translation
      version input =
    let
      val configured = SmtLib_GraphTranslation.configured_options
        options translation
      val make_session = fn _ =>
        SmtLib_GraphTranslation.create_session options translation
      val dicts = SmtLib.parser_dicts_for_solver_translation "cvc5" translation
    in packet version (graph_command_reader_with_factory make_session
      (#base configured) dicts version input) end

  fun parse_graph_stream_with_version options declaration_dicts version input
      : graph_proof =
    SmtLib_GraphProof.proof
      (parse_graph_packet_with_version options declaration_dicts version input)

  fun policy_reader_length values =
    let fun count [] (n:IntInf.int) = n
          | count (_::rest) n = count rest (n+1)
    in count values 0 end
  fun policy_reader_width SmtReplayResourcePolicy.Uncapped _ = true
    | policy_reader_width (SmtReplayResourcePolicy.AtMost cap) value =
        cap >= 0 andalso Arbnum.<=
          (value,Arbnum.fromString (IntInf.toString cap))
  fun install_graph_recipes_with_policy_for_backend value_index
      (options:'a F.constructed_policy_options)
      (terms:'a F.constructed_session) =
    let
      fun bounded_distinct token indices arguments =
        let val count = policy_reader_length arguments
            val limit = #template_limit (#recipe_limits options)
            (* Regex distinct builds pairwise relations. Admit its quadratic
               schematic work before invoking the authoritative builder. *)
            val regex = case arguments of first :: _ =>
                cpc_type_eq (Term.type_of first, cpc_reglan_ty)
              | [] => false
            val _ = if regex andalso count > 0 andalso
                not (SmtReplayResourcePolicy.allows limit (count * count * 16)) then
              raise ERR "graph_distinct" "distinct schema exceeds contract"
            else ()
        in cpc_distinct_parsefn token indices arguments end
      val entries =
        [("=", cpc_equality_parsefn), ("distinct", bounded_distinct),
         ("str.++", cpc_concat_parsefn "smtstr_concat"),
         ("re.++", cpc_concat_parsefn "reglan_concat"),
         ("re.union", cpc_concat_parsefn "reglan_union"),
         ("re.inter", cpc_concat_parsefn "reglan_inter"),
         ("to_int", cpc_intreal_parsefn), ("to_real", cpc_intreal_parsefn),
         ("int.pow2", cpc_intreal_parsefn)]
      val totals = List.map (fn name => (name, cpc_arith_total_parsefn))
        ["div_total", "mod_total", "/_total", "@int_div_by_zero",
         "@mod_by_zero", "@div_by_zero", "**_total"]
      val backend = #backend (#reader terms)
      val private_symbol = graph_private_allocator terms
      val _ = install_graph_qualifications backend
        (#add_recipe_parser terms) (#add_constructor_parser terms)
        private_symbol
      val limits = #recipe_limits options
      val _ = install_graph_indexed backend limits terms
      val width_limit = #index_limit limits
      fun admitted term =
        case SmtReplayImport.raw_size_with_policy width_limit term of
          SOME _ => term
        | NONE => raise ERR "graph_index" "expanded private literal index"
      fun natural term =
        let val value = numeral_of_term "graph private index" (admitted term)
        in if policy_reader_width width_limit value then value else
          raise ERR "graph_index" "private numeric index exceeds contract" end
      fun index (P.SourceIndex (node,_)) = index (P.ValueIndex (node,"("))
        | index (P.LexicalIndex pair) = index (P.ValueIndex pair)
        | index (P.LiteralIndex term) = natural term
        | index (P.ValueIndex (node, _)) = value_index natural node
        | index _ = raise ERR "graph_index" "nonliteral private index"
      fun marker frame token indices args =
        let
          val ty = case (token, indices, args) of
              ("Int", [], []) => intSyntax.int_ty
            | ("BitVec", [bits], []) =>
                wordsSyntax.mk_word_type (fcpLib.index_type (index bits))
            | ("FloatingPoint", [eb, sb], []) =>
                SmtLib_Theories.smtfp_type (index eb, index sb)
            | ("->", [], _ :: _ :: _) =>
                let val (domains, range) = Lib.front_last args in
                  boolSyntax.list_mk_fun
                    (List.map (B.type_of backend) domains,
                     B.type_of backend range) end
            | _ => raise ERR "cpc_sort_marker_parsefn"
                ("malformed CPC sort marker " ^ token)
        in graph_private_atom backend frame (private_symbol frame
          {kind = "@cpc." ^ token, hol_type = ty,
           source = NONE, stable = true}) end
      fun private_fp frame token indices args =
        if not (null indices) then raise ERR "cpc_fp_private_parsefn"
          "unexpected indices"
        else case args of
            [sort_marker] => graph_private_atom backend frame
              (private_symbol frame
                {kind = token, hol_type = B.type_of
                   backend sort_marker, source = NONE, stable = false})
          | [sort_marker, source] => graph_private_atom backend frame
              (private_symbol frame
                {kind = token, hol_type = B.type_of
                   backend sort_marker, source = SOME source, stable = true})
          | _ => raise ERR "cpc_fp_private_parsefn"
              (token ^ " expects a sort marker and at most one " ^
               "floating-point operand")
      fun private_total frame token indices args =
        if not (null indices) orelse null args then
          raise ERR "cpc_fp_total_parsefn" "malformed private FP operator"
        else
          let val types = List.map (B.type_of backend) args
              val ty = boolSyntax.list_mk_fun (types, hd types)
              val head = private_symbol frame
                {kind = token, hol_type = ty, source = NONE, stable = true}
              val originals = case B.constructor_sources backend of
                  SOME {arguments,...} => arguments
                | NONE => List.map (B.source_syntax backend frame) args
              val source = List.foldl (fn (arg,head) =>
                C.application (head,arg))
                (C.private_atom (graph_private_descriptor backend head))
                originals
              val _ = B.note_constructor_source backend source
          in List.foldl (fn (arg, head) =>
            B.application backend frame (head, arg))
            (graph_private_reference backend frame head) args end
      fun arithmetic frame token indices args =
        if null indices andalso null args andalso
            List.exists (Lib.equal token)
              ["@int_div_by_zero", "@mod_by_zero", "@div_by_zero"] then
          graph_private_atom backend frame (private_symbol frame
            {kind = token, hol_type = if token = "@div_by_zero"
               then realSyntax.real_ty else intSyntax.int_ty,
             source = NONE, stable = true})
        else SmtLib_GraphTheories.recipe_parsefn_with_policy backend limits
          cpc_arith_total_parsefn frame token indices args
      val _ = List.app (#add_recipe_parser terms) entries
      val _ = List.app (fn (name, _) =>
        (#add_constructor_parser terms) (name, arithmetic)) totals
      val _ = List.app (fn name =>
        (#add_constructor_parser terms) (name, marker))
        ["Int", "BitVec", "FloatingPoint", "->"]
      val _ = List.app (fn name =>
        (#add_constructor_parser terms) (name, private_fp))
        ["@fp.SIGN", "@fp.EXPONENT", "@fp.SIGNIFICAND", "@fp.ZERO",
         "@fp.NAN", "@fp.INF"]
      val _ = List.app (fn name =>
        (#add_constructor_parser terms) (name, private_total))
        ["fp.max_total", "fp.min_total"]
      val _ = List.app (#add_recipe_parser terms)
        [("@fp.RMBITBLAST", cpc_fp_rounding_parsefn),
         ("bvite", cpc_bvite_parsefn), ("bvsltbv", cpc_bv_parsefn),
         ("bvultbv", cpc_bv_parsefn), ("concat", cpc_bv_parsefn),
         ("@bvsize", cpc_bv_parsefn)]
      val _ = install_graph_cpc_constructors backend limits terms
        private_symbol
    in () end


  fun install_graph_recipes_with_policy
      (options:F.policy_options) (terms:F.session) =
    let val graph = #graph options
        val width_limit = #index_limit (#recipe_limits options)
        fun value_index natural node =
          case G.unfolded_nodes_with_policy graph
              G.RawNodes width_limit node of
              SOME size =>
                if SmtReplayResourcePolicy.allows width_limit size then
                  natural (G.representative graph node)
                else raise ERR "graph_index" "expanded private index operand"
            | NONE => raise ERR "graph_index" "opaque private index operand"
    in install_graph_recipes_with_policy_for_backend value_index options terms
    end

  fun graph_term_reader_with_version_with_policy options version instream =
    let
      val version = resolve_version version
      val baseline = with_cpc_literals
        (SmtLib_Logics.parsedicts_of_logic "ALL")
      val reserved_names = Redblackmap.foldl
        (fn (key, _, keys) => key :: keys)
        (Redblackmap.foldl (fn (key, _, keys) => key :: keys)
          ["_", "!", "as", "let", "forall", "exists", "lambda", "match",
           "par", "declare-const", "declare-fun", "declare-sort",
           "declare-datatype", "declare-datatypes", "define",
           "assume", "assume-push", "step", "step-pop"] (#1 baseline))
        (#2 baseline)
      val terms = SmtLib_GraphFrontend.create_session_with_policy options
        {solver = "cvc5", version = version,
         policy = SmtLib_GraphFrontend.CPC, reserved_names = reserved_names}
        (SmtLib_Parser.make_cpc_proof_stream_tokenizer instream)
      val _ = install_graph_recipes_with_policy options terms
      val _ = (#add_literal_parser terms)
        (fn token => cpc_literal_parsefn token [] [])
    in #reader terms end
  fun graph_term_reader_with_policy options instream =
    graph_term_reader_with_version_with_policy options unknown_cvc_version instream

  fun graph_policy_description version =
    let
      val baseline = with_cpc_literals
        (SmtLib_Logics.parsedicts_of_logic "ALL")
      val syntax_names =
        ["_", "!", "as", "let", "forall", "exists", "lambda", "match",
         "par", "declare-const", "declare-fun", "declare-sort",
         "declare-datatype", "declare-datatypes", "define", "assume",
         "assume-push", "step", "step-pop"]
      val reserved_names = Redblackmap.foldl
        (fn (key, _, keys) => key :: keys)
        (Redblackmap.foldl (fn (key, _, keys) => key :: keys)
          syntax_names (#1 baseline)) (#2 baseline)
    in {solver="cvc5",version=version,policy=F.CPC,
      reserved_names=reserved_names} end

  fun graph_command_reader_for_backend_with_policy
      install_recipes make_session (options:'a F.constructed_policy_options)
      (declaration_dicts:dicts) requested_version make_token
      : 'a constructed_graph_command_reader =
    let
      val version = resolve_version requested_version
      val description = graph_policy_description version
      val token = make_token ()
      val terms = make_session options description token
      val _ = install_recipes options terms
      val indexed = cpc_indexed_identifier (fn name =>
        let val namespace = (#namespace terms) () in
          set_member (#proof_terms namespace) name orelse
          set_member (#source_terms namespace) name orelse
          Option.isSome (Redblackmap.peek (#2 declaration_dicts, name))
        end)
      val (graph_read_definition_list, define_list) = graph_definition_lists
        indexed (#lookup_list terms) (#symbol_key terms) (#define_list terms)
      val _ = (#add_literal_parser terms)
        (fn token => cpc_literal_parsefn token [] [])
      val locations = graph_locations (#backend (#reader terms))
        (#symbol_key terms)
      val known = ref (HOLset.empty String.compare)
      val snapshots = ref ([] : string HOLset.set list)
      val seen = ref
        (Redblackmap.mkDict String.compare :
          (string, string list) Redblackmap.dict)
      val pending = ref (NONE : (string * string) option)
      val ended = ref false
      val _ = Library.expect_token "(" (token ())
      fun error message = raise ERR "graph_commands" message
      fun tokens raw action =
        let val remaining = ref (raw_tokens raw)
            fun next () = case !remaining of
                first :: rest => (remaining := rest; first)
              | [] => error "buffered term ended unexpectedly"
            val result = action next
            val _ = if null (!remaining) then () else
              error "buffered term has trailing syntax"
        in result end
      fun sort raw = graph_parse_sort (#backend (#reader terms)) tokens
        (#parse_sort terms) (#sort_dictionary terms) raw
      fun graph_application raw = case raw of
          RawList (RawAtom "_" :: RawAtom name :: indices) =>
            if name = "BitVec" orelse name = "FloatingPoint" then
              let
                val arity = if name = "BitVec" then 1 else 2
                val _ = if List.length indices = arity then () else
                  error ("malformed CPC indexed sort marker " ^ name)
                (* These are actual indexed sort markers, not the CPC
                   higher-order application form. The installed marker
                   recipe admits every literal/value index and its width
                   before constructing the authoritative HOL type. *)
              in RawList (RawAtom "_" :: RawAtom name ::
                List.map graph_application indices) end
            else if indexed name then raw
            else RawList (RawAtom "@" ::
              List.map graph_application (RawAtom name :: indices))
        | RawList (RawAtom "_" :: arguments) =>
            RawList (RawAtom "@" :: List.map graph_application arguments)
        | RawList ((head as RawList (RawAtom "_" :: _)) :: arguments) =>
            RawList (head :: List.map graph_application arguments)
        | RawList entries => RawList (List.map graph_application entries)
        | RawAtom _ => raw
      fun parse raw : 'a F.constructed_term = (#locate locations) (
        case raw of
          RawList [RawAtom "@var", RawAtom name, ty] =>
            (#private_variable terms) (cpc_var_name name, sort ty)
        | _ => tokens (graph_application (normalize_cpc_testers indexed raw))
            (#parse_from terms))
      fun raw_list context raw = case raw of RawList entries => entries
        | _ => error (context ^ " must be parenthesized")
      fun atom context raw = case raw of RawAtom text => text
        | _ => error (context ^ " must be atomic")
      fun id text = cpc_id_key "graph_commands" "command ID" text
      fun fresh name = ensure_fresh_id "graph_commands" name known
      fun add name = known := HOLset.add (!known, name)
      fun close name = case !snapshots of
          previous :: rest => (known := previous; snapshots := rest; add name)
        | [] => error ("step-pop without assume-push in CPC step " ^ name)
      fun declarations kind =
        let val name = token ()
            val domain = if kind = "declare-fun" then
                List.map sort (raw_list "function domain"
                  (read_raw_term token))
              else []
            val range = sort (read_raw_term token)
            val _ = Library.expect_token ")" (token ())
        in (#declare terms) (name, boolSyntax.list_mk_fun (domain, range)) end
      fun datatype_declaration kind =
        let
          val namespace = (#namespace terms) ()
          val symbol_key = #symbol_key terms
          fun binding raw = case raw of
              RawList [RawAtom name, RawAtom arity] =>
                let val (key, text) = datatype_symbol_using symbol_key
                      "declare-datatypes" "datatype sort" name
                in (key, text, datatype_arity "declare-datatypes" text arity)
                end
            | _ => error "malformed datatype binding"
          val declarations = if kind = "declare-datatype" then
              let
                val name = token ()
                val (key, text) = datatype_symbol_using symbol_key
                  kind "datatype sort" name
                val body = read_raw_term token
                val arity = case body of
                    RawList [RawAtom "par", RawList params, RawList _] =>
                      List.length params
                  | _ => 0
              in [parse_datatype_body_using symbol_key
                kind key text arity body] end
            else
              let val bindings = List.map binding
                    (raw_list "datatype bindings" (read_raw_term token))
                  val bodies = raw_list "datatype bodies"
                    (read_raw_term token)
                  val _ = if List.length bindings = List.length bodies then
                    () else error "datatype binding/body count mismatch"
              in ListPair.mapEq (fn ((key, name, arity), body) =>
                parse_datatype_body_using symbol_key kind key name arity body)
                (bindings, bodies) end
          val _ = Library.expect_token ")" (token ())
        in validate_datatype_declarations_using namespace
          (ref ((#sort_dictionary terms) (), #2 declaration_dicts))
          declarations end
      fun define_term pair =
        ((#define terms) pair;(#define locations) pair)
      fun define () =
        let
          val name = graph_definition_name ((#namespace terms) ())
            (#2 declaration_dicts) (#symbol_key terms) (token ())
          val start = token ()
          val first = if start = "(" then
              (Library.expect_token ")" (token ()); token ()) else start
          fun ordinary prefix =
            let
              val raw = read_raw_term
                (Library.undo_look_ahead prefix token)
              val _ = Library.expect_token ")" (token ())
            in case raw of
                RawList [RawAtom "@var", RawAtom variable, ty] =>
                  ignore ((#define_variable terms)
                    (name, cpc_var_name variable, sort ty))
              | RawList [RawAtom "@purify", payload] =>
                  define_term (name, parse payload)
              | _ => define_term (name, parse raw)
            end
        in
          if first = "@list" then
            (skip_sexp token; (#define_opaque terms) name)
          else if first = "(" then
            let val head = token () in
              if head = "@list" then
                let
                  val entries = graph_read_definition_list token
                    (#parse_from terms) (#parse_sort terms)
                    (#private_variable terms) (#locate locations)
                  val _ = define_list (name, entries)
                in Library.expect_token ")" (token ()) end
              else ordinary [first, head]
            end
          else ordinary [first]
        end
      val argument = graph_object_argument parse parse (#lookup_list terms)
      fun index raw =
        let val text = atom "CPC index" raw
        in case Int.fromString text of
            SOME index => if index >= 0 then GraphIndex index else
              error "negative CPC index"
          | NONE => error "non-numeral CPC index" end
      fun rule_arguments name rule_name (rule : proof_rule) raws =
        if #replay_handler rule = "and_elim" orelse
           #replay_handler rule = "not_or_elim" then
          (case raws of [raw] => [index raw]
           | _ => error "elimination rule expects one index")
        else if #name rule = "cnf_and_pos" orelse
                #name rule = "cnf_or_neg" then
          (case raws of [object, number] =>
              [GraphTerm (parse object), index number]
           | _ => error "CNF rule expects an object and index")
        else if #name rule = "resolution" then
          (case raws of polarity :: pivot :: hints =>
              GraphTerm (parse polarity) :: GraphTerm (parse pivot) ::
                List.map GraphHint hints
           | [] => []
           | _ => error "resolution requires polarity and pivot")
        else if #replay_handler rule = "resolution" then
          (case raws of [] => []
           | target :: rest => GraphTerm (parse target) ::
               List.map argument rest)
        else if #replay_handler rule = "exists_elim" orelse
                #replay_handler rule = "quant_rewrite" then
          List.map argument raws
        else if #replay_handler rule = "rare_inventory" orelse
                #name rule = "arith-mod-over-mod" orelse
                #name rule = "arith-mod-over-mod-mult" then
          List.map (graph_structured_argument (#backend (#reader terms))
            name rule_name parse (#lookup_list terms)) raws
        else graph_validate_set_sort_metadata
          (#backend (#reader terms)) name rule_name
          (graph_step_arguments (#backend (#reader terms)) name rule_name
            parse sort (#lookup_list terms) raws)
      fun step kind =
        let
          val consumed = ref ([] : string list)
          fun next () = let val text = token () in
            consumed := text :: !consumed; text end
          val name = id (next ())
          val _ = fresh name
          val first = next ()
          val conclusion = if first = ":rule" then NONE else
            SOME (read_raw_term (Library.undo_look_ahead [first] next))
          val _ = if first = ":rule" then () else
            Library.expect_token ":rule" (next ())
          val rule_name = next ()
          val rule = case lookup_rule version rule_name of
              SOME rule => rule
            | NONE => raise ERR "graph_step"
                (registry_lookup_failure version rule_name)
          (* Supported conclusions precede all attributes. Unsupported
             inventory entries must remain entirely syntax-only. *)
          val eager = not (Option.isSome
            (rare_unsupported_diagnostic rule_name))
          val parsed_conclusion = if eager then
              SOME (Option.map parse conclusion) else NONE
          val parsed_args = ref NONE
          fun attrs saw_premises saw_args premises args =
            case next () of
              ")" => (premises, args)
            | ":premises" =>
                if saw_premises then error "duplicate :premises" else
                  let val premises = List.map
                        (cpc_id_key "graph_step" "premise ID" o
                          atom "premise ID")
                        (graph_premise_list (read_raw_term next))
                      val _ = List.app
                        (require_known_premise name known) premises
                  in attrs true saw_args premises args end
            | ":args" => if saw_args then error "duplicate :args" else
                let
                  val raws =
                    if eager andalso (graph_ordinary_rule_arguments rule
                        orelse graph_structured_rule_arguments rule) then
                      let
                        val backend = #backend (#reader terms)
                        val (raws, args) =
                          if graph_structured_rule_arguments rule then
                            graph_read_structured_step_arguments next backend
                              name rule_name parse (#lookup_list terms)
                          else graph_read_step_arguments next
                            (graph_step_argument_at backend name rule_name
                              parse sort (#lookup_list terms))
                        val _ = parsed_args := SOME
                          (graph_validate_set_sort_metadata backend name
                            rule_name args)
                      in raws end
                    else
                      let
                        val raws = raw_list "arguments" (read_raw_term next)
                        val _ = if eager then parsed_args :=
                          SOME (rule_arguments name rule_name rule raws)
                          else ()
                      in raws end
                in attrs saw_premises true premises raws end
            | attribute => error ("unknown CPC step attribute " ^ attribute)
          val (premises, args) = attrs false false [] []
          val _ = register_command_signature seen kind name
            (List.rev (!consumed))
          val _ = if kind = "step-pop" then close name else add name
        in case rare_unsupported_diagnostic rule_name of
            SOME diagnostic =>
              let fun raw_error detail = raise ERR "parse_step"
                    ("malformed raw term in unsupported CPC step " ^ name ^
                     ": " ^ detail)
                  val _ = Option.app (validate_raw_term raw_error) conclusion
                  val _ = List.app (validate_raw_term raw_error) args
                  val _ = if Option.isSome (!pending) then () else
                    pending := SOME (rule_name, diagnostic)
              in NONE end
          | NONE => SOME (GraphStep
              {step = {id = name, rule = rule, premises = premises,
                 conclusion = (case parsed_conclusion of
                     SOME result => result
                   | NONE => Option.map parse conclusion),
                 args = (case !parsed_args of SOME result => result
                   | NONE => rule_arguments name rule_name rule args),
                 raw_conclusion = conclusion, raw_args = args},
               pop = kind = "step-pop"})
        end
      fun finish () =
        let val _ = if null (!snapshots) then () else
              error "unclosed assume-push scope at end of CPC proof wrapper"
            val trailing = SOME (token ()) handle P.CPCProofEOF => NONE
            val _ = case trailing of NONE => () | SOME text =>
              error ("second CPC proof wrapper or trailing token '" ^
                P.proof_symbol_text text ^ "'")
            val _ = ended := true
        in case !pending of NONE => NONE
          | SOME (rule, diagnostic) => raise ERR rule diagnostic end
      fun next () = if !ended then NONE else
        case token () of
          ")" => finish ()
        | "(" =>
            (case token () of
               "declare-const" => (declarations "declare-const"; next ())
             | "declare-fun" => (declarations "declare-fun"; next ())
             | "declare-sort" =>
                 let val name = token ()
                     val arity = datatype_arity "declare-sort" name (token ())
                     val _ = Library.expect_token ")" (token ())
                 in (#declare_sort terms) (name, arity); next () end
             | "declare-datatype" =>
                 (datatype_declaration "declare-datatype"; next ())
             | "declare-datatypes" =>
                 (datatype_declaration "declare-datatypes"; next ())
             | "define" => (define (); next ())
             | "assume" => assumption false
             | "assume-push" => assumption true
             | "step" => (case step "step" of
                 NONE => next () | command => command)
             | "step-pop" => (case step "step-pop" of
                 NONE => next () | command => command)
             | command => error ("unknown CPC construct " ^ command))
        | text => error ("unexpected CPC token '" ^
            P.proof_symbol_text text ^ "'")
      and assumption push =
        let val name = id (token ())
            val _ = fresh name
            val value = parse (read_raw_term token)
            val _ = Library.expect_token ")" (token ())
            val _ = if push then snapshots := !known :: !snapshots else ()
            val _ = add name
        in SOME (if push then GraphAssumePush (name, value)
          else GraphAssume (name, value)) end
      fun checked_next () = next () handle P.CPCProofEOF =>
        raise ERR "parse_stream_with_version"
          "unexpected end of CPC proof wrapper"
    in {next = checked_next, terms = terms, cvc_version = version} end


  fun graph_command_reader_with_factory_with_policy_token_factory
      make_session (options:F.policy_options) declaration_dicts
      requested_version make_token : graph_command_reader =
    graph_command_reader_for_backend_with_policy
      install_graph_recipes_with_policy make_session options declaration_dicts
      requested_version make_token

  fun graph_command_reader_with_factory_with_policy make_session
      options declaration_dicts version instream =
    graph_command_reader_with_factory_with_policy_token_factory
      make_session options declaration_dicts version
      (fn () => P.make_cpc_proof_stream_tokenizer instream)

  fun graph_command_reader_with_version_with_policy options declaration_dicts version input =
    graph_command_reader_with_factory_with_policy F.create_session_with_policy
      options declaration_dicts version input

  fun graph_configured_command_reader_with_version_with_policy
      (configured : F.policy_configured_options) declaration_dicts version input =
    graph_command_reader_with_factory_with_policy
      (fn _ => F.create_configured_session_with_policy configured)
      (#base configured) declaration_dicts version input

  fun parse_graph_packet_with_version_with_policy options declaration_dicts version input =
    let val reader = graph_command_reader_with_version_with_policy
          options declaration_dicts version input
    in packet version reader end

  fun parse_graph_configured_packet_with_version_with_policy configured declaration_dicts
      version input =
    packet version (graph_configured_command_reader_with_version_with_policy
      configured declaration_dicts version input)

  fun parse_graph_translation_packet_with_version_with_policy_token_factory
      options translation version make_token =
    let
      val configured = SmtLib_GraphTranslation.configured_options_with_policy
        options translation
      val make_session = fn _ =>
        SmtLib_GraphTranslation.create_session_with_policy options translation
      val dicts = SmtLib.parser_dicts_for_solver_translation "cvc5" translation
    in packet version
      (graph_command_reader_with_factory_with_policy_token_factory
        make_session (#base configured) dicts version make_token) end

  fun parse_graph_translation_packet_with_version_with_policy options translation
      version input =
    parse_graph_translation_packet_with_version_with_policy_token_factory
      options translation version
      (fn () => P.make_cpc_proof_stream_tokenizer input)

  fun parse_graph_translation_packet_with_version_with_policy_from_input
      options translation version input =
    parse_graph_translation_packet_with_version_with_policy_token_factory
      options translation version
      (fn () => P.make_cpc_proof_tokenizer_from_input input)

  fun parse_graph_stream_with_version_with_policy options declaration_dicts version input
      : graph_proof =
    SmtLib_GraphProof.proof
      (parse_graph_packet_with_version_with_policy options declaration_dicts version input)

end

end
