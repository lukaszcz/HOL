structure SmtFpGraph :> SmtFpGraph =
struct
  open HolKernel

  exception Declined of string

  type descriptor =
    {value : term, sign : term, exponent : term, fraction : term,
     representation : thm}

  fun head_name term =
    let
      val (head, _) = boolSyntax.strip_comb term
    in
      if Term.is_const head then
        let val {Thy, Name, ...} = Term.dest_thy_const head
        in SOME (Thy, Name) end
      else NONE
    end

  val fp_type_id = #Tyop (Type.dest_thy_typeid ``:(1,2) smtfp``)
  val rounding_type_id = #Tyop (Type.dest_thy_typeid ``:rounding``)

  fun is_fp_type ty =
    not (Type.is_vartype ty) andalso
    KernelSig.id_compare
      (#Tyop (Type.dest_thy_typeid ty), fp_type_id) = EQUAL

  fun is_rounding_type ty =
    not (Type.is_vartype ty) andalso
    KernelSig.id_compare
      (#Tyop (Type.dest_thy_typeid ty), rounding_type_id) = EQUAL

  val unsupported_producers =
    ["smtfp_mul", "smtfp_div", "smtfp_fma",
     "smtfp_sqrt", "smtfp_rem", "smtfp_round_to_integral", "smtfp_min",
     "smtfp_max", "smtfp_to_fp", "smtfp_from_real", "smtfp_from_sbv",
     "smtfp_from_ubv"]

  fun registered_name names term =
    let
      val (head, _) = boolSyntax.strip_comb term
      val actual = #Name (Term.dest_thy_constid head)
      fun matches name = KernelSig.id_compare
        (actual, #Name (Term.dest_thy_constid
          (Term.prim_mk_const {Thy = "smtfloat", Name = name}))) = EQUAL
    in List.find matches names end

  fun known_unsupported term =
    case head_name term of
      SOME ("smtfloat", name) => List.exists (fn saved => name = saved)
        unsupported_producers
    | _ => false

  val supported_producers =
    ["smtfp_bits", "smtfp_abs", "smtfp_neg", "smtfp_pzero",
     "smtfp_nzero", "smtfp_pinf", "smtfp_ninf", "smtfp_nan",
     "smtfp_add", "smtfp_sub"]

  fun supported_producer term =
    let val (head, _) = boolSyntax.strip_comb term
    in Term.is_const head andalso
      Option.isSome (registered_name supported_producers term)
    end

  fun semantic_fp_producer term =
    is_fp_type (Term.type_of term) andalso
    (case head_name term of
       SOME ("smtfloat", _) => true
     | SOME ("bool", "COND") => true
     | _ => false)

  fun bits_fields term =
    case boolSyntax.strip_comb term of
      (head, [sign, exponent, fraction]) =>
        (case head_name head of
           SOME ("smtfloat", "smtfp_bits") => (sign, exponent, fraction)
         | _ => raise Declined "representation is not smtfp_bits")
    | _ => raise Declined "representation is not ternary smtfp_bits"

  fun placeholder descriptor =
    let
      val represented = boolSyntax.rhs (Thm.concl (#representation descriptor))
      val (head, _) = boolSyntax.strip_comb represented
      val fields = [#sign descriptor, #exponent descriptor,
        #fraction descriptor]
      val variables = List.map (Term.genvar o Term.type_of) fields
      val bits = List.foldl
        (fn (field, function) => Term.mk_comb (function, field))
        head variables
    in
      (bits, ListPair.mapEq (fn (variable, field) => variable |-> field)
        (variables, fields))
    end

  fun admit_schema admission theorem =
    let
      val conclusion = Thm.concl theorem
      fun inspect node = if Term.is_abs node then
          #admit_abstraction admission "fp-graph-stage1-schema" node
        else ignore (#intern admission (Term.type_of node))
      val _ = SmtResource.dag_nodes_up_to_with_inspector inspect
        SmtResource.max_bv_replay_term_nodes conclusion
    in
      SmtResource.check_bitblast_goal "fp-graph-stage1-schema" conclusion
    end

  fun instantiate_law admission theorem placeholder_term actual_term
      substitution =
    let
      val pattern = boolSyntax.lhs (Thm.concl theorem)
      val instantiated = Drule.INST_TY_TERM
        (Term.match_term pattern placeholder_term) theorem
      val _ = admit_schema admission instantiated
      val inserted = Thm.INST substitution instantiated
    in Thm.TRANS (Thm.REFL actual_term) inserted end

  fun expose_leaf term =
    let
      val schema = smtfloatTheory.smtfp_bits_rep
      val pattern = boolSyntax.rhs (Thm.concl schema)
      val theorem = Thm.SYM
        (Drule.INST_TY_TERM (Term.match_term pattern term) schema)
    in Thm.TRANS (Thm.REFL term) theorem end

  fun prepare_constant_schema law nan =
    let
      val (premise, equation) = boolSyntax.dest_imp (Thm.concl law)
      val (_, bits) = boolSyntax.dest_eq equation
      val (sign, exponent, fraction) =
        case boolSyntax.strip_comb bits of
          (_, [sign, exponent, fraction]) => (sign, exponent, fraction)
        | _ => raise Declined "malformed smtfp_nan bits"
      fun conjuncts tm = if boolSyntax.is_conj tm then
          let val (left, right) = boolSyntax.dest_conj tm
          in conjuncts left @ conjuncts right end
        else [tm]
      fun equality_for variable =
        List.find
          (fn tm => boolSyntax.is_eq tm andalso
            Portable.pointer_eq (boolSyntax.lhs tm, variable))
          (conjuncts premise)
      fun word_number number target = wordsSyntax.mk_n2w
        (numSyntax.mk_numeral (Arbnum.fromInt number),
         wordsSyntax.dim_of target)
      fun instantiate_like source target = Term.inst
        (Type.match_type (Term.type_of source) (Term.type_of target)) source
      val maximum = case equality_for exponent of
          SOME equality => boolSyntax.rhs equality
        | NONE => word_number 0 exponent
      fun assigned variable =
        case equality_for variable of
          SOME equality => boolSyntax.rhs equality
        | NONE => if Portable.pointer_eq (variable, fraction) andalso nan then
            instantiate_like maximum fraction
          else word_number 0 variable
      val instantiated = Thm.INST
        [sign |-> assigned sign, exponent |-> assigned exponent,
         fraction |-> assigned fraction] law
      val (premise, _) = boolSyntax.dest_imp (Thm.concl instantiated)
      val premise_theorem = simpLib.SIMP_PROVE (bossLib.srw_ss ())
        [wordsTheory.word_T_not_zero] premise
    in Thm.MP instantiated premise_theorem end

  fun constant_representation admission schema term =
    let
      val pattern = boolSyntax.lhs (Thm.concl schema)
      val specialized = Drule.INST_TY_TERM
        (Term.match_term pattern term) schema
      val _ = admit_schema admission specialized
    in Thm.TRANS (Thm.REFL term) specialized end

  val constant_laws =
    [("smtfp_pzero",
      prepare_constant_schema smtfloatTheory.smtfp_pzero_bits false),
     ("smtfp_nzero",
      prepare_constant_schema smtfloatTheory.smtfp_nzero_bits false),
     ("smtfp_pinf",
      prepare_constant_schema smtfloatTheory.smtfp_pinf_bits false),
     ("smtfp_ninf",
      prepare_constant_schema smtfloatTheory.smtfp_ninf_bits false),
     ("smtfp_nan",
      prepare_constant_schema smtfloatTheory.smtfp_nan_bits true)]

  fun constant_law name =
    Option.map Lib.snd
      (List.find (fn (saved, _) => name = saved) constant_laws)

  fun preflight admission term =
    let
      val unsupported = ref false
      fun inspect node =
        (if Term.is_abs node then
           #admit_abstraction admission "fp-graph-stage1" node
         else ignore (#intern admission (Term.type_of node));
         if semantic_fp_producer node andalso
            not (supported_producer node) then unsupported := true else ())
      val _ = SmtResource.dag_nodes_up_to_with_inspector inspect
        SmtResource.max_bv_replay_term_nodes term
      val _ = SmtResource.check_bitblast_goal "fp-graph-stage1" term
      val _ = if !unsupported then
          raise Declined "unsupported floating-point producer"
        else ()
    in () end

  fun full_named thy name arity term =
    let val (head, arguments) = boolSyntax.strip_comb term
    in
      Term.is_const head andalso List.length arguments = arity andalso
      let val id = Term.dest_thy_const head
      in #Thy id = thy andalso #Name id = name end
    end

  fun helper_definition term =
    let
      val (head, arguments) = boolSyntax.strip_comb term
      val candidate = if not (Term.is_const head) then NONE else
        case (#Thy (Term.dest_thy_const head),
              #Name (Term.dest_thy_const head)) of
          ("smtfloat", "smtfp_nan_pattern") =>
            SOME (smtfloatTheory.smtfp_nan_pattern_def, 2)
        | ("smtfloatReplayAddSubWord", "smtfp_word_addsub") => SOME
            (smtfloatReplayAddSubWordTheory.smtfp_word_addsub_def, 10)
        | ("smtfloatReplayAddSubWord", "smtfp_word_addsub_fields") => SOME
            (smtfloatReplayAddSubWordTheory.smtfp_word_addsub_fields_def, 10)
        | ("smtfloatReplayAddSubWord", "smtfp_word_addsub_trace") => SOME
            (smtfloatReplayAddSubWordTheory.smtfp_word_addsub_trace_def, 9)
        | ("smtfloatReplayAddSubWord", "smtfp_word_addsub_exp") => SOME
            (smtfloatReplayAddSubWordTheory.smtfp_word_addsub_exp_def, 1)
        | ("smtfloatReplayAddSubWord", "smtfp_word_addsub_sig") => SOME
            (smtfloatReplayAddSubWordTheory.smtfp_word_addsub_sig_def, 2)
        | ("smtfloatReplayAddSubWord", "smtfp_word_retained_scale") => SOME
            (smtfloatReplayAddSubWordTheory.smtfp_word_retained_scale_def, 2)
        | ("smtfloatReplayAddSubWord", "smtfp_word_bounded_align") => SOME
            (smtfloatReplayAddSubWordTheory.smtfp_word_bounded_align_def, 3)
        | ("smtfloatReplayAddSubWord", "smtfp_word_pair_trace") => SOME
            (smtfloatReplayAddSubWordTheory.smtfp_word_pair_trace_def, 5)
        | ("smtfloatReplayAddSubWord", "smtfp_word_addsub_zero_sign") => SOME
            (smtfloatReplayAddSubWordTheory.smtfp_word_addsub_zero_sign_def, 8)
        | ("smtfloatReplayEncodeWord", "smtfp_word_encode_fields") => SOME
            (smtfloatReplayEncodeWordTheory.smtfp_word_encode_fields_def, 5)
        | ("smtfloatReplayEncodeWord", "smtfp_word_encode_exponent") => SOME
            (smtfloatReplayEncodeWordTheory.smtfp_word_encode_exponent_def, 3)
        | ("smtfloatReplayEncodeWord", "smtfp_word_encode_qrd") => SOME
            (smtfloatReplayEncodeWordTheory.smtfp_word_encode_qrd_def, 3)
        | ("smtfloatReplayEncodeWord", "smtfp_word_round") => SOME
            (smtfloatReplayEncodeWordTheory.smtfp_word_round_def, 5)
        | ("smtfloatReplayEncodeWord", "smtfp_word_round_up") => SOME
            (smtfloatReplayEncodeWordTheory.smtfp_word_round_up_def, 5)
        | ("smtfloatReplayEncodeWord", "smtfp_word_pack_fields") => SOME
            (smtfloatReplayEncodeWordTheory.smtfp_word_pack_fields_def, 5)
        | ("smtfloatReplayEncodeWord", "smtfp_word_overflow_fields") => SOME
            (smtfloatReplayEncodeWordTheory.smtfp_word_overflow_fields_def, 3)
        | ("smtfloatReplayWord", "smtfp_cvc_rounding_bits") => SOME
            (smtfloatReplayWordTheory.smtfp_cvc_rounding_bits_def, 1)
        | ("smtfloatReplayWord", "smtfp_word_lsr_bv") => SOME
            (smtfloatReplayWordTheory.smtfp_word_lsr_bv_def, 2)
        | ("smtfloatReplayWord", "smtfp_word_lsl_bv") => SOME
            (smtfloatReplayWordTheory.smtfp_word_lsl_bv_def, 2)
        | ("smtfloatReplayWord", "smtfp_word_jam_bv") => SOME
            (smtfloatReplayWordTheory.smtfp_word_jam_bv_def, 2)
        | ("smtfloatReplayWord", "smtfp_word_priority") => SOME
            (smtfloatReplayWordTheory.smtfp_word_priority_def, 2)
        | ("smtfloatReplayWord", "smtfp_cvc_unpacked_exponent") => SOME
            (smtfloatReplayWordTheory.smtfp_cvc_unpacked_exponent_def, 4)
        | ("smtfloatReplayWord", "smtfp_cvc_unpacked_significand") => SOME
            (smtfloatReplayWordTheory.smtfp_cvc_unpacked_significand_def, 4)
        | _ => NONE
    in
      case candidate of
        SOME (theorem, arity) =>
          if List.length arguments = arity then SOME theorem else NONE
      | NONE => NONE
    end

  fun pointer_peek entries term =
    case List.find
        (fn (saved, _) => Portable.pointer_eq (term, saved)) entries of
      NONE => NONE
    | SOME (_, value) => SOME value

  fun rebuild head theorems = List.foldl
    (fn (argument, function) => Thm.MK_COMB (function, argument))
    (Thm.REFL head) theorems

  fun rounding_case term = Lib.can
    (Term.match_term (boolSyntax.lhs (Thm.concl
      smtfloatReplayRoundingTheory.smtfp_rounding_case_unpack))) term

  fun rounding_test term =
    if not (boolSyntax.is_eq term) then false
    else
      let val (left, right) = boolSyntax.dest_eq term
      in
        full_named "smtfloat" "smtfp_unpack_rounding" 1 left orelse
        full_named "smtfloat" "smtfp_unpack_rounding" 1 right
      end

  val rounding_test_laws = Drule.CONJUNCTS
    smtfloatReplayRoundingTheory.smtfp_unpack_rounding_tests

  val priority_laws = Drule.CONJUNCTS
    smtfloatReplayWordTheory.smtfp_word_priority_compute

  type helper_metrics =
    {visited : int, memo_hits : int, rewrites : int, output_nodes : int,
     literals : int, lets : int, betas : int, pairs : int,
     projections : int, conditionals : int, helpers : int,
     priorities : int, ordinary : int, beta_seconds : real}

  fun close_helper_graph type_admission root =
    let
      val memo = ref (Redblackmap.mkDict String.compare :
        (string, (term * (thm * bool)) list) Redblackmap.dict)
      val visited = ref 0
      val memo_hits = ref 0
      val rewrites = ref 0
      val literals = ref 0
      val lets = ref 0
      val betas = ref 0
      val pairs = ref 0
      val projections = ref 0
      val conditionals = ref 0
      val helpers = ref 0
      val priorities = ref 0
      val ordinary = ref 0
      val beta_time = ref Time.zeroTime
      val helper_schemas = ref ([] : (term * hol_type * thm) list)

      fun atomic term =
        Term.is_var term orelse Term.is_const term orelse
        numSyntax.is_numeral term orelse wordsSyntax.is_word_literal term

      fun generic_argument argument =
        if full_named "smtfloat" "smtfp_unpack_rounding" 1 argument then
          let
            val (head, raw) =
              case boolSyntax.strip_comb argument of
                (head, [raw]) => (head, raw)
              | _ => raise Declined "malformed smtfp_unpack_rounding"
            val variable = Term.genvar (Term.type_of raw)
          in Term.mk_comb (head, variable) end
        else if is_rounding_type (Term.type_of argument) then
          raise Declined
            "arithmetic helper received a non-decoder rounding value"
        else if Term.is_const argument orelse numSyntax.is_numeral argument
             orelse wordsSyntax.is_word_literal argument then argument
        else Term.genvar (Term.type_of argument)

      fun local_head term =
        let val (head, arguments) = boolSyntax.strip_comb term
        in
          (if Term.is_const head then
             let val id = Term.dest_thy_const head
             in #Thy id ^ "." ^ #Name id end
           else if Term.is_abs head then "abstraction"
           else "variable") ^ "/" ^ Int.toString (List.length arguments)
        end

      fun memo_class term =
        let
          val type_id = SmtWordGraph.primitive_type_id
            type_admission (Term.type_of term)
          fun shape 0 node = local_head node
            | shape depth node =
                let val (_, arguments) = boolSyntax.strip_comb node
                in
                  local_head node ^ "[" ^
                  String.concatWith ","
                    (List.map (shape (depth - 1)) arguments) ^ "]"
                end
        in shape 2 term ^ ":" ^ Int.toString type_id end

      fun memo_peek term =
        case Redblackmap.peek (!memo, memo_class term) of
          NONE => NONE
        | SOME entries => pointer_peek entries term

      fun head_label head =
        if Term.is_const head then
          let val id = Term.dest_thy_const head
          in #Thy id ^ "." ^ #Name id end
        else "nonconstant"

      fun save term result =
        let
          val key = memo_class term
          val entries = Option.getOpt (Redblackmap.peek (!memo, key), [])
        in
          memo := Redblackmap.insert (!memo, key, (term, result) :: entries);
          result
        end

      fun continue term prefix =
        let val right = boolSyntax.rhs (Thm.concl prefix)
        in
          if Term.aconv term right then save term (Thm.REFL term, false)
          else
            let val (tail, _) = close right
                val _ = rewrites := !rewrites + 1
            in save term (Thm.TRANS prefix tail, true) end
        end

      and close term =
        if atomic term then
          (literals := !literals + 1; (Thm.REFL term, false))
        else case memo_peek term of
          SOME result => (memo_hits := !memo_hits + 1; result)
        | NONE =>
            let
              val _ = visited := !visited + 1
              val _ = SmtWordGraph.admit_primitive_type
                type_admission (Term.type_of term)
              val (head, arguments) = boolSyntax.strip_comb term
            in
              if full_named "bool" "LET" 2 term then
                let
                  val _ = lets := !lets + 1
                  val (function, value) = case arguments of
                    [function, value] => (function, value)
                  | _ => raise Declined "malformed LET"
                  val (value_theorem, _) = close value
                  val assembled = rebuild head
                    [Thm.REFL function, value_theorem]
                  val reduced = Conv.REWR_CONV boolTheory.LET_THM
                    (boolSyntax.rhs (Thm.concl assembled))
                in continue term (Thm.TRANS assembled reduced) end
              else if Term.is_abs head andalso not (List.null arguments) then
                let
                  val _ = betas := !betas + 1
                  val (first, remaining) = case arguments of
                    first :: remaining => (first, remaining)
                  | [] => raise Declined "malformed abstraction application"
                  val (first_theorem, _) = close first
                  val applied = Thm.MK_COMB (Thm.REFL head, first_theorem)
                  val timer = Timer.startRealTimer ()
                  val beta = BETA_CONV
                    (boolSyntax.rhs (Thm.concl applied))
                  val elapsed = Timer.checkRealTimer timer
                  val reduced = Thm.TRANS applied beta
                  val _ = beta_time := Time.+ (!beta_time, elapsed)
                  val attached = List.foldl
                    (fn (argument, theorem) =>
                      Thm.MK_COMB (theorem, Thm.REFL argument))
                    reduced remaining
                in continue term attached end
              else if full_named "pair" "pair_CASE" 2 term then
                let
                  val _ = pairs := !pairs + 1
                  val (value, function) = case arguments of
                    [value, function] => (value, function)
                  | _ => raise Declined "malformed pair_CASE"
                  val (value_theorem, _) = close value
                  val assembled = rebuild head
                    [value_theorem, Thm.REFL function]
                  val reduced = Conv.REWR_CONV pairTheory.pair_CASE_def
                    (boolSyntax.rhs (Thm.concl assembled))
                in continue term (Thm.TRANS assembled reduced) end
              else if full_named "pair" "UNCURRY" 2 term then
                let
                  val _ = pairs := !pairs + 1
                  val (function, value) = case arguments of
                    [function, value] => (function, value)
                  | _ => raise Declined "malformed UNCURRY"
                  val (value_theorem, _) = close value
                  val assembled = rebuild head
                    [Thm.REFL function, value_theorem]
                  val reduced = Conv.REWR_CONV pairTheory.UNCURRY
                    (boolSyntax.rhs (Thm.concl assembled))
                in continue term (Thm.TRANS assembled reduced) end
              else if full_named "pair" "FST" 1 term orelse
                      full_named "pair" "SND" 1 term then
                let
                  val _ = projections := !projections + 1
                  val value = case arguments of
                    [value] => value
                  | _ => raise Declined "malformed pair projection"
                  val (value_theorem, _) = close value
                  val assembled = rebuild head [value_theorem]
                  val residue = boolSyntax.rhs (Thm.concl assembled)
                  val value' = List.hd
                    (Lib.snd (boolSyntax.strip_comb residue))
                  val reduced = if boolSyntax.is_cond value' then
                      Conv.REWR_CONV boolTheory.COND_RAND residue
                    else Conv.QCONV (Conv.FIRST_CONV
                      [Conv.REWR_CONV pairTheory.FST,
                       Conv.REWR_CONV pairTheory.SND,
                       Conv.ALL_CONV]) residue
                in continue term (Thm.TRANS assembled reduced) end
              else if boolSyntax.is_cond term then close_cond term
              else if rounding_case term then continue term
                (Conv.REWR_CONV
                  smtfloatReplayRoundingTheory.smtfp_rounding_case_unpack term)
              else if rounding_test term then continue term
                (Conv.QCONV (simpLib.SIMP_CONV bossLib.pure_ss
                  rounding_test_laws) term)
              else
                (case helper_definition term of
                   SOME definition => close_helper term definition
                 | NONE => close_ordinary term head arguments)
            end

      and close_cond term = SmtResource.profile_phase
        "fp-graph/close-conditional"
        (fn term => let
          val _ = conditionals := !conditionals + 1
          val (condition, yes, no) = boolSyntax.dest_cond term
          val (condition_theorem, _) = close condition
          val condition' = boolSyntax.rhs (Thm.concl condition_theorem)
          val evaluated = if HOLset.isEmpty
              (Term.FVL_dag [condition'] Term.empty_tmset) then
              Conv.QCONV bossLib.EVAL condition'
            else Thm.REFL condition'
          val guard = Thm.TRANS condition_theorem evaluated
          val guard' = boolSyntax.rhs (Thm.concl guard)
          val (head, _) = boolSyntax.strip_comb term
        in
          if Term.aconv guard' boolSyntax.T orelse
             Term.aconv guard' boolSyntax.F then
            let
              val assembled = rebuild head
                [guard, Thm.REFL yes, Thm.REFL no]
              val reduced = Conv.COND_CONV
                (boolSyntax.rhs (Thm.concl assembled))
            in continue term (Thm.TRANS assembled reduced) end
          else
            let
              val (yes_theorem, yes_changed) = close yes
              val (no_theorem, no_changed) = close no
              val result = rebuild head [guard, yes_theorem, no_theorem]
              val guard_changed = not (Term.aconv condition guard')
              val changed = guard_changed orelse yes_changed orelse no_changed
            in save term (if changed then (result, true)
              else (Thm.REFL term, false)) end
        end) term

      and close_helper term definition =
        let val (head, arguments) = boolSyntax.strip_comb term
        in
          if full_named "smtfloatReplayWord" "smtfp_word_priority" 2 term
          then
            let
              val _ = priorities := !priorities + 1
              val (count, word) = case arguments of
                [count, word] => (count, word)
              | _ => raise Declined "malformed word priority"
              val _ = if HOLset.isEmpty
                  (Term.FVL_dag [count] Term.empty_tmset) then ()
                else raise Declined "nonliteral priority count"
              val count_theorem = Conv.QCONV bossLib.EVAL count
              val assembled = rebuild head
                [count_theorem, Thm.REFL word]
              val residue = boolSyntax.rhs (Thm.concl assembled)
              val reduced = Conv.QCONV (Conv.FIRST_CONV
                (List.map Conv.REWR_CONV priority_laws)) residue
            in continue term (Thm.TRANS assembled reduced) end
          else
            let
              val _ = helpers := !helpers + 1
              val converted = List.map close arguments
              val assembled = rebuild head (List.map Lib.fst converted)
              val normalized = boolSyntax.rhs (Thm.concl assembled)
              val head_type = Term.type_of head
              val schema =
                case List.find (fn (saved_head, saved_type, saved) =>
                    Term.same_const head saved_head andalso
                    Type.compare (saved_type, head_type) = EQUAL andalso
                    Lib.can (Term.match_term
                      (boolSyntax.lhs (Thm.concl saved))) normalized)
                    (!helper_schemas) of
                  SOME (_, _, saved) => saved
                | NONE =>
                    let
                      val action = fn () =>
                        let
                          val label = head_label head
                          val generic_arguments =
                            List.map generic_argument arguments
                          val generic =
                            Term.list_mk_comb (head, generic_arguments)
                          val unfolded =
                            Conv.REWR_CONV definition generic
                          val (closed, _) = close
                            (boolSyntax.rhs (Thm.concl unfolded))
                          val saved = Thm.TRANS unfolded closed
                          val output_nodes = SmtResource.dag_nodes_up_to
                            SmtResource.max_bv_replay_term_nodes
                            (boolSyntax.rhs (Thm.concl saved))
                          val _ = helper_schemas :=
                            (head, head_type, saved) :: !helper_schemas
                        in saved end
                    in
                      SmtResource.profile_phase
                        ("fp-graph/helper-schema/" ^ head_label head)
                        action ()
                    end
              val instantiated = SmtResource.profile_phase
                ("fp-graph/helper-instantiate/" ^ head_label head)
                (fn () => Drule.INST_TY_TERM
                  (Term.match_term
                    (boolSyntax.lhs (Thm.concl schema)) normalized) schema) ()
              val result = Thm.TRANS assembled instantiated
            in save term (result, true) end
        end

      and close_ordinary term head arguments = SmtResource.profile_phase
        "fp-graph/close-ordinary"
        (fn () =>
          if Term.is_abs term orelse List.null arguments then
            save term (Thm.REFL term, false)
          else
            let
              val _ = ordinary := !ordinary + 1
              val converted = List.map close arguments
              val changed = List.exists Lib.snd converted
            in
              if changed then save term
                (rebuild head (List.map Lib.fst converted), true)
              else save term (Thm.REFL term, false)
            end) ()

      val (theorem, _) = close root
      val output = boolSyntax.rhs (Thm.concl theorem)
      val output_nodes = SmtResource.dag_nodes_up_to
        SmtResource.max_bv_replay_term_nodes output
    in
      (theorem,
       {visited = !visited, memo_hits = !memo_hits,
        rewrites = !rewrites, output_nodes = output_nodes,
        literals = !literals, lets = !lets, betas = !betas,
        pairs = !pairs, projections = !projections,
        conditionals = !conditionals, helpers = !helpers,
        priorities = !priorities, ordinary = !ordinary,
        beta_seconds = Time.toReal (!beta_time)})
    end

  fun field_projection_conversion term =
    let
      fun direct theorem = Conv.REWR_CONV theorem term
      fun lift_source head theorem =
        Thm.MK_COMB (Thm.REFL head, theorem)
      fun projection () =
        let val (head, source) = case boolSyntax.strip_comb term of
              (head, [source]) => (head, source)
            | _ => raise Conv.UNCHANGED
        in
          lift_source head (field_projection_conversion source)
          handle Conv.UNCHANGED =>
            if boolSyntax.is_cond source then
              direct boolTheory.COND_RAND
            else
              (Conv.FIRST_CONV
                 [Conv.REWR_CONV pairTheory.FST,
                  Conv.REWR_CONV pairTheory.SND] term
               handle Feedback.HOL_ERR holerr =>
                 if Feedback.top_structure_of holerr = "Conv" andalso
                    Feedback.top_function_of holerr = "NO_CONV" then
                   raise Conv.UNCHANGED
                 else raise Feedback.HOL_ERR holerr)
        end
      val (head, arguments) = boolSyntax.strip_comb term
      fun priority () =
        let
          val (count, word) = case arguments of
            [count, word] => (count, word)
          | _ => raise Conv.UNCHANGED
          val _ = if HOLset.isEmpty
              (Term.FVL_dag [count] Term.empty_tmset) then ()
            else raise Declined "nonliteral priority count"
          val count_theorem = Conv.QCONV bossLib.EVAL count
          val assembled = Thm.MK_COMB
            (Thm.MK_COMB (Thm.REFL head, count_theorem), Thm.REFL word)
          val residue = boolSyntax.rhs (Thm.concl assembled)
          val reduced = Conv.FIRST_CONV
            (List.map Conv.REWR_CONV priority_laws) residue
        in Thm.TRANS assembled reduced end
    in
      if (full_named "pair" "FST" 1 term orelse
          full_named "pair" "SND" 1 term) then projection ()
      else if full_named "smtfloatReplayWord"
          "smtfp_word_priority" 2 term then
        SmtResource.profile_phase "fp-field/priority" priority ()
      else
        case helper_definition term of
          SOME definition => SmtResource.profile_phase
            "fp-field/helper" (fn () => direct definition) ()
        | NONE =>
            if full_named "bool" "LET" 2 term then direct boolTheory.LET_THM
            else if full_named "pair" "pair_CASE" 2 term then
              direct pairTheory.pair_CASE_def
            else if full_named "pair" "UNCURRY" 2 term then
              direct pairTheory.UNCURRY
            else if Term.is_abs head andalso not (List.null arguments) then
              Conv.REDEPTH_CONV BETA_CONV term
            else if rounding_case term then
              direct
                smtfloatReplayRoundingTheory.smtfp_rounding_case_unpack
            else if rounding_test term then
              simpLib.SIMP_CONV bossLib.pure_ss rounding_test_laws term
            else raise Conv.UNCHANGED
    end

  val convert_word_projection = field_projection_conversion

  fun admitted_width admission ty =
    SmtWordGraph.word_width admission ty
    handle Conv.UNCHANGED => raise Declined "unknown floating-point dimension"

  fun word_type width =
    wordsSyntax.mk_word_type (fcpLib.index_type width)

  fun arithmetic_widths admission exponent fraction =
    let
      val e = admitted_width admission (Term.type_of exponent)
      val f = admitted_width admission (Term.type_of fraction)
      val packed = Arbnum.+ (Arbnum.one, Arbnum.+ (e, f))
      val _ = if Arbnum.< (e, Arbnum.fromInt 2) then
          raise Declined "floating-point exponent width is below two"
        else if Arbnum.>= (packed, Arbnum.fromInt 32) then
          raise Declined "floating-point arithmetic width is at least 32"
        else ()
      val d = Arbnum.+ (f, Arbnum.fromInt 5)
      val maximum = Arbnum.-
        (Arbnum.pow (Arbnum.two, e), Arbnum.fromInt 2)
      val required = Arbnum.+ (maximum, d)
      val c = Arbnum.plus1 (Arbnum.log2 (Arbnum.less1 required))
      val cword = word_type c
      val dword = word_type d
      val _ = SmtWordGraph.admit_primitive_type admission cword
      val _ = SmtWordGraph.admit_primitive_type admission dword
    in (c, d, cword, dword) end

  fun named_free name theorem =
    case List.find (fn variable =>
        Lib.fst (Term.dest_var variable) = name)
        (Term.free_vars (Thm.concl theorem)) of
      SOME variable => variable
    | NONE => raise Fail ("missing theorem variable " ^ name)

  fun validate_arithmetic_output theorem =
    let
      val output = boolSyntax.rhs (Thm.concl theorem)
      val _ = bits_fields output
      fun inspect node =
        if Term.is_abs node then
          raise Fail "arithmetic helper closure retained an abstraction"
        else if not (Term.is_const node) then ()
        else
          let val {Thy, Name, ...} = Term.dest_thy_const node
          in
            if Thy = "smtfloatReplayAddSubWord" andalso
                 Name <> "smtfp_word_addsub_fields" orelse
               List.exists (fn saved => Thy = saved)
                 ["smtfloatReplayEncodeWord", "smtfloatReplayWord"] orelse
               Thy = "smtfloat" andalso Name = "smtfp_nan_pattern" orelse
               Thy = "bool" andalso Name = "LET" orelse
               Thy = "pair" andalso List.exists (fn saved => Name = saved)
                 ["pair_CASE", "UNCURRY"] then
              raise Fail ("arithmetic helper closure retained " ^
                Thy ^ "." ^ Name)
            else ()
          end
      val _ = SmtResource.dag_nodes_up_to_with_inspector inspect
        SmtResource.max_bv_replay_term_nodes output
    in () end

  fun build_arithmetic_schema admission subtract head left_bits right_bits =
    let
      val (_, exponent, fraction) = bits_fields left_bits
      val (_, _, right_fraction) = bits_fields right_bits
      val _ = if Term.type_of fraction = Term.type_of right_fraction then ()
        else raise Declined "add/sub operands have different formats"
      val (_, _, cword, dword) =
        arithmetic_widths admission exponent fraction
      val raw_mode = Term.genvar (word_type (Arbnum.fromInt 3))
      val unpack = Term.mk_comb
        (Term.prim_mk_const
          {Thy = "smtfloat", Name = "smtfp_unpack_rounding"}, raw_mode)
      val semantic = Term.list_mk_comb
        (head, [unpack, left_bits, right_bits])
      val law0 = Thm.INST_TYPE
        [{redex = Type.mk_vartype "'c",
          residue = wordsSyntax.dest_word_type cword},
         {redex = Type.mk_vartype "'d",
          residue = wordsSyntax.dest_word_type dword}]
        smtfloatReplayAddSubWordTheory.smtfp_word_addsub_exact
      val law1 = Thm.INST
        [{redex = named_free "subtract" law0,
          residue = if subtract then boolSyntax.T else boolSyntax.F}] law0
      val law2 = simpLib.SIMP_RULE bossLib.pure_ss
        [boolTheory.COND_CLAUSES] law1
      val (_, equation) = boolSyntax.dest_imp (Thm.concl law2)
      val specialized = Drule.INST_TY_TERM
        (Term.match_term (boolSyntax.rhs equation) semantic) law2
      val (premise, _) = boolSyntax.dest_imp (Thm.concl specialized)
      val premise_theorem = Drule.EQT_ELIM (bossLib.EVAL premise)
      val exact = Thm.SYM (Thm.MP specialized premise_theorem)
      val word_operator = boolSyntax.rhs (Thm.concl exact)
      (* Expose the three result fields without expanding their shared
         producer.  The field-projection conversion below lowers only fields
         demanded by the surrounding Boolean certificate. *)
      val exposed = simpLib.SIMP_CONV bossLib.pure_ss
        [smtfloatReplayAddSubWordTheory.smtfp_word_addsub_def,
         boolTheory.LET_THM, pairTheory.pair_CASE_def,
         pairTheory.UNCURRY] word_operator
      val result = Thm.TRANS exact exposed
      val _ = if Term.aconv (boolSyntax.lhs (Thm.concl result)) semantic
        then () else raise Fail "arithmetic schema lost its endpoint"
      val _ = validate_arithmetic_output result
      val metrics =
        {visited = 0, memo_hits = 0, rewrites = 1,
         output_nodes = SmtResource.dag_nodes_up_to
           SmtResource.max_bv_replay_term_nodes
           (boolSyntax.rhs (Thm.concl result)),
         literals = 0, lets = 0, betas = 0, pairs = 0,
         projections = 3, conditionals = 0, helpers = 1,
         priorities = 0, ordinary = 0, beta_seconds = 0.0}
    in (result, metrics) end

  type schema_entry =
    {source_type : hol_type, subtract : bool,
     theorem : thm, metrics : helper_metrics}

  fun arithmetic_schema admission cache subtract head left_bits right_bits =
    let val source_type = Term.type_of left_bits
    in
      case List.find (fn entry => #subtract entry = subtract andalso
          Type.compare (#source_type entry, source_type) = EQUAL) (!cache) of
        SOME entry => (#theorem entry, #metrics entry)
      | NONE =>
          let
            val (theorem, metrics) = SmtResource.profile_phase
              "fp-graph/static-schema"
              (fn () => build_arithmetic_schema admission subtract
                head left_bits right_bits) ()
            val entry = {source_type = source_type, subtract = subtract,
              theorem = theorem, metrics = metrics}
            val _ = cache := entry :: !cache
          in (theorem, metrics) end
    end

  fun represent_internal admission word_admission schema_cache memo term =
    case List.find (fn (saved, _) => Portable.pointer_eq (term, saved))
        (!memo) of
      SOME (_, descriptor) => descriptor
    | NONE => if not (is_fp_type (Term.type_of term)) then
      raise Declined "term is not floating-point"
    else if known_unsupported term then
      raise Declined "unsupported floating-point producer"
    else
      let
        val _ = ignore (#intern admission (Term.type_of term))
        val equality =
          case head_name term of
            SOME ("smtfloat", "smtfp_bits") => Thm.REFL term
          | SOME ("smtfloat", "smtfp_abs") =>
              let
                val argument = case boolSyntax.strip_comb term of
                    (_, [argument]) => argument
                  | _ => raise Declined "malformed smtfp_abs"
                val child = represent_internal admission word_admission
                  schema_cache memo argument
                val (head, _) = boolSyntax.strip_comb term
                val congruence = Thm.MK_COMB
                  (Thm.REFL head, #representation child)
                val actual = boolSyntax.rhs (Thm.concl congruence)
                val (bits, substitution) = placeholder child
                val schematic = Term.mk_comb (head, bits)
              in
                Thm.TRANS congruence
                  (instantiate_law admission smtfloatTheory.smtfp_abs_bits
                    schematic actual substitution)
              end
          | SOME ("smtfloat", "smtfp_neg") =>
              let
                val argument = case boolSyntax.strip_comb term of
                    (_, [argument]) => argument
                  | _ => raise Declined "malformed smtfp_neg"
                val child = represent_internal admission word_admission
                  schema_cache memo argument
                val (head, _) = boolSyntax.strip_comb term
                val congruence = Thm.MK_COMB
                  (Thm.REFL head, #representation child)
                val actual = boolSyntax.rhs (Thm.concl congruence)
                val (bits, substitution) = placeholder child
                val schematic = Term.mk_comb (head, bits)
              in
                Thm.TRANS congruence
                  (instantiate_law admission smtfloatTheory.smtfp_neg_bits
                    schematic actual substitution)
              end
          | SOME ("smtfloat", "smtfp_add") =>
              arithmetic_representation admission word_admission
                schema_cache memo false term
          | SOME ("smtfloat", "smtfp_sub") =>
              arithmetic_representation admission word_admission
                schema_cache memo true term
          | SOME ("smtfloat", name) =>
              (case constant_law name of
                 SOME schema => constant_representation admission schema term
               | NONE => expose_leaf term)
          | _ => expose_leaf term
        val equality = Thm.TRANS (Thm.REFL term) equality
        val represented = boolSyntax.rhs (Thm.concl equality)
        val (sign, exponent, fraction) = bits_fields represented
        val _ = if Portable.pointer_eq
            (boolSyntax.lhs (Thm.concl equality), term) then ()
          else raise Fail "SmtFpGraph.represent lost its endpoint"
        val descriptor =
          {value = term, sign = sign, exponent = exponent,
           fraction = fraction, representation = equality}
        val _ = memo := (term, descriptor) :: !memo
      in descriptor
      end

  and arithmetic_representation admission word_admission schema_cache memo
      subtract term =
    let
      val (head, arguments) = boolSyntax.strip_comb term
      val (mode, left, right) = case arguments of
        [mode, left, right] => (mode, left, right)
      | _ => raise Declined "malformed floating-point add/sub"
      val left_descriptor = represent_internal admission word_admission
        schema_cache memo left
      val right_descriptor = represent_internal admission word_admission
        schema_cache memo right
      val inverse = Thm.SYM smtfloatTheory.smtfp_unpack_pack_rounding
      val mode_theorem = Drule.INST_TY_TERM
        (Term.match_term (boolSyntax.lhs (Thm.concl inverse)) mode) inverse
      val congruence = rebuild head
        [mode_theorem, #representation left_descriptor,
         #representation right_descriptor]
      val actual = boolSyntax.rhs (Thm.concl congruence)
      val (left_bits, _) = placeholder left_descriptor
      val (right_bits, _) = placeholder right_descriptor
      val (schema, _) = arithmetic_schema word_admission schema_cache
        subtract head left_bits right_bits
      val instantiated = SmtResource.profile_phase
        "fp-graph/late-insertion"
        (fn () => Drule.INST_TY_TERM
          (Term.match_term (boolSyntax.lhs (Thm.concl schema)) actual) schema) ()
    in Thm.TRANS congruence instantiated end

  fun represent term =
    SmtResource.with_bitblast_step_time "fp-graph-stage1"
      (fn term =>
        let
          val admission = SmtSkeletonProve.new_type_admission_context ()
          val _ = preflight admission term
          val word_admission = SmtWordGraph.new_type_admission ()
          val schema_cache = ref ([] : schema_entry list)
          val memo = ref []
        in represent_internal admission word_admission schema_cache memo term end)
      term

  val helper_definitions =
    [smtfloatTheory.smtfp_nan_pattern_def,
     smtfloatTheory.smtfp_mag_lt_def,
     smtfloatTheory.smtfp_word_equal_def,
     smtfloatTheory.smtfp_word_fp_eq_def,
     smtfloatTheory.smtfp_word_lt_def,
     smtfloatTheory.smtfp_word_le_def,
     smtfloatTheory.smtfp_word_gt_def,
     smtfloatTheory.smtfp_word_ge_def]

  fun close_schema theorem = Conv.CONV_RULE
    (Conv.RAND_CONV
      (simpLib.SIMP_CONV simpLib.empty_ss helper_definitions)) theorem
    handle Conv.UNCHANGED => theorem

  val atom_laws = List.map (fn (name, theorem) =>
    (name, close_schema theorem))
    [("smtfp_is_normal", smtfloatTheory.smtfp_is_normal_bits),
     ("smtfp_is_subnormal", smtfloatTheory.smtfp_is_subnormal_bits),
     ("smtfp_is_zero", smtfloatTheory.smtfp_is_zero_bits),
     ("smtfp_is_infinite", smtfloatTheory.smtfp_is_infinite_bits),
     ("smtfp_is_nan", smtfloatTheory.smtfp_is_nan_bits),
     ("smtfp_is_negative", smtfloatTheory.smtfp_is_negative_bits),
     ("smtfp_is_positive", smtfloatTheory.smtfp_is_positive_bits),
     ("smtfp_eq", smtfloatTheory.smtfp_eq_bits),
     ("smtfp_lt", smtfloatTheory.smtfp_lt_bits),
     ("smtfp_le", smtfloatTheory.smtfp_le_bits),
     ("smtfp_gt", smtfloatTheory.smtfp_gt_bits),
     ("smtfp_ge", smtfloatTheory.smtfp_ge_bits)]

  val equality_bits_law =
    close_schema smtfloatTheory.smtfp_equality_bits

  val finite_bits_law =
    let
      val operand = case boolSyntax.strip_comb
          (boolSyntax.lhs
            (Thm.concl smtfloatTheory.smtfp_is_finite_expansion)) of
          (_, [operand]) => operand
        | _ => raise Fail "malformed smtfp_is_finite_expansion"
      val represented = boolSyntax.lhs
        (Thm.concl smtfloatTheory.smtfp_bits_rep)
      val (bits_head, represented_fields) =
        boolSyntax.strip_comb represented
      val fields = List.map (Term.genvar o Term.type_of) represented_fields
      val bits = List.foldl
        (fn (field, function) => Term.mk_comb (function, field))
        bits_head fields
      val represented = Drule.INST_TY_TERM
        (Term.match_term operand bits)
        smtfloatTheory.smtfp_is_finite_expansion
    in
      close_schema
        (simpLib.SIMP_RULE simpLib.empty_ss
          [smtfloatTheory.smtfp_is_nan_bits,
           smtfloatTheory.smtfp_is_infinite_bits] represented)
    end

  fun law_for name =
    case List.find (fn (saved, _) => name = saved) atom_laws of
      SOME (_, theorem) => theorem
    | NONE => raise Declined ("unsupported FP atom " ^ name)

  val atom_names = "smtfp_is_finite" :: List.map Lib.fst atom_laws

  fun atom_arity name =
    if List.exists (fn saved => name = saved)
        ["smtfp_is_normal", "smtfp_is_subnormal", "smtfp_is_zero",
         "smtfp_is_infinite", "smtfp_is_nan", "smtfp_is_finite",
         "smtfp_is_negative", "smtfp_is_positive"] then 1
    else 2

  fun classify_atom term =
    let
      val _ = if Term.type_of term = Type.bool then ()
        else raise Declined "FP atom does not have Boolean result type"
    in
      if boolSyntax.is_eq term then
        let val (left, right) = boolSyntax.dest_eq term
        in
          if is_fp_type (Term.type_of left) andalso
             is_fp_type (Term.type_of right) then
            (Term.rator (Term.rator term), [left, right], equality_bits_law)
          else raise Declined "HOL equality is not over FP values"
        end
      else
        let
          val (head, arguments) = boolSyntax.strip_comb term
          val _ = if Term.is_const head then ()
            else raise Declined "FP atom head is not a registered constant"
          val name = case registered_name atom_names head of
              SOME name => name
            | NONE => raise Declined "not a registered FP predicate"
          val _ = if List.length arguments = atom_arity name then ()
            else raise Declined "FP atom has the wrong arity"
        in
          if name = "smtfp_is_finite" then
            (head, arguments, finite_bits_law)
          else (head, arguments, law_for name)
        end
    end

  fun lower_atom_domain term =
    (ignore (classify_atom term); true)
    handle Declined _ => false
         | Feedback.HOL_ERR _ => false

  fun convert_addsub_observation admission word_admission schema_cache memo
      term =
    let
      val (predicate, predicate_arguments) = boolSyntax.strip_comb term
      val operation = case predicate_arguments of
        [operation] => operation
      | _ => raise Declined "malformed add/sub observation"
      val observation =
        case registered_name ["smtfp_is_zero", "smtfp_is_nan"] predicate of
          SOME name => name
        | NONE => raise Declined "not a supported add/sub observation"
      val (operator, arguments) = boolSyntax.strip_comb operation
      val (mode, left, right) = case arguments of
        [mode, left, right] => (mode, left, right)
      | _ => raise Declined "malformed floating-point add/sub"
      val subtract =
        case head_name operation of
          SOME ("smtfloat", "smtfp_add") => false
        | SOME ("smtfloat", "smtfp_sub") => true
        | _ => raise Declined "zero observation is not over add/sub"
      val left_descriptor = represent_internal admission word_admission
        schema_cache memo left
      val right_descriptor = represent_internal admission word_admission
        schema_cache memo right
      val inverse = Thm.SYM smtfloatTheory.smtfp_unpack_pack_rounding
      val mode_theorem = Drule.INST_TY_TERM
        (Term.match_term (boolSyntax.lhs (Thm.concl inverse)) mode) inverse
      val operation_equality = rebuild operator
        [mode_theorem, #representation left_descriptor,
         #representation right_descriptor]
      val atom_equality = Thm.MK_COMB
        (Thm.REFL predicate, operation_equality)
      val actual = boolSyntax.rhs (Thm.concl atom_equality)
      val (left_bits, _) = placeholder left_descriptor
      val (right_bits, _) = placeholder right_descriptor
      val (_, exponent, fraction) = bits_fields left_bits
      val (_, _, right_fraction) = bits_fields right_bits
      val _ = if Term.type_of fraction = Term.type_of right_fraction then ()
        else raise Declined "add/sub operands have different formats"
      val (_, _, cword, dword) =
        arithmetic_widths word_admission exponent fraction
      val law =
        if observation = "smtfp_is_zero" then
          smtfloatReplayAddSubWordTheory.smtfp_addsub_is_zero_word_trace
        else
          smtfloatReplayAddSubWordTheory.smtfp_addsub_is_nan_word_fields
      val law0 = Thm.INST_TYPE
        [{redex = Type.mk_vartype "'c",
          residue = wordsSyntax.dest_word_type cword},
         {redex = Type.mk_vartype "'d",
          residue = wordsSyntax.dest_word_type dword}] law
      val law1 = Thm.INST
        [{redex = named_free "subtract" law0,
          residue = if subtract then boolSyntax.T else boolSyntax.F}] law0
      val law2 = simpLib.SIMP_RULE bossLib.pure_ss
        [boolTheory.COND_CLAUSES] law1
      val (_, equation) = boolSyntax.dest_imp (Thm.concl law2)
      val specialized = Drule.INST_TY_TERM
        (Term.match_term (boolSyntax.lhs equation) actual) law2
      val (premise, _) = boolSyntax.dest_imp (Thm.concl specialized)
      val premise_theorem = Drule.EQT_ELIM (bossLib.EVAL premise)
      val observation = Thm.MP specialized premise_theorem
    in Thm.TRANS atom_equality observation end

  fun convert_atom_internal term =
    let
      val admission = SmtSkeletonProve.new_type_admission_context ()
      val _ = preflight admission term
      val word_admission = SmtWordGraph.new_type_admission ()
      val schema_cache = ref ([] : schema_entry list)
      val memo = ref []
      val (candidate_head, candidate_arguments) =
        boolSyntax.strip_comb term
      val direct_domain =
        case candidate_arguments of
          [operation] =>
            Option.isSome
              (registered_name ["smtfp_is_zero", "smtfp_is_nan"]
                candidate_head) andalso
            (case head_name operation of
               SOME ("smtfloat", "smtfp_add") => true
             | SOME ("smtfloat", "smtfp_sub") => true
             | _ => false)
        | _ => false
    in
      if direct_domain then
        convert_addsub_observation admission word_admission schema_cache memo
          term
      else
    let
      val (head, arguments, law) = classify_atom term
      fun convert argument = if is_fp_type (Term.type_of argument) then
          let
            val descriptor = SmtResource.with_bitblast_step_time
              "fp-graph-stage1-argument"
              (represent_internal admission word_admission schema_cache memo)
              argument
            val (bits, substitution) = placeholder descriptor
          in (#representation descriptor, bits, substitution) end
        else (Thm.REFL argument, argument, [])
      val converted = List.map convert arguments
      val equality = List.foldl
        (fn ((argument_equality, _, _), theorem) =>
          Thm.MK_COMB (theorem, argument_equality))
        (Thm.REFL head) converted
      val actual = boolSyntax.rhs (Thm.concl equality)
      val schematic = List.foldl
        (fn ((_, argument, _), function) =>
          Term.mk_comb (function, argument)) head converted
      val substitution = List.concat
        (List.map (fn (_, _, substitution) => substitution) converted)
      val result = Thm.TRANS equality
        (SmtResource.with_bitblast_step_time "fp-graph-stage1-law"
          (fn () => instantiate_law admission law schematic actual
            substitution) ())
      val result = Thm.TRANS (Thm.REFL term) result
      val _ = if Portable.pointer_eq
          (boolSyntax.lhs (Thm.concl result), term) then ()
        else raise Fail "SmtFpGraph.convert_atom lost its endpoint"
    in result end
    end

  val convert_atom = convert_atom_internal

  fun lower_atom term =
    SmtResource.with_bitblast_step_time "fp-graph-stage1"
      (fn term =>
        let
          val converted = convert_atom_internal term
          val right = boolSyntax.rhs (Thm.concl converted)
          val lowered = Conv.QCONV
            (SmtWordGraph.normalize_with_node_conversion
              field_projection_conversion) right
        in Thm.TRANS converted lowered end) term
end
