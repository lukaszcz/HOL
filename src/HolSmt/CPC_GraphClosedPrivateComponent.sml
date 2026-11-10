(* Kernel computations of exact admitted closed private component targets. *)
structure CPC_GraphClosedPrivateComponent :> CPC_GraphClosedPrivateComponent =
struct
  open SmtReplayImport SmtWordGraph bossLib smtfloatTheory
    smtfloatReplayWordTheory
  val ERR = Feedback.mk_HOL_ERR "CPC_GraphClosedPrivateComponent"
  val width_cap = 16
  val island_limit = 8192
  fun size metric limit term = case metric limit term of
      SOME n => n | NONE => raise ERR "proof" "actual law exceeds preflight"
  (* A width<=16 n2w literal costs at most 2*16+5=37 nodes. Equality
     contributes three, so n+40 bounds the complete component computation.
     Its ALPHA bound also dominates the whole target-congruence equation. *)
  fun admit limit target =
    let val budget = Int.min (limit,island_limit)
        fun fits metric = case metric budget target of
            SOME n => 3+2*(n+40) <= budget
          | NONE => false
    in budget > 0 andalso fits SmtReplayImport.bounded_raw_size andalso
      fits SmtReplayImport.bounded_binder_size end
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem) in
      null (Thm.hyp theorem) andalso null (Tag.axioms_of (Thm.tag theorem))
      andalso List.all (fn tag => tag = "DISK_THM") tags end
  fun named theory name arity term =
    let val (head,args) = boolSyntax.strip_comb term in
      if Term.is_const head andalso length args = arity then
        let val id = Term.dest_thy_const head in
          if #Thy id = theory andalso #Name id = name then SOME args else NONE
        end
      else NONE
    end
  fun prove {target,limit,check_type} =
    if not (admit limit target) then NONE else
    let
      val budget = Int.min (limit,island_limit)
      val metrics = [SmtReplayImport.bounded_raw_size,
        SmtReplayImport.bounded_binder_size]
      fun bound n = if n <= budget then () else
        raise ERR "proof" "actual computation exceeded complete law budget"
      fun whole term = List.app (fn metric =>
        bound (size metric budget term)) metrics
      fun alpha left right = List.app (fn metric =>
        bound (3+size metric budget left+size metric budget right)) metrics
      fun inspect term =
        (check_type (Term.type_of term);
         if Term.is_comb term then
           let val (operator,operand) = Term.dest_comb term
           in inspect operator;inspect operand end
         else ())
      (* No binder/free-variable traversal occurs before both complete gates. *)
      fun binder_free term = not (Term.is_abs term) andalso
        (not (Term.is_comb term) orelse
          binder_free (Term.rator term) andalso binder_free (Term.rand term))
      val _ = inspect target
      val primitive = SmtWordGraph.new_type_admission ()
      val has_bits = ref false
      fun word_width ty =
        if not (wordsSyntax.is_word_type ty) then NONE else
          let val n = SmtWordGraph.word_width primitive ty in
            if Arbnum.<= (n,Arbnum.fromInt width_cap) then
              SOME (Arbnum.toInt n) else NONE
          end
      fun width term = word_width (Term.type_of term)
      fun power 0 = 1 | power n = 2*power (n-1)
      fun literal expected term =
        wordsSyntax.is_word_literal term andalso width term = SOME expected
        andalso Arbnum.< (wordsSyntax.dest_word_literal term,
          Arbnum.fromInt (power expected))
      fun selector field term =
        case named "binary_ieee" ("recordtype.float.seldef." ^ field) 1 term of
          SOME [represented] =>
            (case named "smtfloat" "smtfp_rep" 1 represented of
                SOME [source] => SOME source | _ => NONE)
        | _ => NONE
      fun source_dimensions term =
        let val {Thy,Tyop,Args} = Type.dest_thy_type (Term.type_of term) in
          case Args of [fraction,exponent] =>
            if Thy = "smtfloat" andalso Tyop = "smtfp" then
              (case (word_width (wordsSyntax.mk_word_type exponent),
                     word_width (wordsSyntax.mk_word_type fraction)) of
                 (SOME e,SOME f) => SOME (e,f) | _ => NONE)
            else NONE
          | _ => NONE
        end
      fun source term =
        case named "smtfloat" "smtfp_bits" 3 term of
          SOME [sign,exponent,fraction] =>
            (case source_dimensions term of SOME (e,f) =>
              if sign_field sign andalso literal e exponent andalso
                  literal f fraction then (has_bits := true;true) else false
             | NONE => false)
        | _ =>
            if List.exists (fn name =>
                Option.isSome (named "smtfloat" name 0 term))
                ["smtfp_pzero","smtfp_nzero","smtfp_nan",
                 "smtfp_pinf","smtfp_ninf"] then
              Option.isSome (source_dimensions term)
            else false
      and sign_field term = literal 1 term orelse
        (case selector "Sign" term of SOME value => source value | _ => false)
      fun predicate name term = case named "smtfloat" name 1 term of
          SOME [value] => SOME value | _ => NONE
      fun same left right = Term.aconv left right
      fun special value term = case named "bool" "\\/" 2 term of
          SOME [zero,rest] =>
            (case (predicate "smtfp_is_zero" zero,
                   named "bool" "\\/" 2 rest) of
               (SOME first,SOME [nan,inf]) =>
                 (case (predicate "smtfp_is_nan" nan,
                        predicate "smtfp_is_infinite" inf) of
                    (SOME second,SOME third) =>
                      same value first andalso same value second andalso
                      same value third
                  | _ => false)
             | _ => false)
        | _ => false
      fun classification term = case named "bool" "COND" 3 term of
          SOME [test,one,zero] =>
            if literal 1 one andalso literal 1 zero andalso
                Arbnum.toInt (wordsSyntax.dest_word_literal one) = 1 andalso
                Arbnum.toInt (wordsSyntax.dest_word_literal zero) = 0 then
              let fun find [] = NONE
                    | find (name :: rest) = case predicate name test of
                        SOME value => SOME (value,1) | NONE => find rest
              in find ["smtfp_is_zero","smtfp_is_nan","smtfp_is_infinite"] end
            else NONE
        | _ => NONE
      fun unpack name offset term =
        case named "smtfloatReplayWord" name 4 term of
          SOME [flags,exponent,fraction,shape] =>
            (case (selector "Exponent" exponent,
                   selector "Significand" fraction) of
               (SOME value,SOME other) =>
                 if same value other andalso special value flags andalso
                     Option.isSome (named "words" "word_L" 0 shape) then
                   (case source_dimensions value of SOME (e,f) =>
                     SOME (value,(if offset then e+2 else f+1)) | _ => NONE)
                 else NONE
             | _ => NONE)
        | _ => NONE
      fun component term = case selector "Sign" term of
          SOME value => SOME (value,1)
        | NONE => (case classification term of SOME value => SOME value
            | NONE => (case unpack "smtfp_cvc_unpacked_exponent" true term of
                SOME value => SOME value
              | NONE => unpack "smtfp_cvc_unpacked_significand" false term))
      fun run left right value expected =
        if expected > width_cap orelse width left <> SOME expected orelse
            not (literal expected right) orelse not (source value) orelse
            not (!has_bits) orelse not (binder_free target) orelse
            not (null (Term.free_vars target)) then NONE else
        let
          val literal_bound = 2*expected+5
          (* Refine the conservative budget using the actual primitive width
             before evaluating any field, predicate or public unpack helper. *)
          val _ = List.app (fn metric =>
            let val c = size metric budget left
                val r = size metric budget right
                val n = size metric budget target
                val output = 3+literal_bound+r
            in bound (3+c+literal_bound);bound (3+n+output);
               bound (output+4);bound (3+2*(3+c+literal_bound)) end) metrics
          val evaluated = bossLib.EVAL left
          val _ = whole (Thm.concl evaluated)
          val _ = if clean evaluated then () else
            raise ERR "proof" "unclean actual component computation"
          val (input,output) = boolSyntax.dest_eq (Thm.concl evaluated)
          val _ = List.app (fn metric =>
            bound (size metric budget output)) metrics
          val _ = if List.all (fn metric =>
              size metric budget output <= literal_bound) metrics andalso
              literal expected output andalso same input left then () else
            raise ERR "proof" "component evaluator changed typed literal law"
          val _ = alpha left input
          val _ = inspect (Thm.concl evaluated)
          val evaluated = Thm.TRANS (Thm.ALPHA left input) evaluated
          val equality = Term.rator (Term.rator target)
          val converted = Thm.MK_COMB
            (Thm.MK_COMB (Thm.REFL equality,evaluated),Thm.REFL right)
          val _ = whole (Thm.concl converted)
          val (original,residue) = boolSyntax.dest_eq (Thm.concl converted)
          val _ = alpha target original
          val _ = inspect (Thm.concl converted)
          val converted = Thm.TRANS (Thm.ALPHA target original) converted
          val conclusion = bossLib.EVAL residue
          val _ = whole (Thm.concl conclusion)
          val _ = if clean conclusion then () else
            raise ERR "proof" "unclean actual literal equality computation"
          val (actual,answer) = boolSyntax.dest_eq (Thm.concl conclusion)
          val _ = alpha residue actual
          val _ = inspect (Thm.concl conclusion)
          val conclusion = Thm.TRANS (Thm.ALPHA residue actual) conclusion
        in if same answer boolSyntax.F then NONE
           else if same answer boolSyntax.T then
             let val result = Thm.EQ_MP (Thm.SYM converted)
                   (Thm.EQ_MP (Thm.SYM conclusion) boolTheory.TRUTH)
                 val _ = alpha (Thm.concl result) target
                 val result = Thm.EQ_MP
                   (Thm.ALPHA (Thm.concl result) target) result
                 val _ = if clean result then () else
                   raise ERR "proof" "actual component result is not closed"
             in SOME result end
           else raise ERR "proof" "literal equality did not evaluate to Boolean"
        end
    in case named "min" "=" 2 target of SOME [left,right] =>
         (case component left of SOME (value,expected) =>
             run left right value expected | _ => NONE)
       | _ => NONE
    end
end
