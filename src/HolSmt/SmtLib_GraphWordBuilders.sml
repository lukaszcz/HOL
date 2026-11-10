(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphWordBuilders :> SmtLib_GraphWordBuilders =
struct
  structure B = SmtLib_GraphBackend
  structure P = SmtLib_Parser
  structure RP = SmtReplayResourcePolicy
  structure T = SmtLib_Theories
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphWordBuilders"
  val legacy_ERR = Feedback.mk_HOL_ERR "SmtLib_Theories"

  fun bbterm backend (limits : RP.recipe_policy) =
    let
      val _ = if List.all RP.positive
          [#template_limit limits, #index_limit limits,
           #operand_limit limits, #token_limit limits] then ()
        else raise ERR "limits" "nonpositive graph constructor contract"

      fun parse frame token indices bits =
        let
          (* Keep K_zero_list's index/arity declines, before mk_bbterm's
             Boolean sort error. No index value needs observation here. *)
          val _ = T.zero_args () indices
          val _ = T.list_args (fn _ => ()) bits
          val width = List.length bits
          val _ = if List.all (fn bit =>
              Type.compare (B.type_of backend bit, Type.bool) = EQUAL)
              bits then ()
            else raise legacy_ERR "mk_bbterm"
              "Boolean bit arguments expected"
          val _ = if RP.allows (#token_limit limits)
              (IntInf.fromInt (String.size token)) then ()
            else raise ERR "bbterm" "constructor token exceeds contract"
          val _ = if RP.allows (#operand_limit limits)
              (IntInf.fromInt width) then ()
            else raise ERR "bbterm"
              "constructor operand count exceeds contract"
          val width_num = Arbnum.fromInt width
          exception NotShape
          fun attempt action = SOME (action ()) handle NotShape => NONE

          (* Only these fixed-depth destructors enter operand syntax.
             In particular, no generic strip_comb or operand reification. *)
          fun constant thy name value =
            case B.view backend frame value of
              B.Atom atom =>
                (let val {Thy, Name, ...} = Term.dest_thy_const atom in
                   Thy = thy andalso Name = name
                 end handle Feedback.HOL_ERR _ => false)
            | _ => false
          fun application value =
            case B.view backend frame value of
              B.Apply pair => pair
            | _ => raise NotShape
          fun unary thy name value =
            let val (head, argument) = application value in
              if constant thy name head then argument else raise NotShape
            end
          fun binary thy name value =
            let
              val (left, right) = application value
              val (head, left) = application left
            in
              if constant thy name head then (left, right)
              else raise NotShape
            end
          fun dest_xor value =
            binary "HolSmt" "xor" value
            handle NotShape => binary "min" "=" (unary "bool" "~" value)
          fun boolean value =
            if constant "bool" "T" value then SOME true
            else if constant "bool" "F" value then SOME false
            else NONE
          fun dest_bit value = binary "words" "word_bit" value
          (* Compare only against the small expected selector position.
             A compound/huge index is a shape miss, not a new refusal or
             permission to reify an expanded numeric graph. *)
          fun index_is expected value =
            let
              fun matches term value =
                if Term.is_const term then
                  (case B.view backend frame value of
                     B.Atom atom => Term.aconv term atom
                   | _ => false)
                else case B.view backend frame value of
                    B.Apply (f,x) =>
                      let val (tf,tx)=Term.dest_comb term in
                        matches tf f andalso matches tx x
                      end
                  | _ => false
            in matches (numSyntax.mk_numeral expected) value end
          fun dimension word =
            let val ty = B.type_of backend word in
              SOME (fcpLib.index_to_num (wordsSyntax.dest_word_type ty))
              handle Feedback.HOL_ERR _ => NONE
            end

          (* Only schematic holes and bounded stock syntax enter recipes.
             No Term.term representing an actual word is ever requested. *)
          fun construct holes template operands =
            B.construct_with_policy backend frame
              (B.compile_recipe_with_policy
                {template = template, holes = holes,
                 template_limit = #template_limit limits}) operands
          fun word_unary mk word =
            let val hole = Term.mk_var
                  ("__smt_bb_word", B.type_of backend word)
            in construct [hole] (mk hole) [word] end
          fun word_binary mk (left, right) =
            let
              val l = Term.mk_var
                ("__smt_bb_left", B.type_of backend left)
              val r = Term.mk_var
                ("__smt_bb_right", B.type_of backend right)
            in construct [l, r] (mk (l, r)) [left, right] end

          fun from_selectors bs =
            case attempt (fn () => List.map dest_bit bs) of
              SOME ((first, word) :: rest) =>
                let
                  fun check _ [] = true
                    | check next ((index, other) :: tail) =
                        index_is next index andalso
                        B.same_value backend (other, word) andalso
                        check (Arbnum.plus1 next) tail
                in
                  if index_is Arbnum.zero first andalso
                     dimension word = SOME width_num andalso
                     check Arbnum.one rest then SOME word else NONE
                end
            | _ => NONE

          (* Preserve mk_bbterm's priority and four levels of recovery.
             Fuel zero does not even recover a bare selector vector. *)
          fun recover 0 _ = NONE
            | recover fuel bs =
                case from_selectors bs of
                  SOME word => SOME word
                | NONE =>
                    (case from_binary fuel (binary "bool" "/\\")
                        wordsSyntax.mk_word_and bs of
                       SOME word => SOME word
                     | NONE =>
                         (case from_binary fuel (binary "bool" "\\/")
                             wordsSyntax.mk_word_or bs of
                            SOME word => SOME word
                          | NONE =>
                              (case from_binary fuel dest_xor
                                  wordsSyntax.mk_word_xor bs of
                                 SOME word => SOME word
                               | NONE =>
                                   (case from_binary fuel (binary "min" "=")
                                       wordsSyntax.mk_word_xnor bs of
                                      SOME word => SOME word
                                    | NONE => from_not fuel bs))))
          and from_binary fuel dest mk bs =
            case attempt (fn () => List.map dest bs) of
              NONE => NONE
            | SOME pairs =>
                (case (recover (fuel - 1) (List.map #1 pairs),
                       recover (fuel - 1) (List.map #2 pairs)) of
                   (SOME left, SOME right) =>
                     SOME (word_binary mk (left, right))
                 | _ => NONE)
          and from_not fuel bs =
            case attempt (fn () => List.map (unary "bool" "~") bs) of
              NONE => NONE
            | SOME inner =>
                (case recover (fuel - 1) inner of
                   SOME word => SOME (word_unary
                     wordsSyntax.mk_word_1comp word)
                 | NONE => NONE)

          val one = wordsSyntax.mk_word (Arbnum.one, Arbnum.one)
          val zero = wordsSyntax.mk_word (Arbnum.zero, Arbnum.one)
          fun singleton bit =
            case boolean bit of
              SOME true => B.literal backend frame one
            | SOME false => B.literal backend frame zero
            | NONE =>
                let val hole = Term.mk_var ("__smt_bb_bit", Type.bool) in
                  construct [hole] (boolSyntax.mk_cond (hole, one, zero))
                    [bit]
                end
          fun constant_value [] _ value = SOME value
            | constant_value (bit :: rest) place value =
                case boolean bit of
                  NONE => NONE
                | SOME set => constant_value rest
                    (Arbnum.* (place, Arbnum.fromInt 2))
                    (if set then Arbnum.+ (value, place) else value)
          fun exact_word () =
            case constant_value bits Arbnum.one Arbnum.zero of
              SOME value => B.literal backend frame
                (wordsSyntax.mk_word (value, width_num))
            | NONE =>
                (case List.rev bits of
                   [] => raise legacy_ERR "mk_bbterm" "empty bit vector"
                 | high :: lower => List.foldl
                     (fn (bit, word) => word_binary
                       wordsSyntax.mk_word_concat (word, singleton bit))
                     (singleton high) lower)
        in
          case recover 4 bits of
            SOME word => word
          | NONE => exact_word ()
        end
    in parse end
end
