(* Copyright (c) 2026 The HOL4 contributors. *)

(* Shared authoritative Z3 literal policy. Graph admission happens before
   literal construction; ordinary parsing retains its original behavior. *)
structure Z3_ProofLiterals =
struct
  val ERR = Feedback.mk_HOL_ERR "Z3_ProofLiterals"
  fun numeric token =
      let
        fun digits text = String.size text > 0 andalso
          List.all Char.isDigit (String.explode text)
        fun signed_integer text =
          if String.isPrefix "-" text then
            digits (String.extract (text, 1, NONE))
          else digits text
        val fields = String.fields (Lib.equal #"/") token
        val fraction =
          case fields of
            [numerator, denominator] =>
              signed_integer numerator andalso digits denominator
          | _ => false
        val negated = String.isPrefix "-" token andalso
          signed_integer token
      in
        if negated orelse fraction then
          let
            (* convert to a fraction, if it isn't already *)
            val n_fraction =
              if fraction then
                token
              else
                token ^ "/1"
            val (left, right) = Lib.pair_of_list
              (String.fields (Lib.equal #"/") n_fraction)
            val numerator = Arbint.fromString left
            val denominator = Arbint.fromString right
          in
            if denominator = Arbint.one then
              realSyntax.term_of_int numerator
            else
              realSyntax.mk_div (realSyntax.term_of_int numerator,
                realSyntax.term_of_int denominator)
          end
        else
          SmtLib_Theories.decline "<z3_builtin_dict._>"
            "not a negated numeral or fraction"
      end

  fun word token =
      if String.size token > 2 andalso String.isPrefix "bv" token andalso
         Char.isDigit (String.sub (token, 2)) andalso
         String.isSubstring "[" token then
        let
          val args = String.extract (token, 2, NONE)
          val (value, args) = Lib.pair_of_list (String.fields (Lib.equal #"[")
            args)
          val (size, args) = Lib.pair_of_list (String.fields (Lib.equal #"]")
            args)
          val _ = args = "" orelse
            SmtLib_Theories.decline "<z3_builtin_dict._>"
              "not a bit-vector constant"
          val value = Library.parse_arbnum value
          val size = Library.parse_arbnum size
        in
          wordsSyntax.mk_word (value, size)
        end
      else
        SmtLib_Theories.decline "<z3_builtin_dict._>"
          "not a bit-vector constant"

  fun bounded_word width_limit token =
    let
      val _ = if width_limit > 0 then () else
        raise ERR "word" "nonpositive word-width contract"
      val candidate = String.size token > 2 andalso
        String.isPrefix "bv" token andalso
        Char.isDigit (String.sub (token, 2)) andalso
        String.isSubstring "[" token
      val _ = if candidate then
        let
          val fields = String.fields (fn c => c = #"[")
            (String.extract (token, 2, NONE))
          val size = case fields of [_, suffix] =>
              (case String.fields (fn c => c = #"]") suffix of
                [size, ""] => SOME size | _ => NONE)
            | _ => NONE
          val _ = case size of SOME text =>
              if Arbnum.<= (Library.parse_arbnum text,
                  Arbnum.fromInt width_limit) then () else
                raise ERR "word" "word width exceeds admitted contract"
            | NONE => ()
        in () end
      else ()
    in word token end

  fun word_with_policy width_limit token =
    let
      val _ = if SmtReplayResourcePolicy.positive width_limit then () else
        raise ERR "word" "nonpositive word-width contract"
      val candidate = String.size token > 2 andalso
        String.isPrefix "bv" token andalso
        Char.isDigit (String.sub (token, 2)) andalso
        String.isSubstring "[" token
      val _ = if candidate then
        let
          val fields = String.fields (fn c => c = #"[")
            (String.extract (token, 2, NONE))
          val size = case fields of [_, suffix] =>
              (case String.fields (fn c => c = #"]") suffix of
                [size, ""] => SOME size | _ => NONE)
            | _ => NONE
          val _ = case size of SOME text =>
              if (case width_limit of
                  SmtReplayResourcePolicy.Uncapped =>
                    (ignore (Library.parse_arbnum text);true)
                | SmtReplayResourcePolicy.AtMost maximum =>
                    Arbnum.<= (Library.parse_arbnum text,
                      Arbnum.fromString (IntInf.toString maximum)))
              then () else
                raise ERR "word" "word width exceeds admitted contract"
            | NONE => ()
        in () end
      else ()
    in word token end

end
