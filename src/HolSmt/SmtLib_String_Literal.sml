(* Copyright (c) 2026 The HOL4 contributors. All rights reserved. *)

(* Shared SMT-LIB Unicode string-literal encoding and decoding. *)

structure SmtLib_String_Literal =
struct

  exception InvalidStringLiteral of string
  exception InvalidCodePoint of string

  val max_code_point = 196607

  fun hex_value c =
    if #"0" <= c andalso c <= #"9" then
      SOME (Char.ord c - Char.ord #"0")
    else if #"a" <= c andalso c <= #"f" then
      SOME (10 + Char.ord c - Char.ord #"a")
    else if #"A" <= c andalso c <= #"F" then
      SOME (10 + Char.ord c - Char.ord #"A")
    else
      NONE

  fun hex_string n =
    String.map Char.toLower (Int.fmt StringCvt.HEX n)

  fun escape_text text start stop =
    String.substring (text, start, stop - start)

  fun out_of_range text start stop value =
    raise InvalidStringLiteral
      ("Unicode escape '" ^ escape_text text start stop ^
       "' denotes code point 0x" ^ hex_string value ^
       ", above the SMT-LIB maximum 0x2ffff")

  fun decode_string_literal text =
  let
    val size = String.size text

    fun fixed_escape start =
      if start + 6 <= size then
        let
          fun loop offset value =
            if offset = 6 then
              SOME (value, start + 6)
            else
              case hex_value (String.sub (text, start + offset)) of
                SOME digit => loop (offset + 1) (16 * value + digit)
              | NONE => NONE
        in
          loop 2 0
        end
      else
        NONE

    fun braced_escape start =
    let
      fun loop pos digits value =
        if pos >= size then
          NONE
        else
          case String.sub (text, pos) of
            #"}" =>
              if 1 <= digits andalso digits <= 5 then
                SOME (value, pos + 1)
              else
                NONE
          | c =>
              if digits = 5 then
                NONE
              else
                case hex_value c of
                  SOME digit => loop (pos + 1) (digits + 1)
                    (16 * value + digit)
                | NONE => NONE
    in
      loop (start + 3) 0 0
    end

    fun unicode_escape start =
      if start + 2 >= size orelse
         String.sub (text, start + 1) <> #"u" then
        NONE
      else if String.sub (text, start + 2) = #"{" then
        braced_escape start
      else
        fixed_escape start

    fun loop pos code_points =
      if pos >= size then
        List.rev code_points
      else if String.sub (text, pos) <> #"\\" then
        loop (pos + 1) (Char.ord (String.sub (text, pos)) :: code_points)
      else
        case unicode_escape pos of
          NONE => loop (pos + 1) (Char.ord #"\\" :: code_points)
        | SOME (value, next) =>
            if value <= max_code_point then
              loop next (value :: code_points)
            else
              out_of_range text pos next value
  in
    loop 0 []
  end

  fun encode_code_point value =
    if value < 0 orelse max_code_point < value then
      raise InvalidCodePoint
        ("SMT-LIB string code point 0x" ^ hex_string value ^
         " is outside the permitted range 0x0..0x2ffff")
    else if 32 <= value andalso value <= 126 andalso
            value <> Char.ord #"\"" then
      String.str (Char.chr value)
    else
      "\\u{" ^ hex_string value ^ "}"

  fun encode_string_literal code_points =
    String.concat (List.map encode_code_point code_points)

end
