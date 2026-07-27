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

  fun invalid_utf8 pos detail =
    raise InvalidStringLiteral
      ("invalid UTF-8 at byte " ^ Int.toString pos ^ ": " ^ detail)

  fun raw_out_of_range pos value =
    raise InvalidStringLiteral
      ("UTF-8 code point at byte " ^ Int.toString pos ^ " is 0x" ^
       hex_string value ^ ", above the SMT-LIB maximum 0x2ffff")

  fun decode_string_literal text =
  let
    val size = String.size text

    fun byte pos = Char.ord (String.sub (text, pos))

    fun continuation start offset =
      let val pos = start + offset
      in
        if pos >= size then
          invalid_utf8 start "truncated multi-byte sequence"
        else
          let val value = byte pos
          in
            if 128 <= value andalso value <= 191 then value
            else invalid_utf8 pos "expected a continuation byte"
          end
      end

    fun utf8_code_point start =
      let
        val first = byte start
        fun two () =
          let val second = continuation start 1
          in (64 * (first - 192) + second - 128, start + 2) end
        fun three () =
          let
            val second = continuation start 1
            val third = continuation start 2
            val _ =
              if first = 224 andalso second < 160 then
                invalid_utf8 start "overlong three-byte sequence"
              else if first = 237 andalso 160 <= second then
                invalid_utf8 start "surrogate code point"
              else ()
          in
            (4096 * (first - 224) + 64 * (second - 128) + third - 128,
             start + 3)
          end
        fun four () =
          let
            val second = continuation start 1
            val third = continuation start 2
            val fourth = continuation start 3
            val _ =
              if first = 240 andalso second < 144 then
                invalid_utf8 start "overlong four-byte sequence"
              else if first = 244 andalso 143 < second then
                invalid_utf8 start "code point above 0x10ffff"
              else ()
          in
            (262144 * (first - 240) + 4096 * (second - 128) +
             64 * (third - 128) + fourth - 128, start + 4)
          end
      in
        if first < 128 then (first, start + 1)
        else if 194 <= first andalso first <= 223 then two ()
        else if 224 <= first andalso first <= 239 then three ()
        else if 240 <= first andalso first <= 244 then four ()
        else invalid_utf8 start "invalid leading byte"
      end

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
        let
          val (value, next) = utf8_code_point pos
        in
          if value <= max_code_point then
            loop next (value :: code_points)
          else
            raw_out_of_range pos value
        end
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

  fun is_hex_code_point value =
    (Char.ord #"0" <= value andalso value <= Char.ord #"9") orelse
    (Char.ord #"a" <= value andalso value <= Char.ord #"f") orelse
    (Char.ord #"A" <= value andalso value <= Char.ord #"F")

  fun starts_unicode_escape code_points =
    case code_points of
      u :: left :: rest =>
        u = Char.ord #"u" andalso
        if left = Char.ord #"{" then
          let
            fun braced digits [] = false
              | braced digits (value :: tail) =
                  if value = Char.ord #"}" then
                    1 <= digits
                  else
                    digits < 5 andalso is_hex_code_point value andalso
                    braced (digits + 1) tail
          in
            braced 0 rest
          end
        else
          (case rest of
             h2 :: h3 :: h4 :: _ =>
               is_hex_code_point left andalso
               is_hex_code_point h2 andalso
               is_hex_code_point h3 andalso
               is_hex_code_point h4
           | _ => false)
    | _ => false

  fun encode_string_literal code_points =
  let
    fun loop [] = []
      | loop (value :: rest) =
          (if value = Char.ord #"\\" andalso
              starts_unicode_escape rest then
             "\\u{5c}"
           else
             encode_code_point value) :: loop rest
  in
    String.concat (loop code_points)
  end

end
