(* Copyright (c) 2026 The HOL4 contributors. *)

(* Coefficient routing only. No classification establishes a HOL equality;
   the caller still executes the ordinary checked cancellation laws. *)
structure WordCancelLiteral :> WordCancelLiteral =
struct
  type classification = {negative:bool,minimum:bool}
  exception Decline
  fun type_id n = #Tyop (Type.dest_thy_typeid
    (fcpSyntax.mk_int_numeric_type n))
  val one_id = type_id 1
  val even_id = type_id 2
  val odd_id = type_id 3
  fun small_type ty =
    let val remaining = ref 64
        fun visit ty = if !remaining = 0 then false else
          (remaining := !remaining - 1;
           Type.is_vartype ty orelse
             List.all visit (#Args (Type.dest_thy_typeid ty)))
    in visit ty andalso Type.uptodate_type ty end
  fun width ty =
    if Type.is_vartype ty then raise Decline else
    let val {Tyop,Args,...} = Type.dest_thy_typeid ty
        fun same held = KernelSig.id_compare (Tyop,held) = EQUAL
        fun child () = case Args of [arg] => width arg | _ => raise Decline
    in if same one_id andalso null Args then 1
       else if same even_id then
         let val n = child () in if n <= 16 then 2*n else raise Decline end
       else if same odd_id then
         let val n = child () in if n < 16 then 2*n+1 else raise Decline end
       else raise Decline
    end
  fun classify term =
    let
      val _ = if small_type (Term.type_of term) then () else raise Decline
      val dimension = case Lib.total wordsSyntax.dim_of term of
          SOME ty => ty | NONE => raise Decline
      val bits = width dimension
      val modulus = Arbnum.pow (Arbnum.two,Arbnum.fromInt bits)
      fun value 0 _ = raise Decline
        | value fuel input =
          case Lib.total wordsSyntax.dest_word_literal input of
            SOME number => Arbnum.mod (number,modulus)
          | NONE => (case Lib.total wordsSyntax.dest_word_2comp input of
              SOME operand => Arbnum.mod
                (Arbnum.- (modulus,value (fuel-1) operand),modulus)
            | NONE => (case Lib.total wordsSyntax.dest_word_sub input of
                SOME (left,right) => Arbnum.mod
                  (Arbnum.- (Arbnum.+ (modulus,value (fuel-1) left),
                    value (fuel-1) right),modulus)
              | NONE => raise Decline))
      val number = value 4 term
      val half = Arbnum.div2 modulus
    in SOME {negative=Arbnum.compare (number,half)<>LESS,
      minimum=number=half} end
    handle Decline => NONE
end
