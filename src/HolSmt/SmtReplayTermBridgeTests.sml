(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayTermBridgeTests =
struct
open HolKernel;
fun require message condition = if condition then () else raise Fail message;
fun ptr a b = Portable.pointer_eq (a,b);
fun check (left,right) =
  let val proof = SmtReplayTermBridge.nodewise_equality left right
      val (a,b) = boolSyntax.dest_eq (Thm.concl proof)
  in require "wrong bridge endpoint occurrence" (ptr a left andalso ptr b right);
     require "bridge acquired hypotheses" (null (Thm.hyp proof));
     Library.check_oracle_tags "Task57Bridge" "bridge" proof
  end;
fun shared 0 term = term
  | shared depth term = let val next = shared (depth-1) term
    in boolSyntax.mk_conj (next,next) end;
fun tree 0 seed = Term.mk_var ("bridge_" ^ Int.toString seed,Type.bool)
  | tree depth seed = boolSyntax.mk_conj
      (tree (depth-1) (2*seed),tree (depth-1) (2*seed+1));
fun run () =
let
val atom=Term.mk_var ("bridge_atom",Type.bool);
val app=boolSyntax.mk_neg atom;
val _=List.app check [(atom,atom),(app,boolSyntax.mk_neg atom),
  (tree 6 1,tree 6 1),(shared 80 atom,shared 80 atom)];
val x=Term.mk_var ("bridge_x",Type.bool);
val y=Term.mk_var ("bridge_y",Type.bool);
val _=check (Term.mk_abs (x,x),Term.mk_abs (y,y));
val leftty=Type.mk_type ("fun",[Type.bool,Type.bool]);
val rightty=Type.mk_type ("fun",[Type.bool,Type.bool]);
val _=check (Term.mk_var ("bridge_function",leftty),
  Term.mk_var ("bridge_function",rightty));
val _=case Exn.capture (fn () =>SmtReplayTermBridge.nodewise_equality atom
    (Term.mk_var ("bridge_other",Type.bool))) () of
    Exn.Exn (Feedback.HOL_ERR detail)=>
      require "changed bridge mismatch" (Feedback.top_structure_of detail="Thm"
        andalso Feedback.top_function_of detail="ALPHA")
  | _=>raise Fail "bridge accepted unequal leaves";
in () end;
end;
