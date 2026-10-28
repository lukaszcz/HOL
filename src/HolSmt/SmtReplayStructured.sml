(* Array/datatype procedures use the same checked variable-only operator
   schemas as arithmetic. Keep every select/store, constructor and literal;
   abstracting arbitrary compound operands would assert a stronger law. *)
structure SmtReplayStructured =
struct
  structure G = SmtReplayGraph

  (* Classification reads only the type operator, never TypeBase.fetch:
     fetching matches/instantiates the entire, not-yet-admitted annotation.
     This is dispatch metadata, not a constructor proof or type admission. *)
  fun datatype_type ty =
    if Type.is_vartype ty then false else
      let val {Thy,Tyop,...} = Type.dest_thy_type ty
      in not (List.exists (fn key => key = (Thy,Tyop))
           [("min","bool"),("num","num"),("smtfloat","smtfp"),
            ("smtfloat","smt_rounding"),("binary_ieee","float")]) andalso
         (case TypeBase.read {Thy=Thy,Tyop=Tyop} of NONE => false
          | SOME info => not (null (TypeBasePure.constructors_of info)))
      end

  fun has_operand_using owns graph scope {inputs,observe} =
    let
      val _ = G.validate_scope graph scope
      fun header node =
        (ignore (G.type_of graph node);
         if G.scope_visible graph scope (G.node_scope graph node) then ()
         else raise Feedback.mk_HOL_ERR "SmtReplayStructured" "has_operand"
           "invisible structured operand")
      val _ = List.app header inputs
      fun tick () = (G.validate_scope graph scope;observe ();
        G.validate_scope graph scope)
      fun compare pair = (tick ();Int.compare pair)
      val seen = ref (Redblackset.empty compare)
      fun visit node =
        (ignore (G.type_of graph node);tick ();
         if Redblackset.member (!seen,G.node_id node) then false else
           (seen := Redblackset.add (!seen,G.node_id node);
            case G.view graph node of
              G.Variable _ => owns node true
            | G.Constant _ => owns node false
            | G.Application (f,x) =>
                owns node false
                orelse visit f orelse visit x
            | G.AdmittedBinder _ =>
                (case G.recorded_binder_closure graph
                    (G.node_scope graph node) node of
                   SOME closure => visit (#body (G.binder_closure_data graph
                     (G.node_scope graph node) closure))
                 | NONE => true)
            | G.OpaqueRetained => true))
    in List.exists visit inputs end

  fun has_operand graph = has_operand_using (fn node => fn variable =>
    (variable andalso Lib.can Type.dom_rng (G.type_of graph node)) orelse
    (not variable andalso (case G.view graph node of G.Constant _ =>
       Term.same_const (G.representative graph node) combinSyntax.update_tm
     | _ => false)) orelse datatype_type (G.type_of graph node)) graph

  (* Native Seq is list-valued; String retains its separate carrier. Only
     inspect the outer type constructor, never instantiate a TypeBase fact. *)
  fun has_sequence_operand graph = has_operand_using
    (fn node => fn _ =>
      let val ty = G.type_of graph node
      in not (Type.is_vartype ty) andalso
         let val {Thy,Tyop,...} = Type.dest_thy_type ty
         in Thy = "list" andalso Tyop = "list" end
      end) graph
end
