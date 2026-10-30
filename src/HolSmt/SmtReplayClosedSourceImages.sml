(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayClosedSourceImages :> SmtReplayClosedSourceImages =
struct
  structure G = SmtReplayGraph
  structure R = SmtReplayResolve
  val ERR = Feedback.mk_HOL_ERR "SmtReplayClosedSourceImages"
  type admission =
    {metric : G.metric,limit : int,check_type : Type.hol_type -> unit}
  fun clean proof =
    let val (tags,_) = Tag.dest_tag (Thm.tag proof) in
      List.all (fn tag => tag = "DISK_THM") tags andalso
      List.null (Tag.axioms_of (Thm.tag proof)) end
  fun prepare graph {scope,resolution,sources,laws,
      admission = {metric,limit,check_type} : admission} =
    let
      val _ = R.validate graph scope resolution
      val _ = if limit > 0 then () else
        raise ERR "prepare" "nonpositive closed-law limit"
      val inventory = Vector.fromList sources
      val seen = ref (Redblackset.empty Int.compare)
      fun plan (index,proof) =
        let
          val _ = if index >= 0 andalso index < Vector.length inventory
            then () else raise ERR "prepare" "unknown Source occurrence"
          val _ = if Redblackset.member (!seen,index) then
              raise ERR "prepare" "duplicate Source occurrence" else ()
          val _ = seen := Redblackset.add (!seen,index)
          val original = Vector.sub (inventory,index)
          val current = R.node resolution original
          val _ = if not (R.is_assignment_source resolution original) andalso
              List.null (Thm.hyp proof) andalso clean proof andalso
              Portable.pointer_eq (Thm.concl proof,
                G.representative graph original) then () else
            raise ERR "prepare" "original law is not exact closed and clean"
          (* An unchanged exact closed Source needs no image, substitution,
             binder opening or native operand admission. R already checked
             its preservation, including any recorded opaque Source view. *)
          val variables = if original = current then [] else
            case G.free_variable_nodes graph original of
              SOME nodes => nodes
            | NONE => raise ERR "prepare" "unknown closed-law dependencies"
          fun participating node = if R.node resolution node = node then NONE
            else case G.view graph node of G.Variable (G.SolverFlexible,_) =>
                SOME (node,R.node resolution node)
              | _ => raise ERR "prepare" "changed non-solver law variable"
          val substitutions = List.mapPartial participating variables
          val roots = if original = current then [] else
            original :: current :: List.concat
              (List.map (fn (left,right) => [left,right]) substitutions)
        in (index,original,current,proof,substitutions,roots) end
      val plans = List.map plan laws
      val roots = List.concat (List.map #6 plans)
      (* Every prospective fully realized endpoint/operand is admitted before
         the first caller type policy or theorem-producing callback. *)
      val _ = List.app (fn node =>
        case G.unfolded_nodes graph metric limit node of SOME size =>
            if size <= limit then () else
              raise ERR "prepare" "closed-law operand exceeds limit"
          | NONE => raise ERR "prepare" "unknown closed-law operand size") roots
      val _ = List.app (check_type o G.type_of graph)
        (G.reachable graph roots)
      val _ = R.validate graph scope resolution
      fun execute (index,original,current,proof,substitutions,_) =
        if original = current then NONE else
          let
            val substitution = List.map (fn (variable,residue) =>
              {redex = G.representative graph variable,
               residue = G.representative graph residue}) substitutions
            val instantiated = Thm.INST substitution proof
            val _ = if List.null (Thm.hyp instantiated) andalso
                clean instantiated then () else
              raise ERR "prepare" "instantiated law acquired Hyp or tags"
            val expected = G.representative graph current
            val result = Thm.EQ_MP
              (Thm.ALPHA (Thm.concl instantiated) expected) instantiated
            val _ = if Portable.pointer_eq (Thm.concl result,expected) andalso
                List.null (Thm.hyp result) andalso clean result then () else
              raise ERR "prepare" "checked current law endpoint differs"
          in SOME (index,result) end
    in List.mapPartial execute plans end
end
