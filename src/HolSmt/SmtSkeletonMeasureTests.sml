(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtSkeletonMeasureTests =
struct
  open HolKernel testutils

  fun require message yes = if yes then () else raise Fail message
  fun test label action = (tprint label; action (); OK ())
  fun exact term =
    let
      val expected = SmtResource.term_measure term
      val actual = SmtSkeletonProve.term_measure term
    in require "skeleton changed the structural tree/DAG metric"
      (actual = expected); actual end

  fun shared 0 leaf = leaf
    | shared depth leaf =
        let val child = shared (depth - 1) leaf
        in boolSyntax.mk_conj (child,child) end
  fun reconstructed 0 () = Term.mk_var ("measure_p",Type.bool)
    | reconstructed depth () = boolSyntax.mk_conj
        (reconstructed (depth - 1) (),reconstructed (depth - 1) ())
  fun balanced [term] = term
    | balanced terms =
        let val half = length terms div 2
        in boolSyntax.mk_conj
          (balanced (List.take (terms,half)),
           balanced (List.drop (terms,half))) end

  fun graphs () =
    let
      val p = Term.mk_var ("measure_p",Type.bool)
      val left = shared 6 p
      val right = reconstructed 6 ()
      val _ = require "reconstructed fixture unexpectedly shares its root"
        (not (Portable.pointer_eq (left,right)))
      val expected = exact left
      val _ = require "small fixture lost its exact unfolded/DAG counts"
        (expected = {tree_nodes=253,dag_nodes=14})
      val _ = require "independent reconstruction changed semantic sharing"
        (exact right = expected)
      val _ = require "equal independent branches acquired extra DAG nodes"
        (exact (boolSyntax.mk_conj (left,right)) =
         exact (shared 7 p))
      (* Same names at different Types must remain distinct typed leaves. *)
      fun typed ty = boolSyntax.mk_eq
        (Term.mk_var ("measure_typed",ty),boolSyntax.mk_arb ty)
      val _ = exact (boolSyntax.mk_conj
        (typed Type.bool,typed (listSyntax.mk_list_type Type.bool)))
    in () end

  fun shared_type 0 = Type.bool
    | shared_type depth =
        let val child = shared_type (depth - 1) in child --> child end
  fun unfolded_type ty =
    if Type.is_vartype ty then 1 else
      List.foldl (fn (child,n) => n + unfolded_type child)
        1 (#Args (Type.dest_thy_type ty))
  fun boundary_type nodes =
    let val ty64 = listSyntax.mk_list_type (shared_type 5)
    in if nodes = 64 then ty64 else listSyntax.mk_list_type ty64 end

  fun type_boundaries () =
    List.app (fn nodes =>
      let
        val left = boundary_type nodes
        val right = boundary_type nodes
        val _ = require "leaf Type boundary fixture has the wrong size"
          (unfolded_type left = nodes andalso
           unfolded_type right = nodes andalso
           not (Portable.pointer_eq (left,right)))
        (* The guard counts unfolded Type nodes, not physical Type nodes.
           Test both leaf kinds on either side of the fast-path cutoff. *)
        fun check ty = List.app (fn leaf => require
          "annotation nodes leaked into the term metric"
          (exact leaf = {tree_nodes=1,dag_nodes=1}))
          [Term.mk_var ("measure_boundary",ty),boolSyntax.mk_arb ty]
        val _ = check left
        val _ = check right
      in () end) [64,65]

  fun fresh_annotations () =
    let
      (* Much more than the recent hint capacity, but a small term graph.
         Equal independently allocated annotations used to grow an unbounded
         pointer list. Revisit old annotations after intervening eviction. *)
      val entries = List.tabulate (256,fn i =>
        ("measure_fresh_" ^ Int.toString i,
         listSyntax.mk_list_type Type.bool))
      val types = List.map #2 entries
      fun distinct [] = true
        | distinct (ty :: rest) =
            List.all (fn other =>
              not (Portable.pointer_eq (ty,other))) rest andalso
            distinct rest
      val _ = require "fresh annotations unexpectedly share their roots"
        (distinct types)
      fun clause (name,ty) = boolSyntax.mk_eq
        (Term.mk_var (name,ty),boolSyntax.mk_arb ty)
      val first = balanced (List.map clause entries)
      val rebuilt = balanced (List.map clause entries)
      val _ = require "fresh annotations changed independently rebuilt IDs"
        (exact first = exact rebuilt)
      val _ = exact (balanced
        (List.map clause (entries @ List.rev entries)))
    in () end

  fun saturation () =
    let
      val p = Term.mk_var ("measure_saturated",Type.bool)
      val measure = exact (shared 80 p)
    in require "saturation changed the tree metric or inflated the DAG"
      (#tree_nodes measure = SmtResource.max_metric andalso
       #dag_nodes measure = 162) end

  fun diagnostic action =
    (action (); raise Fail "expected original binder-opening diagnostic")
    handle Feedback.HOL_ERR detail =>
      (Feedback.top_structure_of detail,Feedback.top_function_of detail,
       Feedback.message_of detail)

  fun binders () =
    let
      val b = Term.mk_var ("measure_bound",Type.bool)
      val p = Term.mk_var ("measure_body",Type.bool)
      val identity = Term.mk_abs (b,b)
      val _ = exact identity
      val _ = exact (Term.mk_comb (identity,b))
      (* Only ~42 physical body nodes. The raw unfolded binder exceeds its
         standing bound; no multi-million-node scan fixture is constructed.
         Lazy insertion avoids standard mk_abs expanding the shared body. *)
      val body = shared 20 p
      val binder = if Thm.kernelid = "expknl" then Term.mk_abs (b,body)
        else
          let
            val marker = Term.mk_var ("measure_insert",Type.bool)
            val template = Term.mk_abs (marker,Term.mk_abs (b,marker))
          in boolSyntax.rhs (Thm.concl
            (Thm.Beta (Thm.REFL (Term.mk_comb (template,body))))) end
      val expected = diagnostic (fn () => ignore
        (SmtResource.term_children binder))
      val standing = diagnostic (fn () =>
        SmtResource.check_term_size_for "BitVector" "binder-opening"
          (SmtResource.max_bv_replay_term_nodes + 1))
      val _ = require "binder fixture lost the standing first diagnostic"
        (expected = standing)
      val application = Term.mk_comb (binder,boolSyntax.T)
      val ty = boundary_type 65
      val prefix = boolSyntax.mk_eq
        (Term.mk_var ("measure_before_binder",ty),boolSyntax.mk_arb ty)
    in List.app (fn term => require
      "fast-path fallback changed the original mandatory binder diagnostic"
      (diagnostic (fn () => ignore (SmtSkeletonProve.term_measure term)) =
       expected))
      [binder,application,boolSyntax.mk_conj (prefix,application),
       boolSyntax.mk_conj (application,prefix)] end

  fun run () =
    (test "Skeleton metrics preserve shared and reconstructed graphs" graphs;
     test "Skeleton leaf Types retain the 64/65 unfolded boundary"
       type_boundaries;
     test "Skeleton metrics handle many fresh small annotations"
       fresh_annotations;
     test "Skeleton tree saturation preserves exact DAG counts" saturation;
     test "Skeleton fallback preserves the original binder first error"
       binders)
end
