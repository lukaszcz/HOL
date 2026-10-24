(* Checked local bridges shared by canonical discovery and assembly. *)
structure SmtReplayTermBridge =
struct
  val ERR = Feedback.mk_HOL_ERR "SmtReplayTermBridge"

  (* Keep the semantic Type order: memoized pairs, never native Type.compare or
     allocation-order IDs. Metadata is routing, not equality evidence. *)
  fun new_type_order () =
    let
      val count = 4093
      val pairs = Array.array
        (count, [] : (Type.hol_type * Type.hol_type * order) list)
      fun bucket ty = if Type.is_vartype ty then 0 else
        KernelSig.epoch_of (#Tyop (Type.dest_thy_typeid ty)) mod count
      fun arguments [] [] = EQUAL
        | arguments [] _ = LESS
        | arguments _ [] = GREATER
        | arguments (l::ls) (r::rs) =
            (case compare (l,r) of EQUAL => arguments ls rs
             | result => result)
      and compare (left,right) =
        if Portable.pointer_eq (left,right) then EQUAL
        else
          let val index = (bucket left + bucket right) mod count in
            case List.find (fn (l,r,_) =>
                Portable.pointer_eq (left,l) andalso
                Portable.pointer_eq (right,r)) (Array.sub (pairs,index)) of
              SOME (_,_,result) => result
            | NONE =>
                let
                  val result = if Type.is_vartype left then
                      if Type.is_vartype right then String.compare
                        (Type.dest_vartype left,Type.dest_vartype right)
                      else LESS
                    else if Type.is_vartype right then GREATER
                    else case KernelSig.id_compare
                        (#Tyop (Type.dest_thy_typeid left),
                         #Tyop (Type.dest_thy_typeid right)) of
                        EQUAL => arguments (#2 (Type.dest_type left))
                          (#2 (Type.dest_type right))
                      | result => result
                  val _ = Array.update (pairs,index,
                    (left,right,result) :: Array.sub (pairs,index))
                in result end
          end
    in compare end

  (* REFL only classifies the prefix up to the first Type variable. Do not
     admit the unused suffix, or optional metadata, as a new prerequisite. *)
  fun admit_type ty =
    let
      val visited = ref 0
      fun visit ty =
        (visited := !visited + 1;
         SmtResource.check_term_size_for "BitVector" "canon-type-work"
           (!visited);
         Type.is_vartype ty orelse
           List.exists visit (#Args (Type.dest_thy_typeid ty)))
    in ignore (visit ty) end

  fun checked_refl term = (admit_type (Term.type_of term); Thm.REFL term)

  (* Native binder work can inspect every annotation. Visit raw Type
     incidences directly, admitting each BEFORE inspecting it. In particular
     neither an unbounded cache probe nor a postorder sum can run ahead of
     the gate. No routing/cache overhead becomes a new refusal. *)
  fun admit_native_up_to operation maximum term =
    let
      val ceiling = SmtResource.max_bv_replay_term_nodes
      fun fail () = SmtResource.check_term_size_for "BitVector" operation
        (ceiling + 1)
      fun full ty =
        let
          val visited = ref 0
          fun visit ty =
            (SmtResource.check_term_size_for "BitVector" operation
               (!visited + 1);
             visited := !visited + 1;
             if Type.is_vartype ty then () else
               List.app visit (#Args (Type.dest_thy_typeid ty)))
        in visit ty end
      (* Counting abstractions opens their bodies. Admit the actual range's
         classification before each opening, like the native REFL gate. *)
      val _ = full (Term.type_of term)
      val _ = case SmtReplayImport.bounded_raw_size_with_type_check
          (fn ty => admit_type (#2 (Type.dom_rng ty))) maximum term of
          SOME _ => () | NONE => fail ()
      fun atoms tm =
        if Term.is_comb tm then
          (atoms (Term.rator tm);atoms (Term.rand tm))
        else if Term.is_abs tm then
          let
            val (domain,range) = Type.dom_rng (Term.type_of tm)
            (* count_body substitutes only an atomic marker of this exact
               domain Type. Unlike standard dest_abs it cannot take the
               name-clash/free_vars branch before the body's annotations
               have been admitted. Count the binder annotation explicitly;
               the marker need not occur in a vacuous abstraction. *)
            val _ = full domain
            val _ = admit_type range
          in atoms (SmtReplayImport.count_body tm) end
        else full (Term.type_of tm)
    in atoms term end

  (* Atomic occurrence transport uses the owned, checked leaf programmes.
     A bounded routing probe may choose a slower programme but never refuse
     a proof. A matching metadata key alone never produces a theorem. *)
  fun leaf_equality types left right =
    let
      val lty = Term.type_of left and rty = Term.type_of right
      val _ = admit_type lty
      val _ = admit_type rty
      val _ = if SmtReplayLeafProof.same_atom left right andalso
          types (lty,rty) = EQUAL then () else
        raise Feedback.mk_HOL_ERR "Thm" "ALPHA"
          "Terms not alpha-convertible"
      exception RoutingLimit
      val remaining = ref (IntInf.fromInt
        SmtResource.max_bv_replay_term_nodes)
      fun debit amount =
        if amount <= !remaining then remaining := !remaining - amount
        else raise RoutingLimit
      val large =
        (if Thm.kernelid = "expknl" then
           SmtReplayLeafProof.large_type debit lty
         else SmtReplayLeafProof.large_type_pair debit lty rty)
        handle RoutingLimit => true
    in
      if not large then Thm.TRANS (Thm.REFL left) (Thm.REFL right)
      else if Thm.kernelid = "expknl" andalso Term.is_var left andalso
          Portable.pointer_eq (lty,rty) then
        SmtReplayLeafProof.shared_variable left right
      else SmtReplayLeafProof.redex_equality left right
    end

  fun admit_native operation = admit_native_up_to operation
    SmtResource.max_bv_replay_term_nodes

  (* Reserve the abstraction constructor BEFORE executing ABS. *)
  fun admit_body_result term = admit_native_up_to "canon-binder-result"
    (SmtResource.max_bv_replay_term_nodes - 1) term

  fun new_term_order () =
    let
      val types = new_type_order ()
      val count = 4093
      val memo = Array.array
        (count,[] : (Term.term * Term.term * order) list)
      fun rank term = if Term.is_var term then 0
        else if Term.is_const term then 1
        else if Term.is_comb term then 2 else 3
      fun compare (left,right) =
        if Portable.pointer_eq (left,right) then EQUAL
        else
          let
            val bucket = (SmtResource.pointer_bucket count left +
              SmtResource.pointer_bucket count right) mod count
          in case List.find (fn (a,b,_) =>
              Portable.pointer_eq (a,left) andalso
              Portable.pointer_eq (b,right)) (Array.sub (memo,bucket)) of
            SOME (_,_,result) => result
          | NONE =>
              let
                val result = case Int.compare (rank left,rank right) of
                    EQUAL =>
                      if Term.is_comb left then
                        (case compare (Term.rator left,Term.rator right) of
                           EQUAL => compare (Term.rand left,Term.rand right)
                         | result => result)
                      else if Term.is_var left then
                        (case String.compare
                            (#1 (Term.dest_var left),
                             #1 (Term.dest_var right)) of
                           EQUAL => types
                             (Term.type_of left,Term.type_of right)
                         | result => result)
                      else if Term.is_const left then
                        (case KernelSig.id_compare
                            (#Name (Term.dest_thy_constid left),
                             #Name (Term.dest_thy_constid right)) of
                           EQUAL => types
                             (Term.type_of left,Term.type_of right)
                         | result => result)
                      else
                        (admit_native "canon-binder-comparison" left;
                         admit_native "canon-binder-comparison" right;
                         Term.compare (left,right))
                  | result => result
                val _ = Array.update (memo,bucket,
                  (left,right,result) :: Array.sub (memo,bucket))
              in result end
          end
    in compare end

  (* Each anchor compares just one freshly rebuilt application: its
     children already have the exact requested endpoint pointers. Never
     use ALPHA on a whole rebuilt application DAG. *)
  fun anchor_left term theorem = Thm.TRANS (checked_refl term) theorem
  fun anchor_right term theorem = Thm.TRANS theorem (checked_refl term)

  fun application_bridge original canonical left right =
    let
      val _ = admit_type (Term.type_of original)
      val _ = admit_type (Term.type_of canonical)
    in anchor_right canonical
      (anchor_left original (Thm.MK_COMB (left,right))) end

  (* Transport an independently allocated endpoint without asking ALPHA or
     TRANS to rediscover equality through its unfolded application tree.
     Pointers route the cache only; every miss has a genuine kernel proof. *)
  fun nodewise_equality left right =
    let
      val types = new_type_order ()
      val count = 4093
      val memo = Array.array
        (count,[] : (Term.term * Term.term * Thm.thm) list)
      fun visit left right =
        if Portable.pointer_eq (left,right) then checked_refl left
        else
          let val bucket = (SmtResource.pointer_bucket count left +
                SmtResource.pointer_bucket count right) mod count in
            case List.find (fn (a,b,_) =>
                Portable.pointer_eq (a,left) andalso
                Portable.pointer_eq (b,right)) (Array.sub (memo,bucket)) of
              SOME (_,_,theorem) => theorem
            | NONE =>
                let
                  val theorem =
                    if Term.is_comb left andalso Term.is_comb right then
                      if Portable.pointer_eq (Term.rator left,
                            Term.rator right) andalso
                          Portable.pointer_eq (Term.rand left,Term.rand right)
                      then Thm.TRANS (checked_refl left) (checked_refl right)
                      else application_bridge left right
                        (visit (Term.rator left) (Term.rator right))
                        (visit (Term.rand left) (Term.rand right))
                    else if Term.is_abs left andalso Term.is_abs right then
                      (admit_native "canon-binder-bridge" left;
                       admit_native "canon-binder-bridge" right;
                       Thm.TRANS (Thm.REFL left) (Thm.REFL right))
                    else if (Term.is_var left andalso Term.is_var right)
                        orelse (Term.is_const left andalso
                                Term.is_const right) then
                      leaf_equality types left right
                    else raise Feedback.mk_HOL_ERR "Thm" "ALPHA"
                      "Terms not alpha-convertible"
                  val _ = Array.update (memo,bucket,
                    (left,right,theorem) :: Array.sub (memo,bucket))
                in theorem end
          end
      val theorem = visit left right
      val (actual_left,actual_right) = boolSyntax.dest_eq (Thm.concl theorem)
      val _ = if Portable.pointer_eq (left,actual_left) andalso
          Portable.pointer_eq (right,actual_right) then () else
        raise ERR "nodewise_equality" "transport lost an endpoint occurrence"
    in theorem end

  fun exact_left term theorem =
    let val left = boolSyntax.lhs (Thm.concl theorem) in
      if Portable.pointer_eq (term,left) then theorem
      else Thm.TRANS (nodewise_equality term left) theorem
    end

  (* A tiny schema can carry enormous atomic annotations. Native term
     substitution matches each redex at each source occurrence; on the
     experimental kernel this can unfold an equal Type even on shared
     annotation roots. Admit the complete conservative portfolio first.
     Otherwise coalesce the compact schema/redex variables, then let INST
     perform its ordinary checked substitution. Sharing is not evidence. *)
  fun prepare_schema_substitution raw theorem substitution =
    let
      val maximum = SmtResource.max_bv_replay_term_nodes
      val comparisons = Int.max (1,raw) * Int.max (1,List.length substitution)
      val allowance = maximum div comparisons
      fun small_type ty =
        let
          fun visit [] n = true
            | visit ([] :: rest) n = visit rest n
            | visit ((ty :: siblings) :: rest) n =
                if n = allowance then false
                else if Type.is_vartype ty then
                  visit (siblings :: rest) (n + 1)
                else visit (#Args (Type.dest_thy_typeid ty) ::
                  siblings :: rest) (n + 1)
        in visit [[ty]] 0 end
      val hard = List.exists
        (fn {redex,residue} => not (small_type (Term.type_of redex)))
        substitution
    in
      if hard then PolyML.shareCommonData (theorem,substitution) else ()
    end
end
