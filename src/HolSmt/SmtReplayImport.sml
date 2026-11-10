(* Copyright (c) 2026 The HOL4 contributors. *)

structure SmtReplayImport :> SmtReplayImport =
struct
  (* A bounded hint only. The observer pays actual public metadata
     steps; callers must still compare physical identity in every bucket.
     Binder bodies are never visited by this programme. *)
  fun pointer_bucket_observed (observe:IntInf.int -> unit) depth modulus root =
    let
      val _ = observe 1
      val _ = if modulus > 0 then () else
        raise Feedback.mk_HOL_ERR "SmtReplayImport" "pointer_bucket"
          "nonpositive bucket count"
      fun add pair = (observe 1;Word.+ pair)
      fun multiply pair = (observe 1;Word.* pair)
      fun previous value = (observe 1;value-1)
      fun name_hash name =
        let
          (* The pure fold has no callback or native mutation. Pay each
             byte's six metadata operations together, before traversing it.
             IntInf prevents machine overflow; Work admits before narrowing. *)
          val _ = observe 3
          val _ = observe (6*IntInf.fromInt (String.size name))
        in CharVector.foldl
          (fn (character, hash) => Word.+ (Word.* (hash, 0w33),
            Word.fromInt (Char.ord character))) 0w17 name end
      fun head term =
        (observe 1;if Term.is_var term then
          (observe 2;name_hash (#1 (Term.dest_var term)))
         else (observe 1;if Term.is_const term then
          (observe 4;Word.fromInt (KernelSig.epoch_of
            (#Name (Term.dest_thy_constid term))))
         else (observe 1;if Term.is_abs term then 0w19 else 0w17)))
      fun first_child operator operand =
        (observe 1;if Term.is_comb operator then
          (observe 2;#2 (Term.dest_comb operator)) else operand)
      fun sample 0 _ term = (observe 1;head term)
        | sample remaining first term =
            (observe 2;if not (Term.is_comb term) then head term else
            let
              val _ = observe 1
              val (operator,operand) = Term.dest_comb term
              val _ = observe 1
              val child = if first then first_child operator operand
                          else operand
            in add (multiply (head operator,0w37),
              add (multiply (0w17,sample (previous remaining) first child),
                0w29))
            end)
      fun samples 0 term =
            (observe 2;let val code = head term in (code,code) end)
        | samples remaining term =
            (observe 2;if not (Term.is_comb term) then
              (observe 1;let val code = head term in (code,code) end)
            else
              let
                val _ = observe 1
                val (operator,operand) = Term.dest_comb term
                val first = first_child operator operand
                val _ = observe 1
                val (left,right) = if Portable.pointer_eq (first,operand) then
                    samples (previous remaining) operand
                  else (sample (previous remaining) true first,
                        sample (previous remaining) false operand)
                val prefix = add (multiply (head operator,0w37),0w29)
                fun mix code = add (prefix,multiply (0w17,code))
              in observe 1;(mix left,mix right) end)
      val _ = observe 1
      val (left,right) = samples (Int.max (0,depth)) root
      val hash = add (multiply (0w37,left),right)
      val _ = observe 3
    in Word.toInt (Word.mod (hash,Word.fromInt modulus)) end
  (* The unmetered routing hint has the same word arithmetic and traversal,
     without constructing observer calls at every metadata instruction.
     Keep the paid programme above literal: its debits and first refusals
     are part of the resource contract. Neither route establishes equality. *)
  fun pointer_bucket depth modulus root =
    let
      val _ = if modulus > 0 then () else
        raise Feedback.mk_HOL_ERR "SmtReplayImport" "pointer_bucket"
          "nonpositive bucket count"
      fun head term =
        if Term.is_var term then
          CharVector.foldl
            (fn (character,hash) => Word.+ (Word.* (hash,0w33),
              Word.fromInt (Char.ord character))) 0w17
            (#1 (Term.dest_var term))
        else if Term.is_const term then
          Word.fromInt (KernelSig.epoch_of
            (#Name (Term.dest_thy_constid term)))
        else if Term.is_abs term then 0w19 else 0w17
      fun first_child operator operand =
        if Term.is_comb operator then #2 (Term.dest_comb operator)
        else operand
      fun sample 0 _ term = head term
        | sample remaining first term =
            if not (Term.is_comb term) then head term else
              let
                val (operator,operand) = Term.dest_comb term
                val child = if first then first_child operator operand
                            else operand
              in Word.+ (Word.* (head operator,0w37),
                   Word.+ (Word.* (0w17,sample (remaining-1) first child),
                     0w29)) end
      fun samples 0 term = let val code = head term in (code,code) end
        | samples remaining term =
            if not (Term.is_comb term) then
              let val code = head term in (code,code) end
            else
              let
                val (operator,operand) = Term.dest_comb term
                val first = first_child operator operand
                val (left,right) = if Portable.pointer_eq (first,operand)
                  then samples (remaining-1) operand
                  else (sample (remaining-1) true first,
                        sample (remaining-1) false operand)
                val prefix = Word.+ (Word.* (head operator,0w37),0w29)
                fun mix code = Word.+ (prefix,Word.* (0w17,code))
              in (mix left,mix right) end
      val (left,right) = samples (Int.max (0,depth)) root
      val hash = Word.+ (Word.* (0w37,left),right)
    in Word.toInt (Word.mod (hash,Word.fromInt modulus)) end

  (* Stock standard dest_abs rebuilds its body. Beta on an atomic argument
     exposes the same syntax lazily, including when the input is a closure.
     Experimental dest_abs already returns its body without rebuilding it.
     A marker need not be fresh: replacement preserves syntax node count. *)
  fun count_body abstraction =
    if Thm.kernelid = "expknl" then #2 (Term.dest_abs abstraction)
    else
      let
        val (domain, _) = Type.dom_rng (Term.type_of abstraction)
        val marker = Term.mk_var ("smt_replay_count", domain)
        val application = Term.mk_comb (abstraction, marker)
      in
        boolSyntax.rhs (Thm.concl (Thm.Beta (Thm.REFL application)))
      end

  (* After the caller's raw/range-Type admission, open with exactly the
     stock destructor's names, but without its possible typed free_vars
     set. Standard all_atomsl visits the stored outer binder first, even
     for a closure. A singleton forces that first insertion through our
     comparator; no body or annotation is compared by this probe. FVL
     below collects only free names. Native variant also uses only names,
     so on a clash this chooses exactly the native dest_abs variant. *)
  fun dest_abs_preserving_names term =
    if Thm.kernelid = "expknl" then Term.dest_abs term
    else
      let
        exception Binder of Term.term
        val seed = Term.mk_var ("smt_replay_binder_probe",Type.bool)
        fun capture (left,right) = raise Binder
          (if Portable.pointer_eq (left,seed) then right else left)
        val variable =
          (ignore (Term.all_atomsl [term]
             (HOLset.add (HOLset.empty capture,seed)));
           raise Fail "abstraction without binder")
          handle Binder variable => variable
        fun names (left,right) = String.compare
          (#1 (Term.dest_var left),#1 (Term.dest_var right))
        val free = Term.FVL [term] (HOLset.empty names)
        val opened = if HOLset.member (free,variable) then
            Term.rename_bvar
              (#1 (Term.dest_var (Term.variant (HOLset.listItems free)
                variable))) term
          else term
      in Term.dest_abs opened end

  (* This is deliberately an unfolded visitor. Public closure destructors
     need not preserve physical sharing, and these callers require a tree
     budget. The worklist stops before exposing an unadmitted binder body. *)
  fun bounded_size_observed_program before_open visit_seen binder_slot
      binder_seen limit root =
    if limit < 0 then NONE
    else
      let
        fun walk ([], count) = (visit_seen ();SOME count)
          | walk (term :: rest, count) =
              (visit_seen ();
               if count >= limit then NONE
              else if Term.is_comb term then
                let val _ = visit_seen ()
                    val (operator, operand) = Term.dest_comb term
                    val _ = visit_seen ()
                in walk (operator :: operand :: rest, count + 1) end
              else if Term.is_abs term then
                if binder_slot andalso limit - count < 2 then NONE
                else (visit_seen ();binder_seen ();
                  (* Standard count_body constructs REFL/Beta at the range
                     Type. The caller must admit that work, not merely the
                     function Type's short-circuit classification. *)
                  before_open term;
                  walk (count_body term :: rest,
                    count + (if binder_slot then 2 else 1)))
              else (visit_seen ();walk (rest, count + 1)))
      in walk ([root], 0) end
  fun bounded_size_program binder_slot binder_seen limit root =
    bounded_size_observed_program (fn _ => ()) (fn () => ()) binder_slot
      binder_seen limit root

  fun bounded_size binder_slot limit root =
    bounded_size_program binder_slot (fn () => ()) limit root
  val bounded_raw_size = bounded_size false
  fun bounded_raw_size_observing_binders observe =
    bounded_size_observed_program (fn _ => ()) (fn () => ()) false observe
  fun bounded_raw_size_with_type_check check_type limit root =
    bounded_size_observed_program (check_type o Term.type_of)
      (fn () => ()) false (fn () => ()) limit root
  fun bounded_raw_size_with_type_check_observed
      {check_type,observe,limit} root =
    bounded_size_observed_program (check_type o Term.type_of)
      observe false (fn () => ()) limit root
  val bounded_binder_size = bounded_size true
  fun bounded_binder_size_with_type_check_observed
      {check_type,observe,limit} root =
    bounded_size_observed_program (check_type o Term.type_of)
      observe true (fn () => ()) limit root
  datatype raw_bound = RawBound of
    {original:Term.term,raw_upper:IntInf.int,inc_upper:IntInf.int,
     epoch:int,symbols:int}
  fun bounded_raw_size_bound_program observed {limit,observe} original =
    let val epoch = Type.type_epoch ()
        val symbols = Term.term_epoch ()
        fun valid () =
          if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then
            ()
          else raise Feedback.mk_HOL_ERR "SmtReplayImport" "raw_bound"
            "Type or Term epoch changed"
        fun note () = (valid ();observe ();valid ())
        val _ = note ()
        val binders = ref 0
        fun binder_seen () =
          (note ();binders := !binders+1)
        fun visit_seen () = if observed then note () else ()
    in case bounded_size_observed_program (fn _ => ()) visit_seen false
        binder_seen limit original of
        NONE => NONE
      | SOME count =>
          let val _ = note ()
              val raw = IntInf.fromInt count
              val inclusive = raw+IntInf.fromInt (!binders)
              val _ = note ()
          in SOME (RawBound {original=original,
            raw_upper=raw,inc_upper=inclusive,
            epoch=epoch,symbols=symbols}) end
    end
  fun bounded_raw_size_with_bound request original =
    bounded_raw_size_bound_program false request original
  (* Same bounded native visitor and sealed result; additionally observes
     every actual App/leaf visit and exposed worklist operation. *)
  fun bounded_raw_size_with_bound_observed request original =
    bounded_raw_size_bound_program true request original
  fun raw_bound_data (RawBound
      {original,raw_upper,inc_upper,epoch,symbols}) expected =
    if not (Portable.pointer_eq (original,expected)) then
      raise Feedback.mk_HOL_ERR "SmtReplayImport" "raw_bound"
        "different actual native pointer"
    else if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then
      {raw_upper=raw_upper,inc_upper=inc_upper}
    else raise Feedback.mk_HOL_ERR "SmtReplayImport" "raw_bound"
      "Type or Term epoch changed"
  fun raw_bound_subterm (saved as RawBound
      {original,raw_upper,inc_upper,epoch,symbols}) {target,observe} =
    let
      val _ = ignore (raw_bound_data saved original)
      fun step () =
        (ignore (raw_bound_data saved original);observe ();
         ignore (raw_bound_data saved original))
      fun visit [] = (step ();NONE)
        | visit (current::rest) =
          (step ();
           if Portable.pointer_eq (current,target) then
             (step ();SOME (RawBound {original=target,
               raw_upper=raw_upper,inc_upper=inc_upper,
               epoch=epoch,symbols=symbols}))
           else (step ();
             if Term.is_comb current then
               let val _ = step ()
                   val (left,right) = Term.dest_comb current
                   val _ = step () val _ = step ()
               in visit (left::right::rest) end
             else visit rest))
    in visit [original] end
  fun recipe_policy_int_limit SmtReplayResourcePolicy.Uncapped = NONE
    | recipe_policy_int_limit (SmtReplayResourcePolicy.AtMost limit) =
        (SOME (IntInf.toInt limit) handle Overflow => NONE)
  (* Same unfolded public-constructor metric, with exact IntInf result.
     Keep opening lazy so a finite ceiling rejects before expanding an
     unadmitted body. Neither marker identity nor this count grants FV or
     Source authority. *)
  fun exact_size_program open_body binder_slot limit root =
    if not (SmtReplayResourcePolicy.allows limit 0) then NONE
    else
      let
        fun walk ([], count) = SOME count
          | walk (term :: rest, count : IntInf.int) =
              if not (SmtReplayResourcePolicy.allows limit (count+1)) then NONE
              else if Term.is_comb term then
                let val (operator, operand) = Term.dest_comb term in
                  walk (operator :: operand :: rest, count + 1)
                end
              else if Term.is_abs term then
                if binder_slot andalso
                    not (SmtReplayResourcePolicy.allows limit (count+2))
                then NONE
                else walk (open_body term :: rest,
                  count + (if binder_slot then 2 else 1))
              else walk (rest, count + 1)
      in walk ([root], 0) end
  val exact_size_with_policy = exact_size_program count_body
  fun size_with_policy binder_slot limit root =
    case recipe_policy_int_limit limit of
        SOME finite => Option.map IntInf.fromInt
          (bounded_size binder_slot finite root)
      | NONE => exact_size_with_policy binder_slot limit root
  (* A genuinely cold binder must retain the lazy bounded visitor.
     Standard dest_abs rebuilds even a rejected, shared body in full.
     Completed admissions can supply raw DATA through Graph's observed
     getter; a miss here still uses the original count-only programme. *)
  val raw_size_with_policy = size_with_policy false
  val binder_size_with_policy = size_with_policy true

end
