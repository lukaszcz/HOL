(* Copyright (c) 2026 The HOL4 contributors. *)
(* Optional, bounded definition projection.  This is not a resource gate:
   NONE means that the caller must use its existing single-INST path.

   The caller supplies original Sources and their exact, closed, fully
   resolved witnesses.  [free] is the exact original free-variable summary,
   in native spellings, NOT the free variables of the resolved witness.
   After prepare succeeds the protocol is:

     val bth = Thm.INST (substitutions plan) input
     val bth = List.foldl (fn (p,b) => Drule.PROVE_HYP p b)
                         bth (early_witnesses plan)
     val result = finish plan bth

   In particular, finish must not see the large early definition Hyps.
   No operation in this module instantiates the input theorem. *)
structure Z3_DefinitionProjection =
struct

  val operand_budget = 8192
  datatype plan = Plan of
    {substitution : (Term.term,Term.term) Lib.subst,
     early : Thm.thm list,
     variables : Term.term list,
     sources : Term.term list,
     conjunction : Term.term,
     projections : Thm.thm list,
     existence : Thm.thm,
     retained : Term.term list,
     conclusion : Term.term,
     operand_bound : int}

  local
    val ERR = Feedback.mk_HOL_ERR "Z3_DefinitionProjection"
    val budget = operand_budget
    exception NotApplicable

    type assignment = {redex : Term.term, residue : Term.term}
    type definition =
      {source : Term.term, proof : Thm.thm, free : Term.term list}

    datatype bound = Small of int | Over | Binder
    datatype work = TM of Term.term | TY of Type.hol_type
                  | TYS of Type.hol_type list

    (* Raw occurrences, including every atomic type annotation tree.  Do not
       use dest_term on an abstraction: on the standard kernel that would
       call dest_abs and open an as-yet unbounded body.  A type-argument list
       is also consumed incrementally, never appended or measured wholesale.
       Over only certifies an over-budget prefix; we do not inspect its tail.
       In particular no FV, type_of, term_size, or binder operation touches a
       large Source or witness conclusion. *)
    fun measure replacement term =
      let
        fun walk n [] = Small n
          | walk n (TYS [] :: rest) = walk n rest
          | walk n (TYS (ty::tys) :: rest) =
              walk n (TY ty :: TYS tys :: rest)
          | walk n work =
              if n >= budget then Over
              else
                case work of
                  TM tm :: rest =>
                    if Term.is_abs tm then Binder
                    else
                      (case Term.dest_term tm of
                         Term.VAR (_,ty) =>
                           (case replacement tm of
                              NONE => walk (n+1) (TY ty :: rest)
                            | SOME size =>
                                if size > budget - n then Over
                                else walk (n+size) rest)
                       | Term.CONST {Ty,...} =>
                           walk (n+1) (TY Ty :: rest)
                       | Term.COMB (f,x) =>
                           walk (n+1) (TM f :: TM x :: rest)
                       | Term.LAMB _ => Binder)
                | TY ty :: rest =>
                    if Type.is_vartype ty then walk (n+1) rest
                    else walk (n+1)
                      (TYS (#Args (Type.dest_thy_type ty)) :: rest)
                | _ => raise ERR "measure" "invalid work stack"
      in
        walk 0 [TM term]
      end

    fun raw term = measure (fn _ => NONE) term
    fun small (Small n) = n
      | small _ = raise NotApplicable
    fun is_small (Small _) = true
      | is_small _ = false
    fun is_over Over = true
      | is_over _ = false

    fun add (a,b) =
      if b > budget - a then raise NotApplicable else a+b
    fun sum ns = List.foldl add 0 ns
    fun times (a,b) =
      if a = 0 then 0
      else if b > budget div a then raise NotApplicable else a*b

    fun member terms term = List.exists (Term.term_eq term) terms
    fun disjoint xs ys = not (List.exists (member xs) ys)
    fun same_variables xs ys =
      List.all (member xs) ys andalso List.all (member ys) xs

    fun invariant context message = raise ERR context message
    fun require true = ()
      | require false = raise NotApplicable

    fun clean context proof =
      let val (tags,_) = Tag.dest_tag (Thm.tag proof)
      in if null (Thm.hyp proof) andalso
          null (Tag.axioms_of (Thm.tag proof)) andalso
          List.all (fn tag => tag = "DISK_THM") tags then ()
        else invariant context "definition witness is not closed and clean"
      end
    (* Both operands must have already been bounded, prospectively for the
       constructed operand.  Metadata is never evidence for this equality. *)
    fun exact context target proof =
      (clean context proof;
       if Term.term_eq target (Thm.concl proof) then proof
       else invariant context "definition witness has the wrong conclusion")

    fun conjunction [tm] = tm
      | conjunction (tm::tms) =
          boolSyntax.mk_conj (tm, conjunction tms)
      | conjunction [] = invariant "prepare" "empty definition group"
    fun conjoin [th] = th
      | conjoin (th::ths) = Thm.CONJ th (conjoin ths)
      | conjoin [] = invariant "prepare" "empty witness group"
    fun projections [_] th = [th]
      | projections (_::rest) th =
          Thm.CONJUNCT1 th :: projections rest (Thm.CONJUNCT2 th)
      | projections [] _ = invariant "prepare" "empty projection group"

    (* Finish admission stops as soon as the aggregate budget is exhausted,
       including when a misbehaving caller supplies many tiny hypotheses. *)
    fun operand_total terms =
      let
        fun total n [] = SOME n
          | total n (tm::rest) =
              (case raw tm of
                 Small size =>
                   if size <= budget - n then total (n+size) rest
                   else NONE
               | _ => NONE)
      in
        total 0 terms
      end

  in

    fun substitutions (Plan {substitution,...}) = substitution
    fun early_witnesses (Plan {early,...}) = early

    fun prepare
        {assignments : (Term.term,Term.term) Lib.subst,
         definitions : definition list,
         retained : Term.term list,
         conclusion : Term.term} =
      let
        val () = require (not (null assignments))
        val original_bounds = List.map (fn (d : definition) =>
          (d, raw (#source d))) definitions
        val () = require (List.exists (is_over o #2) original_bounds)
        val measured_definitions = List.map (fn (d,source_bound) =>
          (d,source_bound,raw (Thm.concl (#proof d)))) original_bounds

        (* Variable equality below only compares bounded atomic annotations.
           The summaries themselves are supplied by the graph importer; no
           native FV query is made on a large original or resolved term. *)
        fun admit_variable v =
          (ignore (small (raw v)); require (Term.is_var v))
        val () = List.app (fn (a : assignment) =>
          admit_variable (#redex a)) assignments
        val () = List.app (fn (d : definition) =>
          List.app admit_variable (#free d)) definitions
        val assigned = List.map #redex assignments
        fun distinct [] = ()
          | distinct (v::vs) =
              (require (not (member vs v)); distinct vs)
        val () = distinct assigned
        val images = List.map (fn (a : assignment) =>
          (a, raw (#residue a))) assignments

        (* Admit the ENTIRE retained/goal input before any native FV query.
           Their post-INST images receive a separate prospective bound below.
           Retained operands may mention early, but never delayed variables. *)
        val original_operands = retained @ [conclusion]
        val original_operand_cost =
          sum (List.map (small o raw) original_operands)
        val operand_free = List.map Term.free_vars original_operands
        fun in_operands v = List.exists (fn vs => member vs v) operand_free
        fun unsafe_definition v = List.exists
          (fn ((d : definition),sb,pb) =>
             (not (is_small sb) orelse not (is_small pb)) andalso
             member (#free d) v) measured_definitions
        val candidates = List.mapPartial
          (fn ((a : assignment),image_bound) =>
            if is_small image_bound andalso
               not (in_operands (#redex a)) andalso
               not (unsafe_definition (#redex a))
            then SOME (#redex a) else NONE) images

        (* Remove whole connected original-definition components, including
           connections through variables that were removed on an earlier
           pass.  Unassigned parameters do not connect assignment groups. *)
        fun isolate candidates =
          let
            fun external free = List.exists
              (fn v => member assigned v andalso
                       not (member candidates v)) free
            val next = List.foldl
              (fn ((d : definition),kept) =>
                if external (#free d) then
                  List.filter (fn v => not (member (#free d) v)) kept
                else kept) candidates definitions
          in
            if List.length next = List.length candidates then next
            else isolate next
          end
        val candidates = isolate candidates
        fun touches (d : definition) =
          not (disjoint candidates (#free d))
        val group = List.filter (fn (d,_,_) => touches d)
          measured_definitions
        val () = require (not (null group))
        (* Do not quantify irrelevant assignment redexes. *)
        val variables = List.filter
          (fn v => List.exists
            (fn ((d : definition),_,_) => member (#free d) v) group)
          candidates
        fun delayed (a : assignment) = member variables (#redex a)
        val delayed_images = List.filter (fn (a,_) => delayed a) images
        val delayed_substitution = List.map #1 delayed_images
        val early_images = List.filter (fn (a,_) => not (delayed a)) images
        val substitution = List.map #1 early_images
        val () = require (not (null substitution))
        val () = require (not (null delayed_substitution))

        (* A maximum replacement weight bounds EVERY partially substituted
           prefix, not just the fully resolved conjunction.  Large images of
           unused early variables are never passed to local Term.subst. *)
        fun weight images v =
          case List.find (fn ((a : assignment),_) =>
                            Term.term_eq (#redex a) v) images of
            NONE => NONE
          | SOME (_,b) => SOME
              (Int.max (small (raw v),
                        case b of Small n => n | _ => budget+1))
        val sources = List.map (fn ((d : definition),_,_) => #source d) group
        val proofs = List.map (fn ((d : definition),_,_) => #proof d) group
        val source_cost = sum (List.map
          (fn (_,sb,_) => small sb) group)
        val proof_cost = sum (List.map
          (fn (_,_,pb) => small pb) group)
        val replaced_cost = sum (List.map
          (small o measure (weight delayed_images)) sources)
        val current_operand_cost = sum (List.map
          (small o measure (weight early_images)) original_operands)
        val image_cost = sum (List.map
          (fn ((a : assignment),b) =>
            add (small (raw (#redex a)), small b)) delayed_images)

        val conj_cost = add (2, small (raw boolSyntax.conjunction))
        val imp_cost = add (2, small (raw boolSyntax.implication))
        val a_bound = add (replaced_cost,
          times (List.length sources - 1, conj_cost))
        (* ?v.B = (? : (ty->bool)->bool) (\v.B).  Charge the
           application, abstraction, binder annotation AND instantiated
           existential-constant annotation.  Bound occurrences in B retain
           their original annotations as a conservative cross-kernel bound.
           All v have already passed atomic term/type admission. *)
        fun exists_cost v =
          let val ty_cost = small (raw v) - 1
          in add (8, times (2,ty_cost)) end
        val q_bound = add (a_bound, sum (List.map exists_cost variables))
        (* Bound the operands of EACH local operation, not the sum of all
           sequential prefix templates. Two Q slots cover an EXISTS target
           and its substituted body, or a CHOOSE suffix and its assumption.
           A and the old group Hyps cover the projection's simultaneous Hyp;
           implication covers PROVE_HYP's DISCH/MP wrapper. Every prefix is
           bounded by the same maximum replacement weight above. No local
           syntax or native binder operation is built before this admission.
           This fixed optional budget is NOT a production quota. *)
        val _ = sum
          [source_cost, proof_cost, image_cost, original_operand_cost,
           current_operand_cost, times (2,a_bound),
           times (2,q_bound),imp_cost]
        val operand_bound = add (source_cost,current_operand_cost)

        val () = List.app (fn (d : definition) =>
          clean "prepare" (#proof d)) definitions
        (* These native FV checks see only admitted small operands.  Check
           the exact original summary locally as an importer invariant; it
           is still the primitive EXISTS below that proves the witness. *)
        val () = List.app (fn ((d : definition),_,_) =>
          let val actual = Term.free_vars (#source d)
          in
            if not (same_variables actual (#free d)) then
              invariant "prepare" "inexact original dependency summary"
            else if List.exists
              (fn v => member assigned v andalso not (member variables v))
              actual then
              invariant "prepare" "definition group is not isolated"
            else ()
          end) group
        val () = List.app (fn ((a : assignment),_) =>
          if disjoint variables (Term.free_vars (#residue a)) then ()
          else invariant "prepare" "witness residue contains a delayed redex")
          delayed_images

        fun current (tm,free) =
          let
            val used = List.filter
              (fn (a : assignment) => member free (#redex a)) substitution
            val result = Term.subst used tm
          in
            if disjoint variables (Term.free_vars result) then result
            else invariant "prepare"
              "resolved retained operand contains a delayed redex"
          end
        val current_operands = ListPair.map current
          (original_operands,operand_free)
        val current_retained =
          List.take (current_operands,List.length retained)
        val current_conclusion = List.last current_operands

        val a = conjunction sources
        val witnesses = ListPair.map
          (fn (source,proof) => exact "prepare"
             (Term.subst delayed_substitution source) proof) (sources,proofs)
        val resolved = exact "prepare"
          (Term.subst delayed_substitution a) (conjoin witnesses)

        (* At index i the target is ?vi..vk.A, with exactly the prefix
           v0..v(i-1) replaced by resolved residues.  Build backwards from
           the checked conjunction; EXISTS checks each actual witness. *)
        fun introduce prefix [] = resolved
          | introduce prefix ((a' : assignment)::rest) =
              let
                val body = Term.subst prefix a
                val target = List.foldr
                  (fn ((s : assignment),b) =>
                    boolSyntax.mk_exists (#redex s,b)) body (a'::rest)
                val inner = introduce (a'::prefix) rest
              in
                exact "prepare" target
                  (Thm.EXISTS (target,#residue a') inner)
              end
        val existence = introduce [] delayed_substitution
        val () =
          if disjoint variables (Term.free_vars (Thm.concl existence)) then ()
          else invariant "prepare" "existential witness leaks a delayed redex"
        val early = List.map #proof
          (List.filter (fn d => not (touches d)) definitions)
      in
        SOME (Plan
          {substitution = substitution, early = early, variables = variables,
           sources = sources, conjunction = a,
           projections = projections sources (Thm.ASSUME a),
           existence = existence, retained = current_retained,
           conclusion = current_conclusion, operand_bound = operand_bound})
      end
      handle NotApplicable => NONE

    fun finish
        (Plan {variables,sources,conjunction,projections,existence,
               retained,conclusion,operand_bound,...}) bth =
      let
        val hyps = Thm.hyp bth
        val goal = Thm.concl bth
        (* This must precede even dest_exists.  It detects a caller that has
           not removed an early large Hyp without opening that Hyp, or a
           retained/goal mismatch.  There is no proof-failure fallback. *)
        val () =
          case operand_total (goal::hyps) of
            SOME n =>
              if n <= operand_bound then ()
              else invariant "finish" "unexpected Hyp/goal operand budget"
          | NONE => invariant "finish" "unbounded or binding Hyp/goal operand"
        val () =
          if Term.term_eq goal conclusion andalso
             List.all (member (sources @ retained)) hyps then ()
          else invariant "finish" "unexpected goal or undischarged early Hyp"
        val remaining = List.filter (fn h => not (member sources h)) hyps
        val body = List.foldl (fn (p,b) => Drule.PROVE_HYP p b)
          bth projections

        (* Open only our prospectively bounded local existential templates.
           Reuse the selected original variables.  The recursive call first
           eliminates the suffix, then CHOOSE discharges its body assumption.
           At the innermost call that assumption is precisely A.  At no point
           does CHOOSE see a large early definition or a substituted input. *)
        fun eliminate [] _ _ =
              invariant "finish" "empty existential elimination"
          | eliminate (v::vs) exth bth =
              let
                val (bound,body) = boolSyntax.dest_exists (Thm.concl exth)
                val selected = Term.subst [{redex=bound,residue=v}] body
                val inner =
                  if null vs then
                    if Term.term_eq selected conjunction then bth
                    else invariant "finish" "wrong existential body"
                  else eliminate vs (Thm.ASSUME selected) bth
              in
                Thm.CHOOSE (v,exth) inner
              end
        val result = eliminate variables existence body
        val () =
          if Term.term_eq (Thm.concl result) goal andalso
             same_variables (Thm.hyp result) remaining then ()
          else invariant "finish" "projection changed the retained sequent"
      in
        result
      end

  end
end
