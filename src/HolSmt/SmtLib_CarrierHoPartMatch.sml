structure SmtLib_CarrierHoPartMatch :> SmtLib_CarrierHoPartMatch =
struct
  structure S = SmtLib_GraphCarrierScratch
  structure H = SmtLib_CarrierHoMatch
  type term = S.term
  type instance = {conditions:term list,left:term,right:term}
  datatype plan = Beta of int | UnderAbs of plan | UnderLeft of plan
    | UnderRight of plan | Both of plan * plan

  (* These declaration-only operations retain Drule's exact native binder
     spelling/avoidance rules. No query body can reach this code. *)
  fun tryalpha variable input =
    let val (binder,body) = Term.dest_abs input in
      if Term.aconv variable binder then input
      else if Term.var_occurs variable body then
        tryalpha (Term.variant (Term.free_vars input) variable) input
      else Term.mk_abs (variable,
        Term.subst [{redex=binder,residue=variable}] body)
    end
  fun deep_alpha [] input = input
    | deep_alpha environment input = case Term.dest_term input of
        Term.LAMB (binder,body) =>
          (let
             val (name,ty) = Term.dest_var binder
             val ((new_name,_),rest) =
               Lib.pluck (fn (_,old) => old=name) environment
             val (binder,body) = Term.dest_abs
               (tryalpha (Term.mk_var (new_name,ty)) input)
           in Term.mk_abs (binder,deep_alpha rest body) end
           handle Feedback.HOL_ERR _ =>
             Term.mk_abs (binder,deep_alpha environment body))
      | Term.COMB (left,right) =>
          Term.mk_comb (deep_alpha environment left,
            deep_alpha environment right)
      | _ => input
  fun avoids bindings input =
    let
      fun visit input known = case Term.dest_term input of
          Term.LAMB (binder,body) =>
            let val name = #1 (Term.dest_var binder)
                val target = Lib.total (Lib.rev_assoc name) bindings
                val known = case target of NONE => known
                  | SOME target => HOLset.foldl
                      (fn (variable,known) =>
                        if #1 (Term.dest_var variable)=target then
                          HOLset.add (known,variable) else known)
                      known (Term.FVL [body] (HOLset.empty Term.compare))
            in visit body known end
        | Term.COMB (left,right) => visit left (visit right known)
        | _ => known
    in visit input (HOLset.empty Term.compare) end
  fun compile_beta variable input =
    if Term.is_abs input then
      let val (binder,body) = Term.dest_abs input in
        if Term.aconv variable binder then NONE
        else Option.map UnderAbs (compile_beta variable body)
      end
    else case boolSyntax.strip_comb input of
        (_,[]) => NONE
      | (head,args) =>
          if Term.aconv head variable then SOME (Beta (List.length args))
          else
            let val (left,right) = Term.dest_comb input
                val left = compile_beta variable left
            in case left of SOME left =>
                 (case compile_beta variable right of
                    SOME right => SOME (Both (left,right))
                  | NONE => SOME (UnderLeft left))
               | NONE => Option.map UnderRight (compile_beta variable right)
            end

  (* Native ALPHA_CONV is applied only to the captured theorem conclusion.
     Residue abstraction bodies are never inspected as native terms. *)
  fun repair_bound_abstractions mapping theorem =
    let
      fun abs_conv convert input =
        let val (binder,body) = Term.dest_abs input
        in Thm.ABS binder (convert body) end
      fun left_conv convert input =
        let val (left,right) = Term.dest_comb input
        in Thm.AP_THM (convert left) right end
      fun right_conv convert input =
        let val (left,right) = Term.dest_comb input
        in Thm.AP_TERM left (convert right) end
      fun arg_conv 0 convert = right_conv convert
        | arg_conv n convert = left_conv (arg_conv (n-1) convert)
      fun lookup variable = List.find
        (fn (saved,_) => Term.aconv variable saved)
      fun walk position binders (done,actions) input =
        case Term.dest_term input of
          Term.LAMB (binder,body) =>
            let
              val binders = (binder,position)::List.filter
                (fn (saved,_) => not (Term.aconv saved binder)) binders
              val (done,restore) =
                (HOLset.delete (done,binder),
                 fn known => HOLset.add (known,binder))
                handle HOLset.NotFound =>
                  (done,fn known => HOLset.delete (known,binder)
                    handle HOLset.NotFound => known)
              val (done,actions) = walk (position o abs_conv) binders
                (done,actions) body
            in (restore done,actions) end
        | Term.COMB _ =>
            let
              val (head,args) = boolSyntax.strip_comb input
              val state = case lookup head mapping of NONE => (done,actions)
                | SOME (_,variables) => List.foldl
                    (fn ((argument,variable),state as (done,actions)) =>
                      if HOLset.member (done,argument) then state
                      else case lookup argument binders of NONE => state
                        | SOME (_,position) =>
                            (HOLset.add (done,argument),
                             position (Drule.ALPHA_CONV variable)::actions))
                    (done,actions) (ListPair.zip (args,variables))
              fun fold (argument,(state,index)) =
                (walk (position o arg_conv index) binders state argument,
                 index+1)
            in #1 (List.foldr fold (state,0) args) end
        | _ => (done,actions)
      val (_,actions) = walk Lib.I []
        (HOLset.empty Term.compare,[]) (Thm.concl theorem)
    in Conv.CONV_RULE (Conv.EVERY_CONV actions) theorem end

  fun prepare (scratch:S.interface) {part,theorem} =
    let
      val ops = #operations scratch
      val {view,type_of,same,substitute,instantiate_type,application,
           abstraction,guard,alive,step,...} = ops
      val _ = alive ()
      fun failure message = raise H.Mismatch message
      fun mismatch primary = case primary of H.Mismatch _ => true
        | S.Mismatch _ => true | _ => (#is_mismatch ops) primary
      fun optional compute = SOME (compute ()) handle primary =>
        if mismatch primary then NONE else raise primary
      fun atom current =
        case (#atomic_term scratch) current of SOME raw => raw
        | NONE => failure "atomic declaration variable required"
      fun dest_application current = case view current of
          H.Application pair => pair | _ => failure "application required"
      fun dest_abstraction current = case view current of
          H.Abstraction pair => pair | _ => failure "abstraction required"
      fun strip_abstractions current =
        let fun walk current reversed = case view current of
                H.Abstraction (binder,body) => walk body (binder::reversed)
              | _ => (List.rev reversed,current)
        in walk current [] end
      fun member current = List.exists (fn old => same (current,old))
      fun bound_variables input =
        let val seen = ref (Redblackset.empty Int.compare)
            fun visit current known =
              let val key = (#key ops) current in
                if Redblackset.member (!seen,key) then known else
                  let val _ = seen := Redblackset.add (!seen,key)
                      val _ = step ()
                  in case view current of
                      H.Abstraction (binder,body) => visit body
                        (if member binder known then known else binder::known)
                    | H.Application (left,right) => visit left
                        (visit right known)
                    | _ => known
                  end
              end
        in visit input [] end
      fun binder_names actual native known =
        (guard actual;step ();
         case (view actual,Term.dest_term native) of
           (H.Abstraction (actual_variable,actual_body),
            Term.LAMB (native_variable,native_body)) =>
             let val actual_name = (#variable_name scratch) actual_variable
                 val native_name = #1 (Term.dest_var native_variable)
                 val pair = (actual_name,native_name)
                 val known = if actual_name=native_name orelse
                     List.exists (fn old => old=pair) known then known
                   else pair::known
             in binder_names actual_body native_body known end
         | (H.Application (al,ar),Term.COMB (nl,nr)) =>
             binder_names al nl (binder_names ar nr known)
         | _ => known)
      fun beta input =
        let val (function,argument) = dest_application input
            val (binder,body) = dest_abstraction function
        in substitute [{redex=binder,residue=argument}] body end
      fun try_beta input = case optional (fn () => beta input) of
          SOME result => result | NONE => input
      fun beta_count 1 input = try_beta input
        | beta_count count input =
            let val (left,right) = dest_application input
            in try_beta (application (beta_count (count-1) left,right)) end
      fun apply_plan plan input =
        (guard input;step ();
         case plan of Beta count => beta_count count input
         | UnderAbs plan =>
             let val (binder,body) = dest_abstraction input
             in abstraction (binder,apply_plan plan body) end
         | UnderLeft plan =>
             let val (left,right) = dest_application input
             in application (apply_plan plan left,right) end
         | UnderRight plan =>
             let val (left,right) = dest_application input
             in application (left,apply_plan plan right) end
         | Both (left_plan,right_plan) =>
             let val (left,right) = dest_application input
                 val left = apply_plan left_plan left
                 val right = apply_plan right_plan right
             in application (left,right) end)
      val specialized = Drule.SPEC_ALL theorem
      val body = Thm.concl specialized
      val pattern = part body
      val rigid_variables = HOLset.listItems
        (HOLset.intersection
          (Term.FVL [pattern] (HOLset.empty Term.compare),
           Thm.hyp_frees theorem))
      val rigid_types = HOLset.listItems (Thm.hyp_tyvars theorem)
      val flexible = List.filter
        (Lib.can Type.dom_rng o Term.type_of) (Term.free_vars body)
      val plans = List.mapPartial
        (fn variable => Option.map (fn plan => (variable,plan))
          (compile_beta variable body)) flexible
      val _ = alive ()
      fun execute target =
        let
          val _ = guard target
          val request =
            {rigid_types=rigid_types,
             rigid_variables=List.map (#of_template scratch) rigid_variables,
             pattern=(#of_template scratch) pattern,target=target}
          val {terms,types} = if List.null flexible then
              H.match_first_order ops request
            else let val {terms,types,...} = H.match ops request
                 in {terms=terms,types=types} end
          val original_terms = terms
          val bound = if List.null flexible then [] else bound_variables target
          fun hold ({redex,residue},known) =
            case view residue of H.Abstraction _ =>
              let val (variables,_) = strip_abstractions residue in
                if List.all (fn variable => member variable bound) variables
                then (atom redex,List.map atom variables)::List.filter
                  (fn (saved,_) => not (Term.aconv saved (atom redex))) known
                else known
              end
            | _ => known
          val bound_to_abs = if List.null flexible then []
            else List.foldl hold [] terms
          val typed = Thm.INST_TYPE types specialized
          val typed_body = Thm.concl typed
          val names = binder_names target (part typed_body) []
          val (prepared,terms) = if List.null names then (typed,terms) else
            let
              val renamed = HOLset.foldl
                (fn (variable,known) =>
                  {redex=variable,
                   residue=Term.genvar (Term.type_of variable)}::known)
                [] (avoids names typed_body)
              val theorem = Thm.INST renamed typed
              val terms = List.map
                (fn {redex,residue} =>
                  {redex=(#of_template scratch)
                    (Term.subst renamed (atom redex)),residue=residue}) terms
              val body = Thm.concl theorem
              val theorem = Thm.EQ_MP
                (Thm.ALPHA body (deep_alpha names body)) theorem
            in (theorem,terms) end
          val prepared = if List.null bound_to_abs then prepared
            else repair_bound_abstractions bound_to_abs prepared
          val instantiated = substitute terms
            ((#of_template scratch) (Thm.concl prepared))
          val plans = if List.null types then plans else
            List.map (fn (variable,plan) =>
              (Term.inst types variable,plan)) plans
          fun finish ({redex,residue},current) =
            case List.find (fn (variable,_) =>
                Term.aconv (atom redex) variable) plans of
              NONE => current
            | SOME (_,plan) =>
                (case optional (fn () => apply_plan plan current) of
                   NONE => current | SOME result => result)
          val result = if List.null flexible then instantiated else
            List.foldl finish instantiated original_terms
          val _ = guard target val _ = guard result val _ = alive ()
        in result end
    in execute end

  fun part_match (scratch:S.interface) theorem =
    let
      val ops = #operations scratch
      val prepared = prepare scratch
        {part=boolSyntax.lhs o #2 o boolSyntax.strip_imp,theorem=theorem}
      fun binary expected current =
        let
          val (partial,right) = case (#view ops) current of
              H.Application pair => pair
            | _ => raise H.Mismatch "binary application expected"
          val (head,left) = case (#view ops) partial of
              H.Application pair => pair
            | _ => raise H.Mismatch "binary operator expected"
          val same = case (#atomic_term scratch) head of
              SOME raw => Term.is_const raw andalso
                Term.same_const raw expected
            | NONE => false
        in if same then (left,right)
           else raise H.Mismatch "different binary operator" end
      fun conditions current reversed =
        case (SOME (binary boolSyntax.implication current)
          handle H.Mismatch _ => NONE) of
          SOME (condition,body) => conditions body (condition::reversed)
        | NONE => (List.rev reversed,current)
    in fn target =>
      let val (conditions,equation) = conditions (prepared target) []
          val (left,right) = binary boolSyntax.equality equation
      in {conditions=conditions,left=left,right=right} end
    end
end
