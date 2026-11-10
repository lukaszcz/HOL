structure SmtReplayInstanceObservation :> SmtReplayInstanceObservation =
struct
  type statistics =
    {inst_calls:IntInf.int,inst_type_calls:IntInf.int,
     schema_raw_nodes:IntInf.int,schema_inc_nodes:IntInf.int,
     schema_annotation_nodes:IntInf.int}
  type meter =
    {inst_calls:IntInf.int ref,inst_type_calls:IntInf.int ref,
     schema_raw_nodes:IntInf.int ref,schema_inc_nodes:IntInf.int ref,
     schema_annotation_nodes:IntInf.int ref}
  val meter : meter option ref = ref NONE
  fun with_statistics action =
    let val _ = case !meter of NONE => () | SOME _ =>
          raise Feedback.mk_HOL_ERR "SmtReplayInstanceObservation"
            "with_statistics" "observation reentry"
        val fields : meter =
          {inst_calls=ref 0,inst_type_calls=ref 0,schema_raw_nodes=ref 0,
           schema_inc_nodes=ref 0,schema_annotation_nodes=ref 0}
        val _ = meter := SOME fields
        val outcome = Exn.capture action ()
        val _ = meter := NONE
        val counts : statistics =
          {inst_calls= !(#inst_calls fields),
           inst_type_calls= !(#inst_type_calls fields),
           schema_raw_nodes= !(#schema_raw_nodes fields),
           schema_inc_nodes= !(#schema_inc_nodes fields),
           schema_annotation_nodes= !(#schema_annotation_nodes fields)}
    in (Exn.release outcome,counts) end
  (* Repeated public syntax and annotation incidences, including every Hyp.
     No unfolded output residue, scalar estimate or topology coefficient. *)
  fun pointer_bucket depth modulus root =
    let
      val _ = if modulus > 0 then () else
        raise Feedback.mk_HOL_ERR "SmtReplayInstanceObservation" "pointer_bucket"
          "nonpositive bucket count"
      fun name_hash name = CharVector.foldl
        (fn (character, hash) => Word.+ (Word.* (hash, 0w33),
          Word.fromInt (Char.ord character))) 0w17 name
      fun head term =
        if Term.is_var term then name_hash (#1 (Term.dest_var term))
        else if Term.is_const term then
          Word.fromInt (KernelSig.epoch_of
            (#Name (Term.dest_thy_constid term)))
        else if Term.is_abs term then 0w19 else 0w17
      fun first_child operator operand =
        if Term.is_comb operator then #2 (Term.dest_comb operator) else operand
      fun sample 0 _ term = head term
        | sample remaining first term =
            if not (Term.is_comb term) then head term else
            let
              val (operator,operand) = Term.dest_comb term
              val child = if first then first_child operator operand
                          else operand
            in Word.+ (Word.* (head operator,0w37),
              Word.+ (Word.* (0w17,sample (remaining-1) first child),0w29))
            end
      fun samples 0 term = let val code = head term in (code,code) end
        | samples remaining term =
            if not (Term.is_comb term) then
              let val code = head term in (code,code) end
            else
              let
                val (operator,operand) = Term.dest_comb term
                val first = first_child operator operand
                val (left,right) = if Portable.pointer_eq (first,operand) then
                    samples (remaining-1) operand
                  else (sample (remaining-1) true first,
                        sample (remaining-1) false operand)
                val prefix = Word.+ (Word.* (head operator,0w37),0w29)
                fun mix code = Word.+ (prefix,Word.* (0w17,code))
              in (mix left,mix right) end
      val (left,right) = samples (Int.max (0,depth)) root
    in Word.toInt (Word.mod (Word.+ (Word.* (0w37,left),right),
      Word.fromInt modulus)) end

  fun input (fields:meter) theorem =
    let val buckets = 4093
        val hint = pointer_bucket 2 buckets
        val memo = Array.array (buckets,
          [] : (Term.term * (IntInf.int * IntInf.int * IntInf.int)) list)
        val types = ref ([] : (Type.hol_type * IntInf.int) list)
        fun type_nodes ty =
          case List.find (fn (saved,_) => Portable.pointer_eq (saved,ty))
              (!types) of SOME (_,nodes) => nodes
            | NONE =>
              let val nodes = if Type.is_vartype ty then 1 else
                    List.foldl (fn (arg,total) => type_nodes arg+total) 1
                      (#2 (Type.dest_type ty))
              in types := (ty,nodes):: !types;nodes end
        fun syntax term =
          let val key = hint term
          in case List.find (fn (saved,_) => Portable.pointer_eq (saved,term))
              (Array.sub (memo,key)) of SOME (_,profile) => profile
            | NONE =>
              let val own = type_nodes (Term.type_of term)
                  val value = if Term.is_comb term then
                    let val (a,b) = Term.dest_comb term
                        val (ar,ai,aa) = syntax a val (br,bi,ba) = syntax b
                    in (1+ar+br,1+ai+bi,own+aa+ba) end
                   else if Term.is_abs term then
                    let val (binder,body) = Term.dest_abs term
                        val (r,i,a) = syntax body
                    in (1+r,2+i,own+type_nodes (Term.type_of binder)+a) end
                   else (1,1,own)
                  val _ = Array.update (memo,key,
                    (term,value)::Array.sub (memo,key))
              in value end
          end
        fun add term =
          let val (raw,inc,annotations) = syntax term
          in #schema_raw_nodes fields := !(#schema_raw_nodes fields)+raw;
             #schema_inc_nodes fields := !(#schema_inc_nodes fields)+inc;
             #schema_annotation_nodes fields :=
               !(#schema_annotation_nodes fields)+annotations end
    in add (Thm.concl theorem);List.app add (Thm.hyp theorem) end
  fun input_profile theorem =
    let val fields : meter =
          {inst_calls=ref 0,inst_type_calls=ref 0,schema_raw_nodes=ref 0,
           schema_inc_nodes=ref 0,schema_annotation_nodes=ref 0}
        val _ = input fields theorem
    in {raw= !(#schema_raw_nodes fields),
        inc= !(#schema_inc_nodes fields),
        annotations= !(#schema_annotation_nodes fields)} end
  fun inst substitutions theorem = case !meter of
      NONE => Thm.INST substitutions theorem
    | SOME fields =>
        (#inst_calls fields := !(#inst_calls fields)+1;
         input fields theorem;Thm.INST substitutions theorem)
  fun inst_type substitutions theorem = case !meter of
      NONE => Thm.INST_TYPE substitutions theorem
    | SOME fields =>
        (#inst_type_calls fields := !(#inst_type_calls fields)+1;
         input fields theorem;Thm.INST_TYPE substitutions theorem)
  fun inst_ty_term (terms,types) theorem = inst terms (inst_type types theorem)
end
