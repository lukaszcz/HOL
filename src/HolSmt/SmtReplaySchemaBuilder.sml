(* Copyright (c) 2026 The HOL4 contributors. *)

structure SmtReplaySchemaBuilder :> SmtReplaySchemaBuilder =
struct
  open HolKernel

  type context = {
    application: term * term -> term,
    stats: unit -> {entries:int, retained_nodes:int}
  }

  fun build replace : context =
    let
      val buckets = 257
      val limit = SmtResource.max_skeleton_replay_dag_nodes
      val pairs = Array.array (buckets, [] : (term * term * term) list)
      val nodes = Array.array (buckets, [] : term list)
      val retained = ref 0
      val entries = ref 0
      val witness = ref (SmtSkeletonProve.cache_signature ())
      exception Decline
      fun bucket term = SmtReplayImport.pointer_bucket 2 buckets term
      fun refresh () =
        if SmtSkeletonProve.cache_signature_matches (!witness) then ()
        else
          (Array.modify (fn _ => []) pairs;
           Array.modify (fn _ => []) nodes;
           retained := 0;
           entries := 0;
           witness := SmtSkeletonProve.cache_signature ())

      (* Count every retained physical node, including unchanged children.
         Failed reservations may retain completed, checked descendants;
         they never publish a parent or exceed the same total bound. *)
      fun reserve root =
        let
          val types = Array.array (16, NONE : hol_type option)
          val next = ref 0
          fun small_type ty =
            if Array.exists (fn SOME old => Portable.pointer_eq (old, ty)
                | NONE => false) types then ()
            else
              let
                val left = ref 64
                fun walk ty =
                  if !left = 0 then raise Decline
                  else
                    (left := !left - 1;
                     if Type.is_vartype ty then ()
                     else List.app walk (#Args (Type.dest_thy_type ty)))
                val _ = walk ty
                val _ = Type.uptodate_type ty orelse raise Decline
              in
                Array.update (types, !next, SOME ty);
                next := (!next + 1) mod Array.length types
              end
          fun visit term =
            let val key = bucket term in
              if List.exists (fn old => Portable.pointer_eq (old, term))
                  (Array.sub (nodes, key)) then ()
              else
                (if !retained >= limit orelse Term.is_abs term
                   then raise Decline else ();
                 if Term.is_var term orelse Term.is_const term then
                   (small_type (Term.type_of term);
                    Term.uptodate_term term orelse raise Decline; ())
                 else if Term.is_comb term then
                   (visit (Term.rator term); visit (Term.rand term))
                 else raise Decline;
                 if !retained >= limit then raise Decline else ();
                 retained := !retained + 1;
                 Array.update (nodes, key, term :: Array.sub (nodes, key)))
            end
        in (visit root; true) handle Decline => false end

      fun application (operator, operand) =
        let
          val _ = refresh ()
          val key = (bucket operator + bucket operand) mod buckets
        in
          case List.find (fn (f, x, _) =>
              Portable.pointer_eq (f, operator) andalso
              Portable.pointer_eq (x, operand)) (Array.sub (pairs, key)) of
            SOME (_, _, result) => result
          | NONE =>
              let val result = Term.mk_comb (operator, operand)
                  val _=if replace andalso !retained>=limit then
                    (Array.modify (fn _=>[]) pairs;
                     Array.modify (fn _=>[]) nodes;
                     retained:=0;entries:=0) else ()
              in
                if !entries < limit andalso reserve result then
                  (entries := !entries + 1;
                   Array.update (pairs, key,
                     (operator, operand, result) :: Array.sub (pairs, key)))
                else ();
                result
              end
        end
    in
      {application = application,
       stats = fn () => {entries = !entries, retained_nodes = !retained}}
    end

  fun new_context () = build false
  fun new_recent_context () = build true

  fun application (context : context) = #application context
  fun stats_for_test (context : context) = #stats context ()

  (* The owning index already retains these exact physical keys. Forward
     every first visit, decline and exception; a positive hit skips only
     the deeper hash that the same index would use for its physical hit.
     The owner resets both tables together on declaration changes. *)
  fun node_ids_for_replay resolve =
    let
      val buckets = 4093
      val entries = Array.array (buckets, [] : (Term.term * int) list)
      val retained = ref 0
      fun visit source =
        let val key = SmtReplayImport.pointer_bucket 4 buckets source in
          case List.find (fn (saved, _) =>
              Portable.pointer_eq (saved, source))
              (Array.sub (entries, key)) of
            SOME (_, id) => SOME id
          | NONE =>
              case resolve source of
                NONE => NONE
              | SOME id =>
                  (if !retained >= SmtResource.max_skeleton_replay_dag_nodes
                   then () else
                     (retained := !retained + 1;
                      Array.update (entries, key,
                        (source, id) :: Array.sub (entries, key)));
                   SOME id)
        end
    in visit end

  fun node_ids_for_recent_replay resolve =
        let val count=4093
            val limit=SmtResource.max_skeleton_replay_dag_nodes
            val entries=Array.array (count,[]:(term*int) list)
            val ring=Array.array (limit,NONE:(int*term) option)
            val next=ref 0
            fun visit source =
              let val bucket=SmtReplayImport.pointer_bucket 4 count source
              in case List.find (fn (old,_)=>
                  Portable.pointer_eq (old,source)) (Array.sub (entries,bucket)) of
                  SOME (_,key)=>SOME key
                | NONE=>case resolve source of NONE=>NONE
                  | SOME key=>
                    let val _=case Array.sub (ring,!next) of NONE=>()
                          | SOME (old_bucket,old)=>Array.update
                            (entries,old_bucket,List.filter (fn (entry,_)=>
                              not (Portable.pointer_eq (entry,old)))
                              (Array.sub (entries,old_bucket)))
                        val _=Array.update (ring,!next,SOME (bucket,source))
                        val _=next:=(!next+1) mod limit
                        val _=Array.update (entries,bucket,
                          (source,key)::Array.sub (entries,bucket))
                    in SOME key end
              end
        in visit end

  (* The caller's canonical index still owns first-visit admissions. Its
     physical hits repeat no Type admission. Keep these hints local to a
     synchronous traversal, where neither the resolver nor declarations
     change. A full table forwards every uncached request unchanged. *)
  fun node_ids_for_call resolve =
    let
      val buckets = 257
      val nodes = Array.array (buckets, [] : (term * int) list)
      val retained = ref 0
      fun visit term =
        let
          val key = SmtReplayImport.pointer_bucket 2 buckets term
        in
          case List.find (fn (saved, _) => Portable.pointer_eq (saved, term))
              (Array.sub (nodes, key)) of
            SOME (_, identifier) => identifier
          | NONE =>
              let val identifier = resolve term in
                if !retained >= SmtResource.max_skeleton_replay_dag_nodes
                then ()
                else
                  (retained := !retained + 1;
                   Array.update (nodes, key,
                     (term, identifier) :: Array.sub (nodes, key)));
                identifier
              end
        end
    in visit end
end
