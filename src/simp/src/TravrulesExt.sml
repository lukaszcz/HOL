(* Threaded construction uses the original structural traversal/preorder
   types, relation lookup and eager map order; no second registry or control. *)
structure TravrulesExt :> TravrulesExt =
struct
  type preorder = Travrules.preorder
  type travrules = Travrules.travrules

  fun mk_threaded_travrules relns congs =
    let
      fun threaded_cong2proc th =
        let
          val r = Opening.rel_of_congrule th
          val Travrules.PREORDER(_,_,refl) = Travrules.find_relation r relns
        in
          OpeningExt.THREADED_CONGPROC refl th
        end
    in
      Travrules.TRAVRULES {relations=relns,
                          congprocs=map threaded_cong2proc congs,
                          weakenprocs=[]}
    end
end
