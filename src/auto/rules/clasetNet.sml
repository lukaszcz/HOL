(* =====================================================================
 * Term-indexing net for the claset.
 *
 * The [match] direction (stored pattern variables act as wildcards, the
 * query is rigid) is exactly what src/1/Ho_Net provides.  This net is a
 * separate implementation because it must ALSO support [unify], where the
 * query's own variables act as wildcards and so may match any stored
 * subterm.  That reverse direction needs [skip_one_m] to step over a whole
 * stored subterm, which relies on the uniform one-node-per-application
 * labelling below (Cmb/Lam/Cnst/Fvar/V).  Ho_Net folds the argument count
 * into
 * its labels (Cnet of ... * int), so it cannot skip a subterm without
 * knowing that arity, and extending it lives on a path shared with every
 * simpset.  Keep [match] here consistent with Ho_Net's semantics.
 *
 * Both sides are labelled eta-contracted.  Isabelle's [Pure/net.ML] states
 * the same requirement -- its operands must be beta-eta-normal -- and here
 * it is forced by the engines themselves: [blastTerm.wkNorm] contracts
 * under a binder, so an assumption [!xs. C a xs] reaches the search as
 * [$! (C a)], while the elimination that takes a universal apart is stored
 * under [!y. P y].  Labelling the stored abstraction structurally hid that
 * rule from the one formula it exists to decompose, and the unifier that
 * follows contracts both sides and would have succeeded.  Contracting at
 * each labelled node is what keeps the index's notion of a term the same
 * as theirs; Isabelle goes further and keys every abstraction as a
 * wildcard, which also covers near-eta redexes such as [%x. ?P (?f x)],
 * but resolution there is higher-order where the matcher and the unifier
 * here are first-order, so nothing but eta can bridge the two spellings.
 * ===================================================================== *)

structure clasetNet :> clasetNet =
struct

open HolKernel KernelTypes

type term = Term.term

datatype label =
    V
  | Cmb
  | Lam
  | Cnst of KernelSig.kernelname
  | Fvar of string

datatype 'a net = NODE of 'a list * (label * 'a net) list

val empty = NODE ([], [])

fun no_checkpoint () = ()

fun const_label tm =
  let val {Name, Thy, ...} = dest_thy_const tm
  in Cnst {Name = Name, Thy = Thy}
  end

fun fvar_label tm =
  let val (Name, _) = dest_var tm
  in Fvar Name
  end

fun is_bound checkpoint bvars tm =
  (checkpoint (); op_mem aconv tm bvars)

(* [\y. f y] and [f] are the same function and the engines' terms are
   carried in whichever spelling reduction left, so the index answers for
   both: a labelled node is contracted first, and the walk contracts each
   child as it reaches it. *)
fun eta_contract tm =
  if not (is_abs tm) then tm
  else
    let
      val (bvar, body) = dest_abs tm
      val body' = eta_contract body
      fun rebuild () = if aconv body' body then tm else mk_abs (bvar, body')
    in
      if is_comb body' then
        let val (rator, rand) = dest_comb body'
        in
          if aconv rand bvar andalso not (free_in bvar rator)
          then eta_contract rator
          else rebuild ()
        end
      else rebuild ()
    end

fun stored_label patvars bvars tm =
  if is_var tm andalso
     (HOLset.member (patvars, tm) orelse
      is_bound no_checkpoint bvars tm) then V
  else if is_var tm then fvar_label tm
  else if is_abs tm then Lam
  else if is_comb tm then Cmb
  else const_label tm

fun query_label checkpoint bvars tm =
  if is_var tm andalso is_bound checkpoint bvars tm then NONE
  else if is_var tm then SOME (fvar_label tm)
  else if is_abs tm then SOME Lam
  else if is_comb tm then SOME Cmb
  else SOME (const_label tm)

fun edge checkpoint label [] = NONE
  | edge checkpoint label ((label', net) :: rest) =
      (checkpoint ();
       if label = label' then SOME net else edge checkpoint label rest)

fun replace_edge label net [] = [(label, net)]
  | replace_edge label net ((entry as (label', _)) :: rest) =
      if label = label' then (label, net) :: rest
      else entry :: replace_edge label net rest

fun stored_labels patvars bvars tm0 =
  let
    val tm = eta_contract tm0
    val label = stored_label patvars bvars tm
  in
    case label of
        Lam =>
          let val (bvar, body) = dest_abs tm
          in label :: stored_labels patvars (bvar :: bvars) body
          end
      | Cmb =>
          let val (rator, rand) = dest_comb tm
          in
            label :: stored_labels patvars bvars rator @
                     stored_labels patvars bvars rand
          end
      | _ => [label]
  end

fun insert ({pat, patvars}, value) net =
  let
    fun enter [] (NODE (tips, edges)) = NODE (value :: tips, edges)
      | enter (label :: labels) (NODE (tips, edges)) =
          let
            val child =
              case edge no_checkpoint label edges of
                  NONE => empty
                | SOME node => node
            val child' = enter labels child
          in
            NODE (tips, replace_edge label child' edges)
          end
  in
    enter (stored_labels patvars [] pat) net
  end

fun append checkpoint [] right = right
  | append checkpoint (item :: items) right =
      (checkpoint (); item :: append checkpoint items right)

fun follow checkpoint normal_walk (tm, bvars) rest (NODE (_, edges)) =
  let
    val vbranch =
      case edge checkpoint V edges of
          NONE => []
        | SOME node => normal_walk rest node
    fun exact label more =
      case edge checkpoint label edges of
          NONE => []
        | SOME node => normal_walk more node
    val exact_branch =
      case query_label checkpoint bvars tm of
          NONE => []
        | SOME Lam =>
            let val (bvar, body) = dest_abs tm
            in exact Lam ((body, bvar :: bvars) :: rest)
            end
        | SOME Cmb =>
            let val (rator, rand) = dest_comb tm
            in exact Cmb ((rator, bvars) :: (rand, bvars) :: rest)
            end
        | SOME label => exact label rest
  in
    append checkpoint exact_branch vbranch
  end

fun match tm net =
  let
    fun walk [] (NODE (tips, _)) = tips
      | walk ((task, bvars) :: rest) node =
          follow no_checkpoint walk (eta_contract task, bvars) rest node
  in
    walk [(tm, [])] net
  end

fun unify_with checkpoint {q, qvars} net =
  let
    fun concat_map _ [] = []
      | concat_map f (item :: items) =
          (checkpoint ();
           append checkpoint (f item) (concat_map f items))

    fun bound _ [] = false
      | bound tm (item :: items) =
          (checkpoint ();
           aconv tm item orelse bound tm items)

    fun skip_one_m (NODE (_, edges)) =
      let
        val _ = checkpoint ()
        fun skip_edge (V, child) = [child]
          | skip_edge (Cnst _, child) = [child]
          | skip_edge (Fvar _, child) = [child]
          | skip_edge (Lam, child) = skip_one_m child
          | skip_edge (Cmb, child) =
              concat_map skip_one_m (skip_one_m child)
      in
        concat_map skip_edge edges
      end

    fun walk [] (NODE (tips, _)) = (checkpoint (); tips)
      | walk ((tm0, bvars) :: rest) node =
          let
            val _ = checkpoint ()
            val tm = eta_contract tm0
          in
            if is_var tm andalso not (bound tm bvars) andalso
               HOLset.member (qvars, tm) then
              concat_map (walk rest) (skip_one_m node)
            else
              follow checkpoint walk (tm, bvars) rest node
          end
  in
    walk [(q, [])] net
  end

fun unify query net = unify_with no_checkpoint query net
fun unifyMeasured checkpoint query net =
  unify_with checkpoint query net

fun vfilter pred net =
  let
    fun keep (NODE (tips, edges)) =
      not (List.null tips) orelse not (List.null edges)
    fun filt (NODE (tips, edges)) =
      let
        fun filt_edges [] = []
          | filt_edges ((label, node) :: rest) =
              let val node' = filt node
              in
                if keep node' then (label, node') :: filt_edges rest
                else filt_edges rest
              end
      in
        NODE (List.filter pred tips, filt_edges edges)
      end
  in
    filt net
  end

fun listItems (NODE (tips, edges)) =
  tips @ List.concat (map (listItems o #2) edges)

end
