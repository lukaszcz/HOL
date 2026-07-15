structure clasetNet :> clasetNet =
struct

open HolKernel KernelTypes

type term = Term.term

datatype label = V | Cmb | Lam | Cnst of string * string

datatype 'a net = NODE of 'a list * (label * 'a net) list

val empty = NODE ([], [])

(* Prefixing makes free-variable labels disjoint from constant labels. *)
fun const_label tm =
  let val {Name, Thy, ...} = dest_thy_const tm
  in Cnst ("c:" ^ Name, Thy)
  end

fun fvar_label tm =
  let val (Name, _) = dest_var tm
  in Cnst ("v:" ^ Name, "")
  end

fun is_bound bvars tm = op_mem aconv tm bvars

fun stored_label patvars bvars tm =
  if is_var tm andalso
     (HOLset.member (patvars, tm) orelse is_bound bvars tm) then V
  else if is_var tm then fvar_label tm
  else if is_abs tm then Lam
  else if is_comb tm then Cmb
  else const_label tm

fun query_label bvars tm =
  if is_var tm andalso is_bound bvars tm then NONE
  else if is_var tm then SOME (fvar_label tm)
  else if is_abs tm then SOME Lam
  else if is_comb tm then SOME Cmb
  else SOME (const_label tm)

fun edge label [] = NONE
  | edge label ((label', net) :: rest) =
      if label = label' then SOME net else edge label rest

fun replace_edge label net [] = [(label, net)]
  | replace_edge label net ((entry as (label', _)) :: rest) =
      if label = label' then (label, net) :: rest
      else entry :: replace_edge label net rest

fun stored_labels patvars bvars tm =
  let val label = stored_label patvars bvars tm
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
              case edge label edges of NONE => empty | SOME node => node
            val child' = enter labels child
          in
            NODE (tips, replace_edge label child' edges)
          end
  in
    enter (stored_labels patvars [] pat) net
  end

fun skip_one (NODE (_, edges)) =
  let
    fun skip_edge (V, net) = [net]
      | skip_edge (Cnst _, net) = [net]
      | skip_edge (Lam, net) = skip_one net
      | skip_edge (Cmb, net) =
          List.concat (map skip_one (skip_one net))
  in
    List.concat (map skip_edge edges)
  end

fun follow normal_walk (tm, bvars) rest (NODE (_, edges)) =
  let
    val vbranch =
      case edge V edges of NONE => [] | SOME node => normal_walk rest node
    fun exact label more =
      case edge label edges of NONE => [] | SOME node => normal_walk more node
    val exact_branch =
      case query_label bvars tm of
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
    exact_branch @ vbranch
  end

fun match tm net =
  let
    fun walk [] (NODE (tips, _)) = tips
      | walk (task :: rest) node = follow walk task rest node
  in
    walk [(tm, [])] net
  end

fun unify {q, qvars} net =
  let
    fun walk [] (NODE (tips, _)) = tips
      | walk ((tm, bvars) :: rest) node =
          if is_var tm andalso not (is_bound bvars tm) andalso
             HOLset.member (qvars, tm) then
            List.concat (map (walk rest) (skip_one node))
          else
            follow walk (tm, bvars) rest node
  in
    walk [(q, [])] net
  end

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
