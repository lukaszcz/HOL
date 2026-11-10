(* The checked schema is about graph names only. Its sole premise is the
   exact recorded target, which must later receive an independent witness. *)
structure CPC_GraphNativeReservation :> CPC_GraphNativeReservation =
struct
  open CPC_ProofParser SmtLib_GraphProof SmtReplaySupport SmtReplaySource
    SmtReplayRules
  structure G = SmtReplayGraph
  structure Q = SmtLib_GraphProof
  structure S = SmtReplaySource
  structure C = SmtReplaySupport
  structure Rules = SmtReplayRules
  type lease =
    {owner : unit ref,revision : int,validate : unit -> unit,
     validate_committed : unit -> unit}
  type request =
    {serial : int,step : CPC_ProofParser.graph_rule_step,target : G.node}
  datatype plan = Plan of
    {packet : CPC_ProofParser.graph_proof Q.packet,sources : S.sources,
     validate : unit -> unit,originals : G.node list,
     template_limit : int,check_type : Type.hol_type -> unit,
     lease : request -> lease}
  datatype origin = Origin of
    {serial : int,target : G.node,equation : G.node * G.node,
     certificate : C.certificate,lease : lease,active : unit -> unit}
  val ERR = Feedback.mk_HOL_ERR "CPC_GraphNativeReservation"
  fun source_nodes sources =
    S.assumption_nodes sources @ [S.denied_goal_node sources]
  fun new {packet,sources,validate,template_limit,check_type,lease} =
    let
      val graph = Q.graph packet val scope = Q.scope packet
      val _ = validate () val _ = G.validate_scope graph scope
      val originals = source_nodes sources
      val _ = List.app (fn node =>
        (G.validate_scope graph (G.node_scope graph node);
         if G.scope_visible graph scope (G.node_scope graph node) then ()
         else raise ERR "new" "original Source is outside packet scope"))
        originals
    in Plan {packet = packet,sources = sources,validate = validate,
      originals = originals,template_limit = template_limit,
      check_type = check_type,lease = lease} end
  fun reserve (Plan {packet,sources,validate,originals,template_limit,
                     check_type,lease}) {serial,step} =
    let
      val graph = Q.graph packet val scope = Q.scope packet
      fun active () =
        (validate ();G.validate_scope graph scope;
         if source_nodes sources = originals then () else
           raise ERR "reserve" "original Source inventory changed";
         List.app (fn node =>
           (G.validate_scope graph (G.node_scope graph node);
            if G.scope_visible graph scope (G.node_scope graph node) then ()
            else raise ERR "reserve" "original Source captures scope"))
           originals)
      val _ = active ()
      fun candidate () =
        if #replay_handler (#rule step) <> "trust" orelse
            not (null (#premises step)) then NONE else
        case (#args step,#conclusion step) of
          ([CPC_ProofParser.GraphTerm argument],SOME declared) =>
            if #node argument <> #node declared then
              raise ERR "reserve" "recorded TRUST endpoint changed"
            else (case Rules.equality graph (#node argument) of
              NONE => NONE
            | SOME pair =>
                let
                  val target = #node argument
                  val allocated = List.map #node (Q.variables packet)
                  fun permitted
                      ({marker,kind,source,...} :
                         SmtLib_GraphFrontend.private_binding) =
                    (marker = #1 pair orelse marker = #2 pair) andalso
                    List.exists (fn node => node = marker) allocated andalso
                    Option.isSome source andalso
                    (kind = "@fp.ZERO" orelse kind = "@fp.INF" orelse
                     kind = "@fp.NAN")
                  val supported = List.exists permitted
                    (Q.private_bindings packet)
                in if supported then SOME (target,pair) else NONE end)
        | _ => NONE
    in case candidate () of NONE => NONE | SOME (target,pair) =>
      let
        val nodes = G.block_reachable graph [target]
        val _ = List.app (fn node =>
          (G.validate_scope graph (G.node_scope graph node);
           if G.scope_visible graph scope (G.node_scope graph node) then ()
           else raise ERR "reserve" "target captures lexical scope")) nodes
        val costs = List.mapPartial (fn node => case G.view graph node of
            G.Constant _ => SOME (5 : IntInf.int)
          | G.Application _ => SOME 7 | _ => NONE) nodes
        val context = if null costs then 1 else
          List.foldl (op +) 0 costs +
          3 * IntInf.fromInt (length costs-1)
        (* P.freeze constructor context plus full named closed identity and
           its equality transport are admitted before caller type work. *)
        val required = 3 + 2 * (context + 8)
      in if required > IntInf.fromInt template_limit then NONE else
        let
          val ticket = lease {serial = serial,step = step,target = target}
          val _ = #validate ticket ()
          val certificate = C.discover graph scope
            {roots = [target],premises = [target],target = target,
             template_limit = template_limit,check_type = check_type,
             prove = fn {premise,...} => premise 0}
          val _ = if C.selected certificate = [0] then () else
            raise ERR "reserve" "temporary Hyp support changed"
          val _ = active ()
          val _ = #validate ticket ()
        in SOME (Origin {serial = serial,target = target,equation = pair,
          certificate = certificate,lease = ticket,active = active}) end
      end
    end
  fun validate_committed (Origin {lease,active,...}) =
    (active ();#validate_committed lease ())
  fun validate_request
      (Origin {serial = expected,target = recorded,lease,active,...})
      {serial,target} =
    (active ();#validate lease ();
     if serial = expected andalso target = recorded then () else
       raise ERR "validate_request" "changed native command occurrence")
  fun serial (origin as Origin {serial,...}) =
    (validate_committed origin;serial)
  fun target (origin as Origin {target,...}) =
    (validate_committed origin;target)
  fun equation (origin as Origin {equation,...}) =
    (validate_committed origin;equation)
  fun revision (origin as Origin {lease,...}) =
    (validate_committed origin;#revision lease)
  fun roots (origin as Origin {certificate,...}) =
    (validate_committed origin;C.roots certificate)
  fun assemble block (origin as Origin {certificate,target,...}) edge =
    (validate_committed origin;
     C.assemble block certificate [{index = 0,node = target,edge = edge}])
end
